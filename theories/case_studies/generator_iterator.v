
From stdpp Require Import base list.
From iris.proofmode Require Import base tactics.
From iris.algebra Require Import excl_auth.


(* Hazel Reasoning *)
From hazel.program_logic Require Import weakest_precondition 
                                        tactics 
                                        shallow_handler_reasoning 
                                        deep_handler_reasoning 
                                        state_reasoning.

(* Local imports *)
From affect.lib Require Import base.
From affect.lang Require Import affect.
From affect.logic Require Import sem_def.
From affect.logic Require Import sem_env.
From affect.logic Require Import sem_sig.
From affect.logic Require Import sem_row.
From affect.logic Require Import sem_judgement.
From affect.logic Require Import sem_types.
From affect.logic Require Import copyable.
From affect.logic Require Import sem_operators.
From affect.logic Require Import tactics.
From affect.logic Require Import compatibility.

(* Make all the definitions opaque so that we do not rely on their definition in the model to show that the programs are well-typed terms. *)
Opaque sem_typed sem_typed_val ty_le row_le sig_le row_type_sub row_env_sub.
Opaque sem_ty_void sem_ty_unit sem_ty_bool sem_ty_int sem_ty_string sem_ty_top sem_ty_cpy sem_env_cpy sem_ty_ref_cpy sem_ty_ref sem_ty_prod sem_ty_sum sem_ty_arr sem_ty_aarr sem_ty_uarr sem_ty_forall sem_ty_row_forall sem_ty_exists sem_ty_rec sem_ty_option sem_ty_list.
Opaque sem_sig_eff sem_sig_os.
Opaque sem_row_nil sem_row_os sem_row_tun sem_row_cons sem_row_rec.

Definition yield := (λ: "x", perform: "yield" "x")%V.
Definition generate :=
  (Λ: λ: "i", let: "cont" := ref (λ: <>, "i" <_> yield) in
      λ: <>, shandle: ("cont" <!- (λ: <>, #())) #() by
                "yield" => λ: "x" "k", "cont" <!- "k" ;; SOME "x"
               | ret    => λ: "x", NONE
             end
  )%V.

Definition generate_deep :=
  (Λ: λ: "i", let: "cont" := ref (λ: <>, NONE) in
              "cont" <!- (λ: <>, handle: "i" <_> yield by
                                   "yield" => λ: "x" "k", "cont" <!- "k" ;; SOME "x"
                                  | ret    =>  λ: "x", NONE
                                end) ;;
              λ: <>, ("cont" <!- λ: <>, NONE) #()
  )%V.

Definition iterate :=
  (λ: "g", 
    Λ: (λ: "f", 
    (rec: "go" "g" := 
        match: "g" #() with
            NONE => #()
        |  SOME "x" => "f" "x" ;; "go" "g" 
        end) "g"))%V.

Section typing.

  Context `{!heapGS Σ}.

  Definition yield_sig (τ : sem_ty Σ) : operation * sem_sig Σ := ("yield", ∀S: (_ : sem_ty Σ), τ =[OS]=> ())%S.
  Definition yield_ty τ := τ -{ (yield_sig τ · ⟨⟩) }-> ().
  Definition iter_ty τ := (∀R: θ, (τ -{ θ }-> ()) -{ θ }-∘ ())%T.
  Definition iter_ty_un τ := (∀R: θ, (τ -{ θ }-> ()) -{ θ }-> ())%T.
  Definition generator_ty τ := (() → Option τ)%T.
  
  Lemma sem_typed_generate :
    ⊢ ⊨ᵥ generate : (∀T: α, iter_ty α → generator_ty α).
  Proof.
    iIntros "". iApply sem_typed_Tclosure. iIntros (α).
    rewrite -(app_nil_r []). iApply sem_typed_ufun; solve_sidecond. simpl.
    set cont_ty := (() -{ yield_sig α · ⟨⟩ }-∘ ()). 
    iApply (sem_typed_let (Refᶜ cont_ty) _ _ _ []); simpl; solve_sidecond. 
    - iApply sem_typed_alloc_cpy.
      rewrite -(app_nil_r [("i", _)]).
      iApply sem_typed_afun; solve_sidecond. 
      iApply (sem_typed_app_os (yield_ty α) _ _ _ [("i", iter_ty α)]); solve_sidecond.
      + iApply sem_typed_sub_nil.
        iApply (sem_typed_RApp (λ ρ, ( α -{ ρ }-> ()) -{ ρ }-∘ ())); solve_sidecond.
        iApply sem_typed_var.
      + iApply sem_typed_frame. iApply sem_typed_sub_nil.
        iApply sem_typed_val. rewrite /yield /yield_ty. iApply sem_typed_closure; solve_sidecond.
        simpl. iApply (sem_typed_perform_os (TT:=[tele _]) [tele_arg ()] with "[]"). 
        iApply sem_typed_var'.
    - set Γ₁ :=[("cont", Refᶜ cont_ty)]; rewrite -(app_nil_r Γ₁). 
      iApply sem_typed_ufun; solve_sidecond. simpl.
      iApply sem_typed_contraction; first solve_copy.
      rewrite app_singletons.
      iApply (sem_typed_shandler (TT:=[tele _]) OS "yield" (tele_app (λ _, α)) (tele_app (λ _, ())) () (Option α) ⊥ _ [("cont", Refᶜ cont_ty)] [] [] [("cont", Refᶜ cont_ty)]); solve_sidecond.
      * iLeft. iPureIntro. apply _.
      * iApply row_le_refl. 
      * iApply sem_typed_app_os; [|iApply sem_typed_unit']. 
        iApply sem_typed_replace_cpy_os; first iApply sem_typed_var'.
        iApply sem_typed_frame. rewrite -(app_nil_r []).
        iApply sem_typed_sub_nil.
        iApply sem_typed_afun; solve_sidecond.
        simpl. iApply sem_typed_unit'.
      * iIntros (?). do 2 iApply sem_typed_swap_third.
        iApply sem_typed_seq.
        { iApply sem_typed_replace_cpy_os; iApply sem_typed_var. }
        iApply sem_typed_some. iApply sem_typed_var.
      * simpl. do 2 iApply sem_typed_weaken.
        iApply sem_typed_none.
  Qed.
  
  Lemma sem_typed_generate_deep :
    ⊢ ⊨ᵥ generate_deep : (∀T: α, iter_ty α → generator_ty α).
  Proof.
    iIntros "". iApply sem_typed_Tclosure. iIntros (α).
    rewrite -(app_nil_r []). iApply sem_typed_ufun; solve_sidecond. simpl.
    set cont_ty := (() ⊸ Option α). 
    iApply (sem_typed_let (Refᶜ cont_ty) _ _ _ [("i", _)]); simpl; solve_sidecond. 
    - iApply sem_typed_alloc_cpy.
      rewrite -(app_nil_l [("i", _)]).
      iApply sem_typed_afun; solve_sidecond.
      iApply sem_typed_sub_nil. iApply sem_typed_none.
    - iApply (sem_typed_seq _ _ _ _ [("cont", Refᶜ cont_ty)]).
      + iApply sem_typed_contraction; solve_copy. iApply sem_typed_frame.
        iApply sem_typed_replace_cpy_os; first iApply sem_typed_var.
        iApply sem_typed_contraction; solve_copy. iApply sem_typed_frame.
        rewrite -(app_nil_r [("cont", _); ("i", _)]).
        iApply sem_typed_afun; solve_sidecond. simpl (_ ::? _).
        iApply sem_typed_swap_second. rewrite app_singletons.
        iApply (sem_typed_handler (TT:=[tele _]) OS "yield" (tele_app (λ _, α)) (tele_app (λ _, ())) () (Option α) ⊥ _ [("i", iter_ty α)] [] [] [("cont", Refᶜ cont_ty)]); solve_sidecond.
        * iApply row_le_refl. 
        * iApply (sem_typed_app_os (yield_ty α) _ _ _ [("i", iter_ty α)]); solve_sidecond.
          ** iApply sem_typed_sub_nil.
             iApply (sem_typed_RApp (λ ρ, ( α -{ ρ }-> ()) -{ ρ }-∘ ())); solve_sidecond.
             iApply sem_typed_var.
          ** iApply sem_typed_sub_nil.
             iApply sem_typed_frame.
             iApply sem_typed_val. rewrite /yield /yield_ty. iApply sem_typed_closure; solve_sidecond.
             simpl. iApply (sem_typed_perform_os (TT:=[tele _]) [tele_arg ()] with "[]"). 
             iApply sem_typed_var'.
        * iIntros (?). do 2 iApply sem_typed_swap_third.
          iApply sem_typed_seq.
          { iApply sem_typed_replace_cpy_os; iApply sem_typed_var'. }
          iApply sem_typed_some. iApply sem_typed_var'.
        * simpl. do 2 iApply sem_typed_weaken.
          iApply sem_typed_none.
      + rewrite -(app_nil_r [("cont", _)]).
        iApply sem_typed_ufun; solve_sidecond. simpl.
        iApply sem_typed_app_os; [|iApply sem_typed_unit']. 
        iApply sem_typed_replace_cpy_os; first iApply sem_typed_var'.
        iApply sem_typed_frame. rewrite -(app_nil_r []).
        iApply sem_typed_sub_nil.
        iApply sem_typed_afun; solve_sidecond.
        simpl. iApply sem_typed_none.
  Qed.

  Lemma sem_typed_iterate τ :
    ⊢ ⊨ᵥ iterate : (generator_ty τ → iter_ty_un τ).
  Proof.
    iIntros. iApply sem_typed_closure; first done. rewrite /iter_ty /=.
    rewrite - {1}(app_nil_r [("g", _)]). 
    iApply sem_typed_RLam; solve_sidecond. iIntros (θ).
    rewrite - {1}(app_nil_r [("g", _)]). 
    iApply sem_typed_sub_nil. 
    iApply sem_typed_ufun; solve_sidecond. simpl.
    iApply sem_typed_app_nil;
      [|iApply sem_typed_swap_second; iApply sem_typed_var'].
    rewrite - {1}((app_nil_r [("f", _)])). 
    iApply sem_typed_sub_u2aarr. iApply sem_typed_sub_nil.
    iApply sem_typed_ufun; solve_sidecond. simpl.
    set Γ₂ := [("g", generator_ty τ); ("go", generator_ty τ -{ θ }-> () ); ("f", τ -{ θ }-> ())].
    iApply (sem_typed_match_option (θ)%R τ _ _ Γ₂); solve_sidecond.
    - iApply sem_typed_sub_nil.
      iApply sem_typed_app_os; solve_sidecond; last iApply sem_typed_unit'.
      iApply sem_typed_contraction; solve_sidecond. 
      iApply sem_typed_sub_u2aarr. iApply sem_typed_var'.
    - do 3 iApply sem_typed_weaken. iApply sem_typed_unit'.
    - iApply (sem_typed_seq () _ _ _ [("g", generator_ty τ); ("go", generator_ty τ -{ θ }-> ())]).
      + do 2 (iApply sem_typed_swap_second; iApply sem_typed_frame_ms; solve_sidecond).
        iApply sem_typed_app_nil.
        { iApply sem_typed_sub_u2aarr. iApply sem_typed_var'. }
        iApply sem_typed_var'.
      + iApply sem_typed_app_nil; [|iApply sem_typed_var'].
        iApply sem_typed_sub_u2aarr. iApply sem_typed_var'.
  Qed.

End typing.
