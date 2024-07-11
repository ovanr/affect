
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
From affect.logic Require Import mode.
From affect.logic Require Import sem_row.
From affect.logic Require Import sem_judgement.
From affect.logic Require Import sem_types.
From affect.logic Require Import sem_operators.
From affect.logic Require Import tactics.
From affect.logic Require Import compatibility.

(* Make all the definitions opaque so that we do not rely on their definition in the model to show that the programs are well-typed terms. *)
Opaque sem_typed sem_typed_val ty_le row_le sig_le row_type_sub row_env_sub.
Opaque sem_ty_void sem_ty_unit sem_ty_bool sem_ty_int sem_ty_string sem_ty_top sem_ty_bang sem_env_bang sem_ty_ref_cpy sem_ty_ref sem_ty_prod sem_ty_sum sem_ty_arr sem_ty_aarr sem_ty_uarr sem_ty_forall sem_ty_row_forall sem_ty_exists sem_ty_rec sem_ty_option sem_ty_list.
Opaque sem_sig_eff sem_sig_flip_bang.
Opaque sem_row_nil sem_row_flip_bang sem_row_cons sem_row_rec.

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

Definition list_iter :=
    (Λ: Λ: λ: "xs",
      (Λ: (λ: "f", 
            (rec: "go" "xs" := 
              list-match: "xs" with
                CONS "x" => "xxs" => ("f" "x" ;; "go" "xxs")
              | NIL => #()
              end) "xs"
         ))
    )%V.

Section typing.

  Context `{!heapGS Σ}.

  Definition yield_sig (τ : sem_ty Σ) : operation * sem_sig Σ := ("yield", ∀S: (_ : sem_ty Σ), τ =[OS]=> ())%S.
  Definition yield_ty τ := τ -{ ¡ (yield_sig τ · ⟨⟩) }-> ().
  Definition iter_ty τ := (∀R:[OS] θ, (τ -{ ¡ θ }-> ()) -{ ¡ θ }-∘ ())%T.
  Definition iter_ty_un τ := (∀R: θ, (τ -{ θ }-> ()) -{ θ }-> ())%T.
  Definition iter_ty_gen m τ := (∀R:[m] θ, ('!_[m] τ -{ ¡_[m] θ }-> ()) -{ ¡_[m] θ }-[m]-> ())%T.
  Definition list_iter_ty := (∀M: ν, ∀T: α, List ('!_[ν] α) → iter_ty_gen ν α).
  Definition generator_ty τ := (() → Option τ)%T.
  
  Lemma sem_typed_generate :
    ⊢ ⊨ᵥ generate : (∀T: α, iter_ty α → generator_ty α).
  Proof.
    iIntros "". iApply sem_typed_Tclosure. iIntros (α).
    rewrite -(app_nil_r []). iApply sem_typed_ufun; solve_sidecond. simpl.
    set cont_ty := (() -{ ¡ (yield_sig α · ⟨⟩) }-∘ ()). 
    iApply (sem_typed_let (Refᶜ cont_ty) _ _ _ []); simpl; solve_sidecond. 
    - iApply sem_typed_alloc_cpy.
      rewrite -(app_nil_r [("i", _)]).
      iApply sem_typed_afun; solve_sidecond. 
      iApply (sem_typed_app_os (yield_ty α) _ _ _ [("i", iter_ty α)]); solve_sidecond.
      + iApply sem_typed_sub_nil.
        iApply (sem_typed_RApp (λ ρ, ( α -{ ¡ ρ }-> ()) -{ ¡ ρ }-∘ ())); solve_sidecond.
        iApply sem_typed_var.
      + iApply sem_typed_frame. iApply sem_typed_sub_nil.
        iApply sem_typed_val. rewrite /yield /yield_ty. iApply sem_typed_closure; solve_sidecond.
        simpl. iApply sem_typed_sub_row; first iApply (row_le_mfbang_intro OS).
        iApply (sem_typed_perform_os (TT:=[tele _]) [tele_arg ()] with "[]"). 
        iApply sem_typed_var'.
    - set Γ₁ :=[("cont", Refᶜ cont_ty)]; rewrite -(app_nil_r Γ₁). 
      iApply sem_typed_ufun; solve_sidecond. simpl.
      iApply sem_typed_contraction; first solve_copy.
      rewrite app_singletons.
      iApply (sem_typed_shandler (TT:=[tele _]) OS "yield" (tele_app (λ _, α)) (tele_app (λ _, ())) () (Option α) ⊥ _ [("cont", Refᶜ cont_ty)] [] [] [("cont", Refᶜ cont_ty)]); solve_sidecond.
      * iLeft. iPureIntro. apply _.
      * iApply row_le_refl. 
      * iApply sem_typed_sub_row; first iApply (row_le_mfbang_elim OS).
        iApply sem_typed_app_os; [|iApply sem_typed_unit']. 
        iApply sem_typed_replace_cpy_os; first iApply sem_typed_var'.
        iApply sem_typed_sub_nil.
        iApply sem_typed_frame. rewrite -(app_nil_r []).
        iApply sem_typed_sub_nil.
        iApply sem_typed_afun; solve_sidecond.
        simpl. iApply sem_typed_unit'.
      * iIntros (?). do 2 iApply sem_typed_swap_third.
        rewrite -/(yield_sig α) /cont_ty.
        iApply sem_typed_sub_env; first iApply env_le_cons; first iApply env_le_refl.
        { iApply ty_le_aarr; first iApply (row_le_mfbang_intro OS); iApply ty_le_refl. }
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
          ** iApply sem_typed_sub_nil. iApply sem_typed_sub_ty.
             { iApply ty_le_aarr; first iApply (row_le_mfbang_elim OS); iApply ty_le_refl. }
             iApply (sem_typed_RApp (λ ρ, ( α -{ ¡ ρ }-> ()) -{ ¡ ρ }-∘ ())); solve_sidecond.
             iApply sem_typed_var.
          ** iApply sem_typed_sub_nil.
             iApply sem_typed_frame.
             iApply sem_typed_val. rewrite /yield /yield_ty. iApply sem_typed_closure; solve_sidecond.
             simpl. iApply sem_typed_sub_row; first iApply (row_le_mfbang_intro OS).
             iApply (sem_typed_perform_os (TT:=[tele _]) [tele_arg ()] with "[]"). 
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
    iApply sem_typed_RLam; simpl; solve_sidecond. 
    { iApply mode_env_sub_ms; solve_copy. }
    iIntros (θ).
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

  Lemma sem_typed_list_iter :
    ⊢ ⊨ᵥ list_iter : list_iter_ty.
  Proof.
    iIntros. rewrite /list_iter /list_iter_ty.
    iApply sem_typed_Mclosure. iIntros (ν).
    rewrite - {1}(app_nil_r []).
    iApply sem_typed_TLam; solve_copy. iIntros (α).
    rewrite - {1}(app_nil_r []).
    iApply sem_typed_ufun; solve_sidecond. simpl.
    rewrite - {1}(app_nil_r [("xs", _)]). 
    iApply sem_typed_sub_env; first iApply env_le_cons; first iApply env_le_refl.
    iApply ty_le_list_bang.
    rewrite - {1}(app_nil_r [("xs", _)]). 
    iApply sem_typed_RLam. 
    { iApply mode_env_sub_cons; first iApply mode_env_sub_ms; solve_copy. iApply mode_type_sub_mbang. }
    iIntros (θ).
    rewrite - {1}(app_nil_r [("xs", _)]). 
    iApply sem_typed_fun; solve_sidecond. simpl.
    { iApply mode_env_sub_cons; first iApply mode_env_sub_ms; solve_copy. iApply mode_type_sub_mbang. }
    iApply sem_typed_swap_second.
    iApply sem_typed_sub_env; first iApply env_le_cons; first iApply env_le_refl.
    { iApply ty_le_mbang_elim. }
    simpl. rewrite app_singletons.
    iApply (sem_typed_app_gen (List ('!_[ν] α)) ⟨⟩%R (¡_[ ν ] θ)%R (¡_[ ν ] θ)%R); last iApply sem_typed_var'.
    - iApply row_le_nil.
    - iApply row_type_sub_once.
    - iApply row_env_sub_copy; solve_copy.
    - iApply row_le_refl.
    - rewrite - {1}(app_nil_r [("f", _)]). 
      iApply sem_typed_sub_ty; first iApply ty_le_u2aarr.
      iApply sem_typed_ufun; solve_sidecond. simpl.
      iApply (sem_typed_match_list ('!_[ν] α) (¡_[ν] θ)%R _ _ [("go", _); ("f", _)]); solve_sidecond.
      + iApply sem_typed_var'.
      + do 2 (iApply sem_typed_weaken). iApply sem_typed_unit'.
      + iApply (sem_typed_seq () _ _ _ [("go", _); ("xxs", _)]); 
          last (iApply sem_typed_swap_second; iApply sem_typed_app_nil; [iApply sem_typed_sub_ty; first iApply ty_le_u2aarr|]; iApply sem_typed_var').
        iApply sem_typed_swap_third. iApply sem_typed_swap_second.
        iApply sem_typed_swap_fourth. 
        iApply (sem_typed_app_gen ('!_[ν] α) ⟨⟩%R _ (¡_[ν] θ)%R). 
        * iApply row_le_nil.
        * iApply row_type_sub_once.
        * iApply row_env_sub_cons; last iApply row_type_sub_copy; solve_copy.
          iApply row_env_sub_cons; last iApply row_type_sub_mfbang_mbang. iApply row_env_sub_copy; solve_copy. 
        * iApply row_le_refl.
        * iApply sem_typed_var'.
        * iApply sem_typed_swap_second. 
          iApply sem_typed_sub_env_final; last iApply sem_typed_var'. 
          iApply env_le_cons; last iApply ty_le_u2aarr.
          iApply env_le_cons; first iApply env_le_cons; first iApply env_le_refl; first iApply ty_le_list_bang.
          iApply ty_le_uarr; [iApply row_le_refl|iApply ty_le_mbang_elim|iApply ty_le_refl].
  Qed.

End typing.
