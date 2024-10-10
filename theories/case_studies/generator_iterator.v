
From stdpp Require Import base list.
From iris.proofmode Require Import base tactics.
From iris.algebra Require Import excl_auth.

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
Opaque sem_ty_bot sem_ty_unit sem_ty_bool sem_ty_int sem_ty_string sem_ty_top sem_ty_mbang env_mbang sem_ty_ref_cpy sem_ty_ref sem_ty_prod sem_ty_sum sem_ty_arr sem_ty_type_forall sem_ty_row_forall sem_ty_exists sem_ty_rec sem_ty_option.
Opaque sem_sig_eff sem_sig_flip_mbang.
Opaque sem_row_nil sem_row_flip_mbang sem_row_cons sem_row_rec.

Definition yield := (λ: "x", perform: "yield" "x")%V.
Definition generate :=
  (λ: "i", let: "cont" := ref (λ: <>, "i" yield) in
      λ: <>, shandle: ("cont" <!- (λ: <>, #())) #() by
                "yield" => λ: "x" "k", "cont" <!- "k" ;; SOME "x"
               | ret    => λ: "x", NONE
             end
  )%V.

Definition generate_deep :=
  (λ: "i", let: "cont" := ref (λ: <>, NONE) in
              "cont" <!- (λ: <>, handle: "i" yield by
                                   "yield" => λ: "x" "k", "cont" <!- "k" ;; SOME "x"
                                  | ret    =>  λ: "x", NONE
                                end) ;;
              λ: <>, ("cont" <!- λ: <>, NONE) #()
  )%V.

Definition iterate :=
  (λ: "g", 
    (λ: "f", 
    (rec: "go" "g" := 
        match: "g" #() with
            NONE => #()
        |  SOME "x" => "f" "x" ;; "go" "g" 
        end) "g"))%V.

Definition list_iter :=
    (λ: "xs",
      ((λ: "f", 
            (rec: "go" "xs" := 
              list-match: "xs" with
                CONS "x" => "xxs" => ("f" "x" ;; "go" "xxs")
              | NIL => #()
              end) "xs"
         ))
    )%V.

Definition iter2seq : val := (λ: "i",
  fold: (λ: <>,
    handle: "i" yield by
          "yield" => λ: "x" "k", InjR ("x", fold: "k")
        | ret     => λ: "x", InjL #()
    end
))%V.

Definition seq2gen : val := (λ: "s",
    let: "r" := ref "s" in
    λ: <>, match: (unfold: "r" <!- fold: (λ: <>, InjL #())) #() with  
            InjL "x" => NONE
          | InjR "x" => "r" <!- (Snd "x") ;; SOME (Fst "x")
           end
)%V.
    
Section typing.
  Context `{!heapGS Σ}.

  Definition yield_sig (τ : sem_ty Σ) : operation * sem_sig Σ := ("yield", τ =[OS]=> 𝟙)%S.
  Definition yield_ty τ := τ -{ ¡ (yield_sig τ · ⟨⟩) }-> 𝟙.
  Definition iter_ty τ := (∀ᵣ θ, (τ -{ ¡ θ }-> 𝟙) -{ ¡ θ }-∘ 𝟙)%T.
  Definition iter_ty_un τ := (∀ᵣ θ, (τ -{ θ }-> 𝟙) -{ θ }-> 𝟙)%T.
  Definition iter_ty_gen m τ := (∀ᵣ θ, (![m] τ -{ ¡[m] θ }-> 𝟙) -{ ¡[m] θ }-[m]-> 𝟙)%T.
  Definition list_iter_ty := (∀ₘ ν, ∀ₜ α, List (![ν] α) → iter_ty_gen ν α).
  Definition generator_ty τ := (𝟙 → Option τ)%T.
  Definition seq_ty τ := (μₜ α, 𝟙 ⊸ (𝟙 + (τ × α)))%T.
  
  Local Instance non_expansive_seq_ty τ : NonExpansive (λ α : sem_ty Σ, 𝟙 ⊸ 𝟙 + (τ × α)).
  Proof. intros ????. by repeat f_equiv. Qed.

  Lemma sem_typed_generate :
    ⊢ ⊨ᵥ generate : (∀ₜ α, iter_ty α → generator_ty α).
  Proof.
    iIntros. iApply sem_typed_Tclosure. iIntros (α).
    iApply sem_typed_closure; first done. simpl.
    set cont_ty := (𝟙 -{ ¡ (yield_sig α · ⟨⟩) }-∘ 𝟙). 
    smart_apply (sem_typed_let (Refᶜ cont_ty) _ _ _ []); simpl.
    - iApply sem_typed_alloc_cpy.
      rewrite -(app_nil_r [("i", _)]).
      smart_apply sem_typed_afun.
      iApply (sem_typed_app_os (yield_ty α) _ _ _ [("i", iter_ty α)]).
      + iApply sem_typed_sub_nil.
        iApply (sem_typed_RApp (λ ρ, ( α -{ ¡ ρ }-> 𝟙) -{ ¡ ρ }-∘ 𝟙)).
        iApply sem_typed_var.
      + iApply sem_typed_frame. iApply sem_typed_sub_nil.
        iApply sem_typed_val. rewrite /yield /yield_ty. iApply sem_typed_closure; first done.
        simpl. iApply sem_typed_sub_row; first iApply (row_le_mfbang_intro OS).
        iApply (sem_typed_perform_os (TT:=[tele ]) [tele_arg] with "[]"). 
        iApply sem_typed_var'.
    - set Γ₁ :=[("cont", Refᶜ cont_ty)]; rewrite -(app_nil_r Γ₁). 
      smart_apply sem_typed_ufun. simpl.
      iApply sem_typed_contraction.
      rewrite app_singletons.
      smart_apply (sem_typed_shandler (TT:=[tele ]) OS "yield" (tele_app α) (tele_app 𝟙) 𝟙 (Option α) ⊥ _ [("cont", Refᶜ cont_ty)] [] [] [("cont", Refᶜ cont_ty)]).
      * iApply row_le_refl. 
      * iApply sem_typed_sub_row; first iApply (@row_le_mfbang_elim _ (yield_sig α · ⟨⟩)%R).
        iApply sem_typed_app_os; [|iApply sem_typed_unit']. 
        iApply sem_typed_replace_cpy_os; first iApply sem_typed_var'.
        iApply sem_typed_sub_nil.
        iApply sem_typed_frame. rewrite -(app_nil_r []).
        iApply sem_typed_sub_nil.
        smart_apply sem_typed_afun.
        simpl. iApply sem_typed_unit'.
      * do 2 iApply sem_typed_swap_third.
        rewrite -/(yield_sig α) /cont_ty.
        iApply sem_typed_sub_env; first iApply env_le_cons; first iApply env_le_refl.
        { iApply ty_le_trans; first iApply ty_le_mbang_elim.
          iApply ty_le_arr; first iApply (row_le_mfbang_intro OS); iApply ty_le_refl. }
        iApply sem_typed_seq.
        { iApply sem_typed_replace_cpy_os; iApply sem_typed_var. }
        iApply sem_typed_some. iApply sem_typed_var.
      * simpl. do 2 iApply sem_typed_weaken.
        iApply sem_typed_none.
  Qed.
  
  Lemma sem_typed_generate_deep :
    ⊢ ⊨ᵥ generate_deep : (∀ₜ α, iter_ty α → generator_ty α).
  Proof.
    iIntros "". iApply sem_typed_Tclosure. iIntros (α).
    iApply sem_typed_closure; first done. simpl.
    set cont_ty := (𝟙 ⊸ Option α). 
    smart_apply (sem_typed_let (Refᶜ cont_ty) _ _ _ [("i", _)]); simpl.
    - iApply sem_typed_alloc_cpy.
      rewrite -(app_nil_l [("i", _)]).
      smart_apply sem_typed_afun.
      iApply sem_typed_sub_nil. iApply sem_typed_none.
    - iApply (sem_typed_seq _ _ _ _ [("cont", Refᶜ cont_ty)]).
      + iApply sem_typed_contraction. iApply sem_typed_frame.
        iApply sem_typed_replace_cpy_os; first iApply sem_typed_var.
        iApply sem_typed_contraction. iApply sem_typed_frame.
        rewrite -(app_nil_r [("cont", _); ("i", _)]).
        smart_apply sem_typed_afun. simpl (_ ::? _).
        iApply sem_typed_swap_second. rewrite app_singletons.
        smart_apply (sem_typed_handler (TT:=[tele]) OS "yield" (tele_app α) (tele_app 𝟙) 𝟙 (Option α) ⊥ _ [("i", iter_ty α)] [] [] [("cont", Refᶜ cont_ty)]).
        * iApply row_le_refl. 
        * iApply (sem_typed_app_os (yield_ty α) _ _ _ [("i", iter_ty α)]).
          ** iApply sem_typed_sub_nil. iApply sem_typed_sub_ty.
             { iApply ty_le_arr; first iApply (@row_le_mfbang_elim _ _); iApply ty_le_refl. }
             iApply (sem_typed_RApp (λ ρ, ( α -{ ¡ ρ }-> 𝟙) -{ ¡ ρ }-∘ 𝟙)).
             iApply sem_typed_var.
          ** iApply sem_typed_sub_nil.
             iApply sem_typed_frame.
             iApply sem_typed_val. rewrite /yield /yield_ty. iApply sem_typed_closure; first done.
             simpl. iApply sem_typed_sub_row; first iApply (row_le_mfbang_intro OS).
             iApply (sem_typed_perform_os (TT:=[tele]) [tele_arg] with "[]"). 
             iApply sem_typed_var'.
        * do 2 iApply sem_typed_swap_third.
          iApply sem_typed_seq.
          { iApply sem_typed_replace_cpy_os; iApply sem_typed_var'. }
          iApply sem_typed_some. iApply sem_typed_var'.
        * simpl. do 2 iApply sem_typed_weaken.
          iApply sem_typed_none.
      + rewrite -(app_nil_r [("cont", _)]).
        smart_apply sem_typed_ufun. simpl.
        iApply sem_typed_app_os; [|iApply sem_typed_unit']. 
        iApply sem_typed_replace_cpy_os; first iApply sem_typed_var'.
        iApply sem_typed_frame. rewrite -(app_nil_r []).
        iApply sem_typed_sub_nil.
        smart_apply sem_typed_afun.
        simpl. iApply sem_typed_none.
  Qed.

  Lemma sem_typed_iterate τ :
    ⊢ ⊨ᵥ iterate : (generator_ty τ → iter_ty_un τ).
  Proof.
    iIntros. iApply sem_typed_closure; first done. rewrite /iter_ty /=.
    rewrite - {1}(app_nil_r [("g", _)]).
    iApply sem_typed_oval.
    iApply sem_typed_RLam; simpl.
    iIntros (θ).
    rewrite - {1}(app_nil_r [("g", _)]).
    smart_apply sem_oval_typed_ufun. simpl.
    iApply sem_typed_app_nil;
      [|iApply sem_typed_swap_second; iApply sem_typed_var'].
    rewrite - {1}((app_nil_r [("f", _)])). 
    iApply sem_typed_sub_u2aarr. iApply sem_typed_sub_nil.
    smart_apply sem_typed_ufun. simpl.
    set Γ₂ := [("g", generator_ty τ); ("go", generator_ty τ -{ θ }-> 𝟙 ); ("f", τ -{ θ }-> 𝟙)].
    smart_apply (sem_typed_match_option (θ)%R τ _ _ Γ₂).
    - iApply sem_typed_sub_nil.
      iApply sem_typed_app_os; last iApply sem_typed_unit'.
      iApply sem_typed_contraction.
      iApply sem_typed_sub_u2aarr. iApply sem_typed_var'.
    - do 3 iApply sem_typed_weaken. iApply sem_typed_unit'.
    - iApply (sem_typed_seq 𝟙 _ _ _ [("g", generator_ty τ); ("go", generator_ty τ -{ θ }-> 𝟙)]).
      + do 2 (iApply sem_typed_swap_second; iApply sem_typed_frame_ms).
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
    iApply sem_typed_Tclosure. iIntros (α).
    iApply sem_typed_closure; first done. simpl.
    rewrite - {1}(app_nil_r [("xs", _)]). 
    iApply sem_typed_sub_env; first iApply env_le_cons; first iApply env_le_refl.
    iApply ty_le_mbang_intro_list. iApply ty_le_mbang_idemp.
    rewrite - {1}(app_nil_r [("xs", _)]).
    iApply sem_typed_oval.
    iApply sem_typed_RLam.
    iIntros (θ).
    rewrite - {1}(app_nil_r [("xs", _)]). 
    smart_apply sem_typed_fun. simpl.
    iApply sem_typed_swap_second.
    iApply sem_typed_sub_env; first iApply env_le_cons; first iApply env_le_refl.
    { iApply ty_le_mbang_elim. }
    simpl. rewrite app_singletons.
    iApply (sem_typed_app_gen (List (![ν] α)) ⟨⟩%R (¡[ν] θ)%R (¡[ν] θ)%R); last iApply sem_typed_var'.
    - iApply row_le_nil.
    - iApply row_le_refl.
    - rewrite - {1}(app_nil_r [("f", _)]). 
      iApply sem_typed_sub_ty; first iApply ty_le_u2aarr.
      smart_apply sem_typed_ufun. simpl.
      smart_apply (sem_typed_match_list (![ν] α) (¡[ν] θ)%R _ _ [("go", _); ("f", _)]).
      + iApply sem_typed_var'.
      + do 2 (iApply sem_typed_weaken). iApply sem_typed_unit'.
      + iApply (sem_typed_seq 𝟙 _ _ _ [("go", _); ("xxs", _)]); 
          last (iApply sem_typed_swap_second; iApply sem_typed_app_nil; [iApply sem_typed_sub_ty; first iApply ty_le_u2aarr|]; iApply sem_typed_var').
        iApply sem_typed_swap_third. iApply sem_typed_frame_ms.
        iApply sem_typed_swap_second.
        iApply sem_typed_sub_env. 
        { iApply env_le_cons; [iApply env_le_refl|].
          iApply ty_le_mbang_intro_list; iApply ty_le_mbang_idemp. }
        iApply sem_typed_sub_env_final. 
        { iApply env_le_cons; [iApply env_le_refl|]. iApply (ty_le_mbang_elim ν). }
        iApply (sem_typed_app_gen (![ν] α) ⟨⟩%R _ (¡[ν] θ)%R). 
        * iApply row_le_nil.
        * iApply row_le_refl.
        * iApply sem_typed_var'.
        * iApply sem_typed_swap_third. iApply sem_typed_swap_third. 
          iApply sem_typed_sub_env_final; last iApply sem_typed_var'. 
          iApply env_le_cons; last iApply ty_le_u2aarr. iApply env_le_refl.
  Qed.

  Lemma sem_typed_iter2seq :
    ⊢ ⊨ᵥ iter2seq : (∀ₜ α, iter_ty α → seq_ty α).
  Proof.
    iIntros. iApply sem_typed_Tclosure. iIntros (α).
    iApply sem_typed_closure; first done. simpl.
    iApply sem_typed_fold. rewrite -/(seq_ty α).
    rewrite -(app_nil_r [("i", _)]).
    smart_apply sem_typed_afun. simpl.
    smart_apply (sem_typed_handler (TT:=[tele]) OS "yield" (tele_app α) (tele_app 𝟙) 𝟙 _ ⊥ _ [("i", iter_ty α)] [] [] []).
    - iApply row_le_nil.
    - iApply (sem_typed_app_os (yield_ty α) _ _ _ [("i", iter_ty α)]).
      + iApply sem_typed_sub_nil. iApply sem_typed_sub_ty.
        { iApply ty_le_arr; first iApply (@row_le_mfbang_elim _ _); iApply ty_le_refl. }
        iApply (sem_typed_RApp (λ ρ, ( α -{ ¡ ρ }-> 𝟙) -{ ¡ ρ }-∘ 𝟙)).
        iApply sem_typed_var.
      + iApply sem_typed_sub_nil.
         iApply sem_typed_frame.
         iApply sem_typed_val. rewrite /yield /yield_ty. iApply sem_typed_closure; first done.
         simpl. iApply sem_typed_sub_row; first iApply (row_le_mfbang_intro OS).
         iApply (sem_typed_perform_os (TT:=[tele]) [tele_arg] with "[]"). 
         iApply sem_typed_var'.
    - iApply sem_typed_right_inj.
      iApply sem_typed_pair; first iApply sem_typed_var.
      iApply sem_typed_swap_second. iApply sem_typed_fold. iApply sem_typed_var.
    - simpl. iApply sem_typed_left_inj. iApply sem_typed_weaken. iApply sem_typed_unit.
  Qed.

  Lemma sem_typed_seq2gen :
    ⊢ ⊨ᵥ seq2gen : (∀ₜ α, seq_ty α → generator_ty α).
  Proof.
    iIntros. iApply sem_typed_Tclosure. iIntros (α).
    iApply sem_typed_closure; first done. simpl.
    smart_apply (sem_typed_let (Refᶜ (seq_ty α)) _ _ _ []); simpl.
    - iApply sem_typed_alloc_cpy. iApply sem_typed_var.
    - rewrite -(app_nil_r [("r", _)]).
      smart_apply sem_typed_ufun. simpl.
      smart_apply (sem_typed_match 𝟙 _ (α × seq_ty α) _ [("r", Refᶜ seq_ty α)] [("r", Refᶜ seq_ty α)]).
      + iApply sem_typed_contraction. iApply sem_typed_frame.
        iApply sem_typed_app_nil; last iApply sem_typed_unit'.
        set C := (λ r, 𝟙 ⊸ 𝟙 + (α × r)). rewrite -/(C (seq_ty α)).
        iApply sem_typed_unfold.
        iApply sem_typed_replace_cpy_os; first iApply sem_typed_var.
        iApply sem_typed_fold. rewrite -/(seq_ty α) -(app_nil_l [("r", Refᶜ seq_ty α)]).
        smart_apply sem_typed_afun. simpl.
        iApply sem_typed_left_inj. iApply sem_typed_unit.
      + simpl. do 2 iApply sem_typed_weaken. iApply sem_typed_none.
      + simpl. iApply (sem_typed_seq _ _ _ _ [("x", α × ⊤)]).
        * iApply sem_typed_replace_cpy_os; first (iApply sem_typed_swap_second; iApply sem_typed_var).
          iApply sem_typed_snd.
        * iApply sem_typed_some. iApply sem_typed_sub_env_final; first iApply env_le_weaken.
          iApply sem_typed_fst.
    Qed.

End typing.
