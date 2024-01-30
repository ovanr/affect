
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
From haffel.lib Require Import base.
From haffel.lang Require Import haffel.
From haffel.logic Require Import sem_def.
From haffel.logic Require Import sem_env.
From haffel.logic Require Import sem_sig.
From haffel.logic Require Import sem_row.
From haffel.logic Require Import sem_judgement.
From haffel.logic Require Import sem_types.
From haffel.logic Require Import copyable.
From haffel.logic Require Import sem_operators.
From haffel.logic Require Import tactics.
From haffel.logic Require Import compatibility.

Definition yield := (λ: "x", perform: (effect "yield", "x"))%V.
Definition generate :=
  (Λ: λ: "i", let: "cont" := ref (λ: <>, "i" <_> yield) in
      λ: <>, let: "comp" := "cont" <!- (λ: <>, #())  in
              shallow-try-ls: "comp" #() handle "yield" with
                effect λ: "x" "k", "cont" <- "k" ;; SOME "x"
             |  return λ: "x", NONE
             end
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

  Definition yield_sig (τ : sem_ty Σ) : label * sem_sig Σ := ("yield", ∀S: _, τ ⇒ () | OS)%S.
  Definition yield_ty τ := τ -{ (yield_sig τ ·: ⟨⟩) }-> ().
  Definition iter_ty τ := (∀R: θ, (τ -{ ¡ θ }-> ()) -{ ¡ θ }-∘ ())%T.
  Definition generator_ty τ := (() → Option τ)%T.
  
  Lemma sem_typed_generate :
    ⊢ ⊨ᵥ generate : (∀T: α, iter_ty α → generator_ty α).
  Proof.
    iIntros "". iApply sem_typed_Tclosure. iIntros (α).
    rewrite -(app_nil_r []). iApply sem_typed_ufun; solve_sidecond. simpl.
    set cont_ty := (() -{ yield_sig α ·: ⟨⟩ }-∘ ()). 
    iApply (sem_typed_let (Refᶜ cont_ty) _ _ _ []); simpl; solve_sidecond. 
    - iApply sem_typed_alloc_cpy.
      rewrite -(app_nil_r [("i", _)]).
      iApply sem_typed_afun; solve_sidecond. simpl.
      iApply (sem_typed_app (yield_ty α) _ _ _ [("i", iter_ty α)]); solve_sidecond.
      + iApply sem_typed_sub_nil.
        iApply sem_typed_sub_ty.
        { iApply ty_le_aarr;[iApply row_le_os_elim| |iApply ty_le_refl]. 
          rewrite /yield_ty. iApply ty_le_uarr; try iApply ty_le_refl.
          iApply row_le_os_intro. }
        iApply (sem_typed_RApp (λ ρ, ( α -{ ¡ ρ }-> ()) -{ ¡ ρ }-∘ ())); solve_sidecond.
        iApply sem_typed_var.
      + iApply sem_typed_frame. iApply sem_typed_sub_nil.
        iApply sem_typed_val. rewrite /yield /yield_ty. iApply sem_typed_closure; solve_sidecond.
        simpl. iApply (sem_typed_perform_os () with "[]"). 
        iApply sem_typed_var'.
    - set Γ₁ :=[("cont", Refᶜ cont_ty)]; rewrite -(app_nil_r Γ₁). 
      iApply sem_typed_ufun; solve_sidecond. simpl.
      iApply (sem_typed_let cont_ty _ _ _ [("cont", Refᶜ cont_ty)]); solve_sidecond.
      + iApply sem_typed_contraction; solve_sidecond.
        iApply sem_typed_replace_cpy; first iApply sem_typed_var'.
        do 2 (iApply sem_typed_frame). rewrite -(app_nil_r []).
        iApply sem_typed_afun; solve_sidecond.
        simpl. iApply sem_typed_unit'.
      + rewrite app_singletons.
        iApply (sem_typed_shallow_try_os OS "yield" (λ _, α) (λ _, ()) () (Option α) ⊥ _ 
                      [("comp", cont_ty)] [] [] [("cont", Refᶜ cont_ty)]); solve_sidecond.
        { iApply row_le_refl. }
        * iApply sem_typed_app; [iApply sem_typed_var'|iApply sem_typed_unit']. 
        * iIntros (?). do 2 iApply sem_typed_swap_third.
          iApply sem_typed_seq.
          { iApply sem_typed_store_cpy; iApply sem_typed_var. }
          iApply sem_typed_some. iApply sem_typed_var.
        * simpl. do 2 iApply sem_typed_weaken.
          iApply sem_typed_none.
  Qed.
  
  Lemma sem_typed_iterate τ :
    ⊢ ⊨ᵥ iterate : (generator_ty τ → iter_ty τ).
  Proof.
    iIntros. iApply sem_typed_closure; first done. rewrite /iter_ty /=.
    rewrite - {1}(app_nil_r [("g", _)]). 
    iApply sem_typed_RLam; solve_sidecond. iIntros (θ).
    rewrite - {1}(app_nil_r [("g", _)]). 
    iApply sem_typed_sub_nil. 
    iApply sem_typed_afun; solve_sidecond. simpl.
    iApply sem_typed_app;
      [|iApply sem_typed_swap_second; iApply sem_typed_var'].
    rewrite - {1}((app_nil_r [("f", _)])). 
    iApply sem_typed_sub_u2aarr. iApply sem_typed_sub_nil.
    iApply sem_typed_ufun; solve_sidecond. simpl.
    set Γ₂ := [("g", generator_ty τ); ("go", generator_ty τ -{ ¡ θ }-> () ); ("f", τ -{ ¡ θ }-> ())].
    iApply (sem_typed_match_option (¡ θ)%R τ _ _ Γ₂); solve_sidecond.
    - iApply sem_typed_sub_nil.
      iApply sem_typed_app; solve_sidecond; last iApply sem_typed_unit'.
      iApply sem_typed_contraction; solve_sidecond. 
      iApply sem_typed_sub_u2aarr. iApply sem_typed_var'.
    - do 3 iApply sem_typed_weaken. iApply sem_typed_unit'.
    - iApply sem_typed_seq.
      + iApply sem_typed_app.
        { iApply sem_typed_sub_u2aarr. iApply sem_typed_var'. }
        iApply sem_typed_swap_fourth. iApply sem_typed_swap_second.
        iApply sem_typed_var'.
      + iApply sem_typed_app; [|iApply sem_typed_var'].
        iApply sem_typed_sub_u2aarr. iApply sem_typed_var'.
  Qed.

End typing.
