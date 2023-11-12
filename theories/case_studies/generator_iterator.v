
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
From affine_tes.lib Require Import base.
From affine_tes.lang Require Import hazel.
From affine_tes.logic Require Import sem_def.
From affine_tes.logic Require Import sem_env.
From affine_tes.logic Require Import sem_types.
From affine_tes.logic Require Import sem_sub_typing.
From affine_tes.logic Require Import sem_operators.
From affine_tes.logic Require Import tactics.
From affine_tes.logic Require Import compatibility.

Definition yield := (λ: "x", perform: "x")%V.
Definition generate :=
  (λ: "i", let: "cont" := ref (λ: <>, "i" <_> yield) in
      λ: <>, let: "comp" := "cont" <!- (λ: <>, #())  in
             shallow-try-os: "comp" #() with
                effect λ: "w" "k", "cont" <- "k" ;; SOME "w"
             |  return λ: "w", NONE
             end
  )%V.

Definition iterate :=
  (λ: "g", 
    (λ: <> "f", 
    (rec: "go" "g" := 
        match: "g" #() with
            NONE => #()
        |  SOME "x" => "f" "x" ;; "go" "g" 
        end) "g"))%V.

Section typing.

  Context `{!heapGS Σ}.

  Definition yield_sig (τ : sem_ty Σ) := (μ∀TS: _, _, τ ⇒ ())%R.
  Definition yield_ty τ := τ -{ ⟨yield_sig τ,⟩ }-> ().
  Definition iter_ty τ := (∀R: θ, (τ -{ θ }-> ()) -{ θ }-∘ ())%T.
  Definition generator_ty τ := (() → Option τ)%T.
  
  Lemma sem_typed_generate τ :
    ⊢ ⊨ᵥ generate : (iter_ty τ → generator_ty τ).
  Proof.
    iIntros "". iApply sem_typed_closure; first done.
    set cont_ty := (() -{ ⟨yield_sig τ,⟩ }-∘ ()). 
    iApply (sem_typed_let _ [] _ _ _ _ (Refᶜ cont_ty)); simpl; solve_sidecond. 
    - iApply sem_typed_alloc_cpy.
      rewrite -(app_nil_r [("i", _)]).
      iApply sem_typed_afun; solve_sidecond. simpl.
      iApply (sem_typed_app _ [("i", iter_ty τ)] _ _ _ (yield_ty τ)); solve_sidecond.
      + iApply (sem_typed_SApp _ _ _ ⟨yield_sig τ,⟩%R (λ ρ, ( τ -{ ρ }-> ()) -{ ρ }-∘ ())); solve_sidecond.
        iApply sem_typed_sub_nil. iApply sem_typed_var.
      + iApply sem_typed_frame_os. iApply sem_typed_sub_nil.
        iApply sem_typed_val. iApply sem_typed_closure; first done.
        simpl. iApply (sem_typed_perform_os _ _ _ () with "[]"). 
        iApply sem_typed_sub_nil. iApply sem_typed_var.
    - set Γ₁ :=[("cont", Refᶜ cont_ty)]; rewrite -(app_nil_r Γ₁). 
      iApply sem_typed_ufun; solve_sidecond. simpl.
      iApply (sem_typed_let _ [("cont", Refᶜ cont_ty)] _ _ _ _ cont_ty); solve_sidecond.
      + iApply sem_typed_contraction; solve_sidecond.
        iApply sem_typed_replace_cpy.
        { iApply sem_typed_sub_nil. iApply sem_typed_var. }
        do 2 iApply sem_typed_frame_os.
        rewrite -(app_nil_r []).
        iApply sem_typed_afun; solve_sidecond.
        simpl. iApply sem_typed_sub_nil. iApply sem_typed_unit.
      + rewrite app_singletons.
        iApply (sem_typed_shallow_try_os' 
                      [("comp", cont_ty)] [] [] [("cont", Refᶜ cont_ty)] 
                      "w" "k" _ _ _ (λ _ _, τ) (λ _ _, ()) (Option τ) ()); solve_sidecond.
        * iApply sem_typed_app; first solve_sidecond; 
          iApply sem_typed_sub_nil;
            [iApply sem_typed_var|iApply sem_typed_unit]. 
        * iIntros (?). do 2 iApply sem_typed_swap_third.
          iApply (sem_typed_seq _ [("w", τ)]).
          { iApply (sem_typed_store_cpy _ _ _ _ _ _ cont_ty); iApply sem_typed_var. }
          iApply sem_typed_some.
          iApply sem_typed_var.
        * simpl. do 2 iApply sem_typed_weaken.
          iApply sem_typed_none.
  Qed.
  
  Lemma sem_typed_iterate τ :
    ⊢ ⊨ᵥ iterate : (generator_ty τ → iter_ty τ).
  Proof.
    iIntros. iApply sem_typed_closure; first done. rewrite /iter_ty /=.
    rewrite - {1}(app_nil_r [("g", _)]). 
    iApply sem_typed_SLam; solve_sidecond. iIntros (θ).
    rewrite - {1}(app_nil_r [("g", _)]). 
    iApply sem_typed_sub_nil. 
    iApply sem_typed_afun; solve_sidecond. simpl.
    iApply sem_typed_app; first solve_sidecond;
      [|iApply sem_typed_sub_nil; iApply sem_typed_swap_second; iApply sem_typed_var].
    rewrite - {1}((app_nil_r [("f", _)])). 
    iApply sem_typed_sub_ty; [iApply ty_le_u2aarr|].
    iApply sem_typed_sub_nil.
    iApply sem_typed_ufun; solve_sidecond. simpl.
    set Γ₂ := [("g", generator_ty τ); ("go", generator_ty τ -{ θ }-> () ); ("f", τ -{ θ }-> ())].
    iApply (sem_typed_match_option _ Γ₂ _ _ _ _ _ θ τ); solve_sidecond.
    - iApply sem_typed_sub_nil. 
      iApply sem_typed_app; solve_sidecond; last iApply sem_typed_unit.
      iApply sem_typed_contraction; solve_sidecond. 
      iApply sem_typed_sub_nil. 
      iApply sem_typed_sub_ty; [iApply ty_le_u2aarr|iApply sem_typed_var].
    - iApply sem_typed_sub_nil. do 3 iApply sem_typed_weaken. iApply sem_typed_unit.
    - iApply (sem_typed_seq _ [("g", generator_ty τ ); ("go", generator_ty τ -{ θ }-> ())]).
      + iApply sem_typed_app; [solve_sidecond| |iApply sem_typed_sub_nil; iApply sem_typed_var].
        iApply sem_typed_sub_nil. iApply sem_typed_swap_third. 
        iApply sem_typed_sub_ty; [iApply ty_le_u2aarr|]. iApply sem_typed_var.
      + iApply sem_typed_app; [solve_sidecond| |iApply sem_typed_sub_nil; iApply sem_typed_var].
        iApply sem_typed_sub_nil. iApply sem_typed_sub_ty; [iApply ty_le_u2aarr|].
        iApply sem_typed_var.
  Qed.

End typing.
