
From iris.proofmode Require Import base tactics.
From Coq Require Import ssreflect ssrfun ssrbool.


(* Hazel Reasoning *)
From program_logic Require Import weakest_precondition 
                                  deep_handler_reasoning 
                                  state_reasoning.

(* Local imports *)
From affine_tes.lang Require Import hazel.
From affine_tes.logic Require Import sem_types.
From affine_tes.logic Require Import sem_typed.
From affine_tes.logic Require Import sem_sub_typing.
From affine_tes.logic Require Import sem_operators.
From affine_tes.logic Require Import compatibility.

Definition generate :=
  (λ: "i", let: "yield" := λ: "x", do: "x" in  
           let: "cont" := ref (λ: <>, "i" "yield") in
           λ: <>, let: "comp" := Load "cont" in 
              TryWith ("comp" #())
                (λ: "w" "k", ("cont" <- "k" ;; SOME "w"))%E
                (λ: "w", "cont" <- (λ: <>,  #()) ;; NONE )%E
  )%E. 

Context `{!heapGS Σ}.

Definition yield_sig (τ : sem_ty Σ) := (τ ⇒ ())%R.
Definition yield_ty τ := τ -{ yield_sig τ }-> ().
Definition iter_ty τ := ((yield_ty τ) -{ yield_sig τ }-∘ ())%T.
Definition generator_ty τ := (() ∘-> Option τ)%T.

Ltac solve_dom := try 
    (apply not_elem_of_nil) || 
    (apply not_elem_of_cons; split; solve_dom) || 
    (intros ?; match goal with
      | H : (BAnon ∈ env_dom _) |- _ => destruct H
      end) ||
    done.

Ltac solve_sidecond := solve_dom; solve_copy.

Lemma app_singletons {A} (x y : A) : [x;y] = [x] ++ [y].
Proof. done. Qed.

Lemma sem_typed_generate i τ :
  ⊢ [(i, iter_ty τ)] ⊨ generate i : ⟨⟩ : generator_ty τ ⊨ [].
Proof.
  iIntros.
  iApply sem_typed_app; [|iApply sem_typed_var].
  rewrite /generate {1}(symmetry (app_nil_r [])).
  iApply (sem_typed_afun [] [] "i" _ (iter_ty τ) ⟨⟩%R (generator_ty τ)); solve_sidecond.
  iApply (sem_typed_let _ [("i", iter_ty τ)] _ _ _ _ (yield_ty τ)); solve_sidecond. 
  - rewrite {1}(symmetry (app_nil_l [("i", iter_ty τ)])).
    iApply sem_typed_ufun; solve_sidecond.
    iApply sem_typed_do. 
    iApply sem_typed_sub_nil.
    iApply sem_typed_var.
  - set cont_ty := Ref (() -{ yield_sig τ }-∘ ()). 
    iApply (sem_typed_let _ [] _ _ _ _ cont_ty); solve_sidecond.
    + set Γ₁ :=[("yield", yield_ty τ); ("i", iter_ty τ)].
      iApply sem_typed_alloc.
      rewrite -(app_nil_r Γ₁).
      iApply sem_typed_afun; solve_dom.
      iApply (sem_typed_app _ [("i", iter_ty τ)] _ _ _ (yield_ty τ));
        do 2 (iApply sem_typed_sub_nil; iApply sem_typed_var).
    + set Γ₁ :=[("cont", cont_ty)]; rewrite -(app_nil_r Γ₁). 
      set in_cont_ty := (() -{ yield_sig τ }-∘ ()).
      iApply sem_typed_sufun; solve_sidecond.
      iApply (sem_typed_let _ [("cont", Ref Moved)] _ _ _ _ in_cont_ty); solve_sidecond.
      { iApply sem_typed_sub_nil. iApply sem_typed_load. }
      rewrite app_singletons.
      set r := fun (w : string) => ("cont" <- (λ: <>, #());; NONE)%E.
      fold (r "w").
      set h := fun (w k : string) => ("cont" <- "k";; SOME "w")%E.
      fold (h "w" "k"). rewrite /yield_sig.
      set e := ("comp" #()).
      iPoseProof (sem_typed_shallow_try 
                    [("comp", in_cont_ty)] [] [("cont", cont_ty)] 
                    [("cont", Ref Moved)]
                    "w" "k" e h r τ () (Option τ) ()) as "Hhand"; solve_sidecond.
      rewrite /Γ₁. iApply "Hhand"; iClear "Hhand".
      * rewrite /e. iApply sem_typed_app; iApply sem_typed_sub_nil;
          [iApply sem_typed_var|iApply sem_typed_unit]. 
      * rewrite /h. 
        iApply (sem_typed_swap_third).
        iApply sem_typed_seq.
        { iApply sem_typed_store. 
          iApply sem_typed_swap_third.
          iApply sem_typed_var. }
        iApply sem_typed_swap_second.
        iApply sem_typed_some.
        iApply sem_typed_var.
      * rewrite /r. simpl.
        iApply sem_typed_weaken.
        iApply sem_typed_seq. 
        iApply sem_typed_store.
        { rewrite -(app_nil_l [("cont", Ref Moved)]). 
          iApply (sem_typed_afun _ _ _ _ () (yield_sig τ) ()); solve_sidecond.
          iApply sem_typed_sub_nil.
          iApply sem_typed_unit. }
        iApply sem_typed_none.
Qed.
