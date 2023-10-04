
From stdpp Require Import base list.
From iris.proofmode Require Import base tactics.
From iris.algebra Require Import excl_auth.


(* Hazel Reasoning *)
From program_logic Require Import weakest_precondition 
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
From affine_tes.logic Require Import reasoning.
From affine_tes.logic Require Import sem_sub_typing.
From affine_tes.logic Require Import sem_operators.
From affine_tes.logic Require Import compatibility.
From affine_tes.logic Require Import tactics.

Definition async : val := (λ: "c", perform: (InjL "c"))%V.
Definition await : val := (λ: "p", (perform: (InjR "p")) ;; #())%V.
Definition yield : val := (λ: <>, await (async (λ: <>, #())))%V.

Definition async' : val := 
    (λ: "c", let: "r" := ref NONE
             in (async (λ: <>, "r" <- SOME ("c" #())), "r"))%V.  
                                    
Section typing.

  Context `{!heapGS Σ}.

  Definition queue_ty := (μT: α, Ref (List (α → α))).

  Definition prom_id := (@sem_ty_unit Σ).

  Definition status_ty := (() + (List (queue_ty → queue_ty))).

  Definition promise_ty := (Ref status_ty).

  Definition cpromise_ty τ := (prom_id × Ref (Option τ)). 

  Definition asig := (μS: α, ( () -{ α }-∘ () ) + prom_id ⇒ prom_id)%R. 

  Lemma async_typed :
    ⊢ ⊨ᵥ async : ( (() -{ asig }-∘ ()) -{ asig }-> prom_id ).
  Proof.
    iIntros "". iApply sem_typed_closure.
    iApply (sem_typed_perform with "[]").
    { intros ????. by repeat f_equiv. } 
    iApply sem_typed_left_inj.
    iApply sem_typed_sub_nil.
    iApply sem_typed_var.
  Qed.

  Lemma await_typed :
    ⊢ ⊨ᵥ await : ( prom_id -{ asig }-> () ).
  Proof.
    iIntros "". iApply sem_typed_closure.
    iApply sem_typed_seq.
    - iApply (sem_typed_perform with "[]").
      { intros ????. by repeat f_equiv. } 
      iApply sem_typed_sub_nil.
      iApply sem_typed_right_inj.
      iApply sem_typed_var. 
    - iApply sem_typed_sub_nil.
      iApply sem_typed_unit.
  Qed.

  Lemma yield_typed :
    ⊢ ⊨ᵥ yield : ( () -{ asig }-> () ).
  Proof.
    iIntros "". iApply sem_typed_closure. simpl.
    rewrite [Val await](@app_mult_env_dom_nil Σ) - {3} (app_nil_r []).
    iApply (sem_typed_app _ [] _ _ _ _ _ prom_id).
    { iApply sem_typed_sub_nil.
      iApply sem_typed_val.
      iApply await_typed. }
    rewrite [Val async](@app_mult_env_dom_nil Σ).
    iApply (sem_typed_app _ [] _ _ _ _ _ _).
    { iApply sem_typed_sub_nil.
      iApply sem_typed_val.
      iApply async_typed. }
    iApply sem_typed_sub_nil.
    rewrite [(λ: <>, _)%E](@ctx_lambda_env_dom_nil Σ).
    rewrite -(app_nil_r []).
    iApply (sem_typed_afun _ _ [] []); solve_sidecond. simpl.
    iApply sem_typed_sub_nil.
    iApply sem_typed_unit.
  Qed.


End typing.
