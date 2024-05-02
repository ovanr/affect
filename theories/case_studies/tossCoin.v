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
From haffel.logic Require Import sem_types.
From haffel.logic Require Import sem_judgement.
From haffel.logic Require Import copyable.
From haffel.logic Require Import sem_operators.
From haffel.logic Require Import compatibility.
From haffel.logic Require Import tactics.

(* The tossCoin example from paper Soundly Hanlding Linearity by Tang et al. *)

Definition tossCoin : val := 
  (Λ: λ: "g", let: "b" := "g" #() in 
              if: "b" then #(LitStr "heads") else #(LitStr "tails"))%V.

Section typing.

  Context `{!heapGS Σ}.

  Definition tossCoin_ty : sem_ty Σ := 
    (∀R: θ, (() -{ θ }-> 𝔹) -{ θ }-> Str)%T.

  Lemma tossCoin_typed : ⊢ ⊨ᵥ tossCoin : tossCoin_ty.
  Proof.
    iIntros. rewrite /tossCoin /tossCoin_ty.
    iApply sem_typed_Rclosure; solve_sidecond. iIntros (θ).
    rewrite - (app_nil_l []).
    iApply sem_typed_ufun; solve_sidecond. simpl.
    iApply (sem_typed_let 𝔹 θ Str _ []); solve_sidecond.
    - iApply (sem_typed_app_ms ()); solve_sidecond.
      { iApply sem_typed_sub_ty; first iApply ty_le_u2aarr.
        iApply sem_typed_var'. }
      iApply sem_typed_unit'.
    - iApply sem_typed_if; first iApply sem_typed_var';
      iApply sem_typed_string'.
  Qed.

End typing.
