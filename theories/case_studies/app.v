
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

Definition app : val := (Λ: Λ: Λ: λ: "f" "x", "f" "x")%V.

Section typing.

  Context `{!heapGS Σ}.

  Definition app_ty : sem_ty Σ := 
    (∀R: θ, ∀T: α, ∀T: β, (α -{ θ }-∘ β) → α -{ θ }-∘ β)%T.

  Lemma app_typed : ⊢ ⊨ᵥ app : app_ty.
  Proof.
    iIntros. rewrite /app /app_ty.
    iApply sem_typed_Rclosure; solve_sidecond. iIntros (θ).
    rewrite - (app_nil_l []).
    iApply sem_typed_TLam; solve_sidecond. iIntros (α).
    rewrite - (app_nil_l []).
    iApply sem_typed_TLam; solve_sidecond. iIntros (β).
    rewrite - (app_nil_l []).
    iApply sem_typed_ufun; solve_sidecond. simpl.
    rewrite - (app_nil_r [("f", _)]).
    iApply sem_typed_afun; solve_sidecond. simpl.
    iApply sem_typed_app_nil; iApply sem_typed_var'.
  Qed.

End typing.
