
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

Definition C : val := (Λ: Λ: Λ: Λ: λ: "x" "y" "z", ("x" "z") "y")%V.

Section typing.

  Context `{!heapGS Σ}.

  Definition C_os_ty : sem_ty Σ := 
    (∀R: θ, ∀T: α, ∀T: β, ∀T: γ,  (β -{ ¡ θ }-∘ (α -{ ¡ θ }-∘ γ)) → α ⊸ β -{ ¡ θ }-∘ γ)%T.

  Definition C_ms_ty : sem_ty Σ := 
    (∀R: θ, ∀T: α, ∀T: β, ∀T: γ,  (β -{ θ }-∘ ('! α -{ θ }-∘ γ)) → ('! α) ⊸ β -{ θ }-∘ γ)%T.

  Lemma C_os_typed : ⊢ ⊨ᵥ C : C_os_ty.
  Proof.
    iIntros. rewrite /C /C_os_ty.
    iApply sem_typed_Rclosure; solve_sidecond. iIntros (θ).
    rewrite - (app_nil_l []).
    iApply sem_typed_TLam; solve_sidecond. iIntros (α).
    rewrite - (app_nil_l []).
    iApply sem_typed_TLam; solve_sidecond. iIntros (β).
    rewrite - (app_nil_l []).
    iApply sem_typed_TLam; solve_sidecond. iIntros (γ).
    rewrite - (app_nil_l []).
    iApply sem_typed_ufun; solve_sidecond. simpl.
    rewrite - (app_nil_r [("x", _)]).
    iApply sem_typed_afun; solve_sidecond. simpl.
    rewrite - (app_nil_r [("y", _); ("x", _)]).
    iApply sem_typed_afun; solve_sidecond. simpl.
    iApply sem_typed_swap_second.
    iApply (sem_typed_app α θ); solve_sidecond.
    { iApply row_le_refl. }
    { iApply sem_typed_app; first iApply row_le_refl; iApply sem_typed_var'. }
    iApply sem_typed_var'.
  Qed.

  Lemma C_ms_typed : ⊢ ⊨ᵥ C : C_ms_ty.
  Proof.
    iIntros. rewrite /C /C_ms_ty.
    iApply sem_typed_Rclosure; solve_sidecond. iIntros (θ).
    rewrite - (app_nil_l []).
    iApply sem_typed_TLam; solve_sidecond. iIntros (α).
    rewrite - (app_nil_l []).
    iApply sem_typed_TLam; solve_sidecond. iIntros (β).
    rewrite - (app_nil_l []).
    iApply sem_typed_TLam; solve_sidecond. iIntros (γ).
    rewrite - (app_nil_l []).
    iApply sem_typed_ufun; solve_sidecond. simpl.
    rewrite - (app_nil_r [("x", _)]).
    iApply sem_typed_afun; solve_sidecond. simpl.
    rewrite - (app_nil_r [("y", _); ("x", _)]).
    iApply sem_typed_afun; solve_sidecond. simpl.
    iApply sem_typed_swap_second.
    iApply (sem_typed_app_ms ('! α)); solve_sidecond.
    { iApply sem_typed_app_nil; iApply sem_typed_var'. }
    iApply sem_typed_var'.
  Qed.

End typing.
