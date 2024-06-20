
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
From affect.logic Require Import sem_types.
From affect.logic Require Import sem_judgement.
From affect.logic Require Import copyable.
From affect.logic Require Import sem_operators.
From affect.logic Require Import compatibility.
From affect.logic Require Import tactics.

(* Make all the definitions opaque so that we do not rely on their definition in the model to show that the programs are well-typed terms. *)
Opaque sem_typed sem_typed_val ty_le row_le sig_le row_type_sub row_env_sub.
Opaque sem_ty_void sem_ty_unit sem_ty_bool sem_ty_int sem_ty_string sem_ty_top sem_ty_cpy sem_env_cpy sem_ty_ref_cpy sem_ty_ref sem_ty_prod sem_ty_sum sem_ty_arr sem_ty_aarr sem_ty_uarr sem_ty_forall sem_ty_row_forall sem_ty_exists sem_ty_rec sem_ty_option sem_ty_list.
Opaque sem_sig_eff sem_sig_os.
Opaque sem_row_nil sem_row_os sem_row_cons sem_row_rec.

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
    iApply (sem_typed_app_os α (¡θ)%R); solve_sidecond.
    { iApply sem_typed_app_os; iApply sem_typed_var'. }
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
