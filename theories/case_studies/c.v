
From stdpp Require Import base list.
From iris.proofmode Require Import base tactics.
From iris.algebra Require Import excl_auth.

(* Local imports *)
From affect.lib Require Import base.
From affect.lang Require Import affect.
From affect.logic Require Import sem_def.
From affect.logic Require Import sem_env.
From affect.logic Require Import sem_sig.
From affect.logic Require Import sem_row.
From affect.logic Require Import sem_types.
From affect.logic Require Import sem_judgement.
From affect.logic Require Import sem_operators.
From affect.logic Require Import compatibility.
From affect.logic Require Import tactics.

(* Make all the definitions opaque so that we do not rely on their definition in the model to show that the programs are well-typed terms. *)
Opaque sem_typed sem_typed_val ty_le row_le sig_le row_type_sub row_env_sub.
Opaque sem_ty_bot sem_ty_unit sem_ty_bool sem_ty_int sem_ty_top sem_ty_mbang env_mbang sem_ty_ref_cpy sem_ty_ref sem_ty_prod sem_ty_sum sem_ty_arr sem_ty_type_forall sem_ty_row_forall sem_ty_exists sem_ty_rec sem_ty_option sem_ty_list.
Opaque sem_sig_eff sem_sig_flip_mbang.
Opaque sem_row_nil sem_row_flip_mbang sem_row_cons sem_row_rec.

Definition C : val := (λ: "x" "y" "z", ("x" "z") "y")%V.

Section typing.

  Context `{!heapGS Σ}.

  Definition C_os_ty : sem_ty Σ := 
    (∀ᵣ θ, ∀ₜ α, ∀ₜ β, ∀ₜ γ,  (β -{ ¡ θ }-∘ (α -{ ¡ θ }-∘ γ)) → α ⊸ β -{ ¡ θ }-∘ γ)%T.

  Definition C_ms_ty : sem_ty Σ := 
    (∀ᵣ θ, ∀ₜ α, ∀ₜ β, ∀ₜ γ,  (β -{ θ }-∘ (![MS] α -{ θ }-∘ γ)) → (![MS] α) ⊸ β -{ θ }-∘ γ)%T.

  Definition C_gen_ty : sem_ty Σ := 
    (∀ₘ ν, ∀ᵣ θ, ∀ₜ α, ∀ₜ β, ∀ₜ γ, (β -{ ¡[ν] θ }-∘ (![ν] α -{ ¡[ν] θ }-∘ γ)) → (![ν] α) ⊸ β -{ ¡[ν] θ }-∘ γ)%T.

  Lemma C_os_typed : ⊢ ⊨ᵥ C : C_os_ty.
  Proof.
    iIntros. rewrite /C /C_os_ty.
    iApply sem_typed_Rclosure; iIntros (θ).
    iApply sem_typed_Tclosure; iIntros (α).
    iApply sem_typed_Tclosure; iIntros (β).
    iApply sem_typed_Tclosure; iIntros (γ).
    iApply sem_typed_closure; first done. simpl.
    rewrite - (app_nil_r [("x", _)]).
    smart_apply sem_typed_afun. simpl.
    rewrite - (app_nil_r [("y", _); ("x", _)]).
    smart_apply sem_typed_afun. simpl.
    iApply sem_typed_swap_second.
    iApply (sem_typed_app_os α (¡θ)%R).
    { iApply sem_typed_app_os; iApply sem_typed_var'. }
    iApply sem_typed_var'.
  Qed.

  Lemma C_ms_typed : ⊢ ⊨ᵥ C : C_ms_ty.
  Proof.
    iIntros. rewrite /C /C_ms_ty.
    iApply sem_typed_Rclosure; iIntros (θ).
    iApply sem_typed_Tclosure; iIntros (α).
    iApply sem_typed_Tclosure; iIntros (β).
    iApply sem_typed_Tclosure; iIntros (γ).
    iApply sem_typed_closure; first done. simpl.
    rewrite - (app_nil_r [("x", _)]).
    smart_apply sem_typed_afun. simpl.
    rewrite - (app_nil_r [("y", _); ("x", _)]).
    smart_apply sem_typed_afun. simpl.
    iApply sem_typed_swap_second.
    iApply (sem_typed_app_ms (![MS] α)).
    { iApply sem_typed_app_nil; iApply sem_typed_var'. }
    iApply sem_typed_var'.
  Qed.

  Lemma C_gen_typed : ⊢ ⊨ᵥ C : C_gen_ty.
  Proof.
    iIntros. rewrite /C_gen_ty /C.
    iApply sem_typed_Mclosure. iIntros (ν).
    iApply sem_typed_Rclosure. iIntros (θ).
    iApply sem_typed_Tclosure. iIntros (α).
    iApply sem_typed_Tclosure. iIntros (β).
    iApply sem_typed_Tclosure. iIntros (γ).
    iApply sem_typed_closure; first done. simpl.
    rewrite - (app_nil_r [("x", _)]).
    smart_apply sem_typed_afun. simpl.
    rewrite - (app_nil_r [("y", _); ("x", _)]).
    smart_apply sem_typed_afun. simpl.
    rewrite - (app_nil_r [("y", _); ("x", _)]).
    iApply (sem_typed_app_gen (![ν] α) (¡[ν] θ)%R (¡[ν] θ)%R (¡[ν] θ)%R).
    - iApply row_le_refl.
    - iApply row_le_refl.
    - iApply (sem_typed_app_gen β (¡ ⟨⟩)%R (¡[ν] θ)%R (¡[ν] θ)%R).
      + iApply row_le_trans; [iApply (row_le_mfbang_elim_nil OS)|iApply row_le_nil].
      + iApply row_le_refl.
      + iApply sem_typed_var'.
      + iApply sem_typed_var'.
    - iApply sem_typed_swap_second. iApply sem_typed_var'.
  Qed.

End typing.
