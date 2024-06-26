
(* sem_judgements.v *)

(* This file contains the definition of semantic typing judgments.
*)

From iris.proofmode Require Import base tactics classes.
From iris.algebra Require Import list.
From iris.program_logic Require Import weakestpre.

From stdpp Require Import base gmap.

(* Hazel Reasoning *)
From hazel.program_logic Require Import weakest_precondition
                                        state_reasoning.

(* Local imports *)
From affect.lib Require Import base.
From affect.lang Require Import affect.
From affect.logic Require Import sem_def.
From affect.logic Require Import sem_sig.
From affect.logic Require Import sem_row.
From affect.logic Require Import ewpw.

(* Semantic typing judgment. *)

(* The semantic typing judgment is defined to be persistent
 * because we want the persistent resources it uses to only be 
 * from the environment Γ.
 *)
Definition sem_typed `{!heapGS Σ}
  (Γ₁ : env Σ)
  (e : expr)
  (ρ : sem_row Σ)
  (τ : sem_ty Σ) 
  (Γ₂ : env Σ) : iProp Σ :=
    tc_opaque (□ (∀ (vs : gmap string val),
                    env_sem_typed Γ₁ vs -∗ 
                    (EWPW (subst_map vs e) <| ρ |> {{ v, τ v ∗ env_sem_typed Γ₂ vs }})))%I.

Global Instance sem_typed_persistent `{!heapGS Σ} (Γ Γ' : env Σ) e ρ τ :
  Persistent (sem_typed Γ e ρ τ Γ').
Proof.
  unfold sem_typed, tc_opaque. apply _.
Qed.

Notation "Γ₁ ⊨ e : ρ : α ⊨ Γ₂" := (sem_typed Γ₁ e%E ρ%R α%T Γ₂)
  (at level 74, e, ρ, α at next level) : bi_scope.

Notation "⊨ e : ρ : α" := (sem_typed [] e%E ρ%R α%T [])
  (at level 74, e, ρ, α at next level) : bi_scope.

(* The value semantic typing judgement is also defined
 * to be persistent, so only persistent values hold for it.
 *) 
Definition sem_val_typed `{!irisGS eff_lang Σ} 
  (v : val) 
  (A : sem_ty Σ) : iProp Σ := tc_opaque (□ (A v))%I.

Notation "⊨ᵥ v : τ" := (sem_val_typed v%V τ%T)
  (at level 20, v, τ at next level) : bi_scope.
Global Instance sem_typed_val_persistent `{!irisGS eff_lang Σ} v τ :
  Persistent (sem_val_typed v τ).
Proof.
  unfold sem_val_typed, tc_opaque. apply _.
Qed.
