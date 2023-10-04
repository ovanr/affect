
(* sem_typed.v *)

(* This file contains the definition semantic typing judgments and 
   typed environments.
*)

From iris.proofmode Require Import base tactics classes.
From iris.algebra Require Import list.
From iris.program_logic Require Import weakestpre.

From stdpp Require Import base gmap.


(* Hazel Reasoning *)
From program_logic Require Import weakest_precondition 
                                  state_reasoning.

(* Local imports *)
From affine_tes.lib Require Import base.
From affine_tes.lang Require Import hazel.
From affine_tes.lang Require Import subst_map.
From affine_tes.logic Require Import iEff.

(** * Semantic Types. *)

(* We equip sem_ty with the OFE structure val -d> iPropO
 * which is the OFE of non-dependently-typed functions over a discrete domain *)
Definition sem_ty Σ := val -d> (iPropO Σ).

Declare Scope sem_ty_scope.
Bind Scope sem_ty_scope with sem_ty.
Delimit Scope sem_ty_scope with T.

(** * Semantic Effect Signature. *)

Notation sem_sig Σ := (iEff Σ).

Declare Scope sem_sig_scope.
Bind Scope ieff_scope with sem_sig.
Delimit Scope sem_sig_scope with R.


(** The Type Environment

The type environment is represented as a list.
Due to the requirement that a type environment Γ is env_sem_typed,
we can utilize the seperation logic's disjointness to argue about
variables occuring twice in the environment.

Thus if we have a `env_sem_typed Γ vs` assumption and
the same variable occurs twice in Γ we get that:

∙ They cannot be of the same non-persistent type (e.g. ref nat):
  So if we have `env_typed (l : ref nat; l : ref nat) vs`,  
  since the variables l are the same, we would have
  that l, v ∈ vs, and that ⟦ ref nat ⟧ v ∗ ⟦ ref nat ⟧ v
  But that means we would need to provide that l ↦ w ∗ l ↦ w
  which would be impossible.

∙ If they have the same type which is a persistent type (e.g. nat):
  Then it is fine, in fact it must be allowed to allow for Copy types

∙ If they don't have the same type:
  Then `vs` would still have only 1 value for the variable `l` so
  it would be impossible to provide env_typed proof.

*) 

Canonical Structure stringO := leibnizO string.

Notation env Σ := (list (stringO * sem_ty Σ)).

(** The domain of the environment. *)
Definition env_dom {Σ} (Γ : env Σ) : list string := (map fst Γ).
Global Opaque env_dom.

Fixpoint env_sem_typed `{irisGS eff_lang Σ} (Γ : env Σ)
                        (vs : gmap string val) : iProp Σ :=
  match Γ with
    | [] => emp
    | (x,A) :: Γ' => (∃ v, ⌜ vs !! x = Some v ⌝ ∗ A v) ∗ 
                     env_sem_typed Γ' vs
  end.

Notation "⟦ Γ ⟧" := (env_sem_typed Γ)%T.

Global Instance env_sem_typed_into_exist `{irisGS eff_lang Σ} x τ Γ vs : 
  IntoExist (⟦ (x, τ) :: Γ ⟧ vs) (λ v, ⌜ vs !! x = Some v ⌝ ∗ τ v ∗ ⟦ Γ ⟧ vs)%I (to_ident_name v).
Proof.
  rewrite /IntoExist /=. iIntros "[(%v & Hrw & Hτ) HΓ]". 
  iExists v. iFrame.
Qed.

Global Instance env_sem_typed_from_exist `{irisGS eff_lang Σ} x τ Γ vs: 
  FromExist (⟦ (x, τ) :: Γ ⟧ vs) (λ v, ⌜ vs !! x = Some v ⌝ ∗ τ v ∗ ⟦ Γ ⟧ vs)%I .
Proof.
  rewrite /FromExist /=. iIntros "[%v (Hrw & Hτ & HΓ)]". 
  iFrame. iExists v. iFrame.
Qed.

Global Opaque env_sem_typed.

(* Semantic typing judgment. *)

(* The semantic typing judgment is defined to be persistent
 * because we want the persistent resources it uses to only be 
 * from the environment Γ.
 *)
Definition sem_typed `{!irisGS eff_lang Σ}
  (Γ₁  : env Σ)
  (e  : expr)
  (ρ  : sem_sig Σ)
  (τ  : sem_ty Σ) 
  (Γ₂  : env Σ) : iProp Σ :=
    tc_opaque( □ (∀ Φ (vs : gmap string val),
                    env_sem_typed Γ₁ vs -∗ 
                    (∀ v, τ v ∗ env_sem_typed Γ₂ vs -∗ Φ v) -∗ 
                    EWP (subst_map vs e) <| ρ |> {{ v, Φ v }}))%I.

Global Instance sem_typed_persistent `{!irisGS eff_lang Σ} (Γ Γ' : env Σ) e ρ τ :
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
  (A : sem_ty Σ) : iProp Σ := □ (A v).

Notation "⊨ᵥ v : A" := (sem_val_typed v%V A%T)
  (at level 20, v, A at next level) : bi_scope.