
(* sem_def.v *)

(* This file contains the definition of types, signatures, rows and environments.
*)

From iris.proofmode Require Import base tactics classes.
From iris.algebra Require Import list ofe gmap.
From iris.program_logic Require Import weakestpre.

(* Hazel Reasoning *)
From hazel.program_logic Require Import weakest_precondition
                                        state_reasoning.

(* Local imports *)
From haffel.lib Require Import base.
From haffel.lang Require Import haffel.

(* -------------------------------------------------------------------------- *)
(** Inhabited. *)
Global Instance mode_inhabited : Inhabited mode := populate MS.

(** OFE Structure. *)
Canonical Structure modeO := leibnizO mode.
Canonical Structure stringO := leibnizO string.


(** * Semantic Types. *)

(* We equip sem_ty with the OFE structure val -d> iPropO
 * which is the OFE of non-dependently-typed functions over a discrete domain *)
Definition sem_ty Σ := (val -d> iPropO Σ)%type.

Declare Scope sem_ty_scope.
(* Bind Scope sem_ty_scope with sem_ty. *)
Delimit Scope sem_ty_scope with T.

(** * Semantic Effect Signature. *)

Definition sem_sig Σ := (modeO * iEff Σ)%type.

Declare Scope sem_sig_scope.
(* Bind Scope sem_sig_scope with sem_sig. *)
Delimit Scope sem_sig_scope with S.

(** * Semantic Effect Row. *)

Definition sem_row Σ := (gmapO (operation * natO) (sem_sig Σ))%type.

Declare Scope sem_row_scope.
(* Bind Scope sem_row_scope with sem_row. *)
Delimit Scope sem_row_scope with R.


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


Definition env Σ := (list (string * sem_ty Σ)).

Declare Scope sem_env_scope.

Delimit Scope sem_env_scope with EN.

(* Copyable types *)
Definition copy_ty {Σ} (τ : sem_ty Σ) := 
  tc_opaque (□ (∀ v, τ%T v -∗ □ τ%T v))%I.

Global Instance copy_ty_persistent {Σ} (τ : sem_ty Σ) :
  Persistent (copy_ty τ).
Proof.
  unfold copy_ty, tc_opaque. apply _.
Qed.

(** The domain of the environment. *)
Definition env_dom {Σ} (Γ : env Σ) : list string := (map fst Γ).
Global Opaque env_dom.

Fixpoint env_sem_typed {Σ} (Γ : env Σ) (vs : gmap string val) : iProp Σ :=
  match Γ with
    | [] => emp
    | (x,A) :: Γ' => (∃ v, ⌜ vs !! x = Some v ⌝ ∗ A v) ∗ 
                     env_sem_typed Γ' vs
  end.

Notation "⟦ Γ ⟧" := (env_sem_typed Γ)%T.

Global Instance env_sem_typed_into_exist {Σ} x τ (Γ : env Σ) vs : 
  IntoExist (⟦ (x, τ) :: Γ ⟧ vs) (λ v, ⌜ vs !! x = Some v ⌝ ∗ τ v ∗ ⟦ Γ ⟧ vs)%I (to_ident_name v).
Proof.
  rewrite /IntoExist /=. iIntros "[(%v & Hrw & Hτ) HΓ]". 
  iExists v. iFrame.
Qed.

Global Instance env_sem_typed_from_exist {Σ} x τ (Γ : env Σ) vs: 
  FromExist (⟦ (x, τ) :: Γ ⟧ vs) (λ v, ⌜ vs !! x = Some v ⌝ ∗ τ v ∗ ⟦ Γ ⟧ vs)%I .
Proof.
  rewrite /FromExist /=. iIntros "[%v (Hrw & Hτ & HΓ)]". 
  iFrame. iExists v. iFrame.
Qed.

Global Opaque env_sem_typed.

(* Copyable environment *)
Definition copy_env {Σ} (Γ : env Σ) :=
  tc_opaque (□ (∀ vs, ⟦ Γ ⟧ vs -∗ □ ⟦ Γ ⟧ vs))%I.

Global Instance copy_env_persistent {Σ} (Γ : env Σ) :
  Persistent (copy_env Γ).
Proof.
  unfold copy_env, tc_opaque. apply _.
Qed.

(* Sub-typing and relations *)

(* Relation on mode *)
Definition mode_le {Σ} (m m' : modeO) : iProp Σ := 
  (m ≡ m' ∨ m ≡ MS)%I.

Definition ty_le {Σ} (A B : sem_ty Σ) := tc_opaque (□ (∀ v, A v -∗ B v))%I.
Global Instance ty_le_persistent {Σ} τ τ' :
  Persistent (@ty_le Σ τ τ').
Proof.
  unfold ty_le, tc_opaque. apply _.
Qed.

Definition sig_le {Σ} (σ σ' : sem_sig Σ) := tc_opaque (mode_le σ.1 σ'.1 ∗ iEff_le σ.2 σ'.2)%I.
Global Instance sig_le_persistent {Σ} σ σ' :
  Persistent (@sig_le Σ σ σ').
Proof.
  unfold sig_le, tc_opaque. apply _.
Qed.

Definition row_le {Σ} (ρ ρ' : sem_row Σ) := 
  tc_opaque (∀ l s σ, lookup (l, s) ρ ≡ Some σ -∗ 
                      ∃ σ', lookup (l, s) ρ' ≡ Some σ' ∗ sig_le σ σ')%I. 

Global Instance row_le_persistent {Σ} ρ ρ' :
  Persistent (@row_le Σ ρ ρ').
Proof.
  unfold row_le, tc_opaque. apply _.
Qed.

Definition env_le {Σ} (Γ₁ Γ₂ : env Σ) :=
  tc_opaque (□ (∀ vs, ⟦ Γ₁ ⟧ vs -∗ ⟦ Γ₂ ⟧ vs))%I.
Global Instance env_le_persistent {Σ} (Γ Γ' : env Σ) :
  Persistent (env_le Γ Γ').
Proof.
  unfold env_le, tc_opaque. apply _.
Qed.

Notation "m '≤M' m'" := (mode_le m m') (at level 98).
Notation "m '≤M@{' Σ } m'" := (@mode_le Σ m m') (at level 98, only parsing).
Notation "τ '≤T' κ" := (ty_le τ%T κ%T) (at level 98).
Notation "σ '≤S' σ'" := (sig_le σ%S σ'%S) (at level 98).
Notation "ρ '≤R' ρ'" := (row_le ρ%R ρ'%R) (at level 98).
Notation "Γ₁ '≤E' Γ₂" := (env_le Γ₁ Γ₂) (at level 98).

Global Instance mode_le_ne {Σ} :
  NonExpansive2 (@mode_le Σ).
Proof. intros ???????. rewrite /mode_le. by repeat f_equiv. Qed.

Global Instance mode_le_proper {Σ} :
  Proper ((≡) ==> (≡) ==> (≡)) (@mode_le Σ).
Proof. apply ne_proper_2. apply _. Qed.

Global Instance ty_le_ne {Σ} :
  NonExpansive2 (@ty_le Σ).
Proof.
  intros n τ κ Hequiv τ' κ' Hequiv'. 
  rewrite /ty_le /tc_opaque. repeat f_equiv; by apply non_dep_fun_dist.
Qed.

Global Instance ty_le_proper {Σ} :
  Proper ((≡) ==> (≡) ==> (≡)) (@ty_le Σ).
Proof. apply ne_proper_2. apply _. Qed.

Global Instance sig_le_ne {Σ} :
  NonExpansive2 (@sig_le Σ).
Proof.
  intros n σ₁ σ₂ Hequiv σ₁' σ₂' Hequiv'. 
  rewrite /sig_le /tc_opaque. by repeat f_equiv.
Qed.

Global Instance sig_le_proper {Σ} :
  Proper ((≡) ==> (≡) ==> (≡)) (@sig_le Σ).
Proof. apply ne_proper_2. apply _. Qed.

Global Instance row_le_ne {Σ} :
  NonExpansive2 (@row_le Σ).
Proof.
  intros n ρ₁ ρ₂ Hequiv ρ₁' ρ₂' Hequiv'.
  rewrite /row_le /tc_opaque. by repeat f_equiv.
Qed.

Global Instance row_le_proper {Σ} :
  Proper ((≡) ==> (≡) ==> (≡)) (@row_le Σ).
Proof. apply ne_proper_2. apply _. Qed.
