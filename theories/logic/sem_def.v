
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

(** * Persistently Monotonic Protocols. *)
(** Persistently Monotonic Protocols are defined using a record, which bundles an iEff protocol
[pmono_prot_car : iEff Σ] together with a proof of it being persistently monotonic. *)

Definition pers_mono {Σ} (Ψ : iEff Σ) : iProp Σ :=
  (∀ (v : val) (Φ Φ' : val → iPropI Σ),
      □ (∀ w : val, Φ w -∗ Φ' w) -∗ iEff_car Ψ v Φ -∗ iEff_car Ψ v Φ')%I.

Record pmono_prot Σ := PMonoProt {
  pmono_prot_car :> iEff Σ;
  pmono_prot_prop : ⊢ pers_mono pmono_prot_car
}.
Arguments PMonoProt {_} _%I {_}.
Arguments pmono_prot_car {_} _ : simpl never.

(** * The COFE structure on pmono protocols *)
Section pmono_prot_cofe.
  Context {Σ : gFunctors}.

  Instance pmono_prot_equiv : Equiv (pmono_prot Σ) := λ Ψ1 Ψ2, pmono_prot_car Ψ1 ≡ pmono_prot_car Ψ2.
  Instance pmono_prot_dist : Dist (pmono_prot Σ) := λ n Ψ1 Ψ2, pmono_prot_car Ψ1 ≡{n}≡ pmono_prot_car Ψ2.
  Lemma pmono_prot_ofe_mixin : OfeMixin (pmono_prot Σ).
  Proof. by apply (iso_ofe_mixin pmono_prot_car). Qed.
  Canonical Structure pmono_protO := Ofe (pmono_prot Σ) pmono_prot_ofe_mixin.
  Global Instance pmono_prot_cofe : Cofe pmono_protO.
  Proof.
    apply (iso_cofe_subtype' (λ Ψ, ⊢ pers_mono Ψ)
      (@PMonoProt _) pmono_prot_car)=> //.
    - by intros [].
    - apply bi.limit_preserving_emp_valid.
      intros ????. rewrite /pers_mono.
      do 8 f_equiv; apply non_dep_fun_dist;
       apply (non_dep_fun_dist _  _ a (iEff_car x) (iEff_car y)); by f_equiv.
  Qed.

  Global Program Instance pmono_prot_inhabited : Inhabited (pmono_prot Σ) := 
    populate (PMonoProt inhabitant).
  Next Obligation.
    rewrite /pers_mono /inhabitant /=. iIntros (???) "_ _ //".
  Qed.

  Global Instance pmono_prot_car_ne n : Proper (dist n ==> dist n) pmono_prot_car.
  Proof. by intros Ψ1 Ψ2 ?. Qed.
  Global Instance pmono_prot_car_proper : Proper ((≡) ==> (≡)) (@pmono_prot_car Σ).
  Proof. by intros Ψ1 Ψ2 ?. Qed.

  Global Instance pmono_prot_ne n Ψ : Proper ((λ _ _, True) ==> dist n) (@PMonoProt Σ Ψ).
  Proof. intros P1 P2 _ ?. apply non_dep_fun_dist. rewrite /pmono_prot_car //. Qed.
  Global Instance pmono_prot_proper Ψ : Proper ((λ _ _, True) ==> (≡)) (@PMonoProt Σ Ψ).
  Proof. intros P1 P2 _ ?. apply non_dep_fun_equiv. rewrite /pmono_prot_car //. Qed.

  Global Program Instance pmono_prot_bottom : Bottom (pmono_prot Σ) := @PMonoProt Σ ⊥ _.
  Next Obligation. rewrite /pers_mono. iIntros (???) "_ [] //". Qed.

End pmono_prot_cofe.

Lemma pmono_prot_equivI {Σ} (Ψ1 Ψ2 : pmono_prot Σ) :
  Ψ1 ≡ Ψ2 ⊢@{iProp Σ} (pmono_prot_car Ψ1) ≡ (pmono_prot_car Ψ2).
Proof. iIntros "H". by iRewrite "H". Qed.

Lemma pmono_prot_iEff_equivI {Σ} (Ψ1 Ψ2 : pmono_prot Σ) :
  Ψ1 ≡ Ψ2 ⊢@{iProp Σ} ∀ v Φ, iEff_car (pmono_prot_car Ψ1) v Φ ≡ iEff_car (pmono_prot_car Ψ2) v Φ.
Proof.
  iIntros "H % %". iPoseProof (pmono_prot_equivI with "H") as "HH".
  iApply (iEff_equivI _ _ with "HH").
Qed.

Arguments pmono_protO : clear implicits.

(** * Semantic Effect Signatures. *)

Definition sem_sig Σ := (pmono_prot Σ)%type.

Declare Scope sem_sig_scope.
Delimit Scope sem_sig_scope with S.

(** * Semantic Effect Row. *)

Definition sem_row_val_prop {Σ} (Ψ : pmono_prot Σ) : iProp Σ := 
  ∀ v Φ, iEff_car Ψ v Φ -∗ ∃ (op : operation) (s : nat) (v' : val), ⌜ v = (effect op, #s, v')%V ⌝.

Record sem_row Σ := SemRow {
  sem_row_car :> pmono_prot Σ;
  sem_row_prop : ⊢ sem_row_val_prop sem_row_car
}.
Arguments SemRow {_} _%I {_}.
Arguments sem_row_car {_} _ : simpl never.

(** * The COFE structure on semantic rows *)
Section sem_row_cofe.
  Context {Σ : gFunctors}.

  Instance sem_row_equiv : Equiv (sem_row Σ) := λ ρ1 ρ2, sem_row_car ρ1 ≡ sem_row_car ρ2.
  Instance sem_row_dist : Dist (sem_row Σ) := λ n ρ1 ρ2, sem_row_car ρ1 ≡{n}≡ sem_row_car ρ2.
  Lemma sem_row_ofe_mixin : OfeMixin (sem_row Σ).
  Proof. by apply (iso_ofe_mixin sem_row_car). Qed.
  Canonical Structure sem_rowO := Ofe (sem_row Σ) sem_row_ofe_mixin.
  Global Instance sem_row_cofe : Cofe sem_rowO.
  Proof.
    apply (iso_cofe_subtype' (λ Ψ, ⊢ sem_row_val_prop Ψ) (@SemRow _) sem_row_car)=> //.
    - by intros [].
    - apply bi.limit_preserving_emp_valid.
      intros ????. rewrite /sem_row_val_prop.
      do 6 f_equiv; apply non_dep_fun_dist. by f_equiv.
  Qed.

  Global Program Instance sem_row_inhabited : Inhabited (sem_row Σ) := 
    populate (@SemRow Σ ⊥ _).
  Next Obligation. rewrite /sem_row /=. iIntros (??) "[] /=". Qed.

  Global Instance sem_row_car_ne n : Proper (dist n ==> dist n) sem_row_car.
  Proof. by intros Ψ1 Ψ2 ?. Qed.
  Global Instance sem_row_car_proper : Proper ((≡) ==> (≡)) (@sem_row_car Σ).
  Proof. by intros Ψ1 Ψ2 ?. Qed.

  Global Instance sem_row_ne n Ψ : Proper ((λ _ _, True) ==> dist n) (@SemRow Σ Ψ).
  Proof. intros P1 P2 _ ?. apply non_dep_fun_dist. rewrite /sem_row_car //. Qed.
  Global Instance sem_row_proper Ψ : Proper ((λ _ _, True) ==> (≡)) (@SemRow Σ Ψ).
  Proof. intros P1 P2 _ ?. apply non_dep_fun_equiv. rewrite /sem_row_car //. Qed.

End sem_row_cofe.

Declare Scope sem_row_scope.
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

Definition sig_le {Σ} (σ σ' : sem_sig Σ) := tc_opaque (iEff_le σ σ')%I.
Global Instance sig_le_persistent {Σ} σ σ' :
  Persistent (@sig_le Σ σ σ').
Proof.
  unfold sig_le, tc_opaque. apply _.
Qed.

Definition row_le {Σ} (ρ ρ' : sem_row Σ) := tc_opaque (iEff_le ρ ρ')%I.

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
