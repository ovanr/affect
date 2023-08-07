
(* sem_types.v *)

(* This file contains the definition of semantic types and row,
   together with the definition of base types and type formers.  
*)

From iris.proofmode Require Import base tactics.
From iris.algebra Require Import ofe.
From iris.base_logic.lib Require Import iprop.
From iris.base_logic Require Import upred.

(* Hazel Reasoning *)
From program_logic Require Import weakest_precondition 
                                  state_reasoning.

(* Local imports *)
From affine_tes.lang Require Import hazel.
From affine_tes.logic Require Import iEff.


(** * Semantic Types. *)

(* We equip sem_ty with the OFE structure val -d> iPropI
 * which is the OFE of non-dependently-typed functions over a discrete domain *)
Definition sem_ty Σ := val -d> (iPropO Σ).

Declare Scope sem_ty_scope.
Bind Scope sem_ty_scope with sem_ty.
Delimit Scope sem_ty_scope with T.

(** * Semantic Row. *)

Notation sem_row Σ := (iEff Σ).

Declare Scope sem_row_scope.
Bind Scope ieff_scope with sem_row.
Delimit Scope sem_row_scope with R.

(* Base types. *)
Definition sem_ty_unit {Σ} : sem_ty Σ := (λ v, ⌜ v = #() ⌝)%I.
Definition sem_ty_bool {Σ} : sem_ty Σ := (λ v, ∃ b : bool, ⌜ v = #b ⌝)%I.
Definition sem_ty_int {Σ} : sem_ty Σ := (λ v, ∃ n : Z, ⌜ v = #n ⌝)%I.
Definition sem_ty_moved {Σ} : sem_ty Σ := (λ v, True)%I.

(* Reference Type *)
Definition sem_ty_ref `{!heapGS Σ} (τ : sem_ty Σ): sem_ty Σ := 
  (λ v, ∃ l : loc, ⌜ v = #l ⌝ ∗ (∃ w, l ↦ w ∗ τ w))%I.

(* Product type. *)
Definition sem_ty_prod {Σ} (τ κ : sem_ty Σ) : sem_ty Σ := 
  (λ v, ∃ v₁ v₂, ⌜v = (v₁, v₂)%V⌝ ∗ τ v₁ ∗ κ v₂)%I.

(* Sum type. *)
Definition sem_ty_sum {Σ} (τ κ : sem_ty Σ) : sem_ty Σ := 
  (λ v, ∃ v', (⌜v = InjLV v'%V⌝ ∗ τ v') ∨ (⌜ v = InjRV v'⌝ ∗ κ v'))%I.

(* Linear Arrow type. *)
Definition sem_ty_larr `{!heapGS Σ} 
  (ρ : sem_row Σ)
  (τ : sem_ty Σ)
  (κ : sem_ty Σ) : sem_ty Σ :=
  (λ (v : val), ∀ Φ (w : val), τ w -∗ (∀ v, κ v -∗ Φ v) -∗ EWP (v w) <| ρ |> {{ Φ }})%I.

(* Unrestricted Arrow type. *)
Definition sem_ty_uarr `{irisGS eff_lang Σ} 
  (ρ : sem_row Σ)
  (τ : sem_ty Σ)
  (κ : sem_ty Σ) : sem_ty Σ :=
  (λ (v : val), ∀ Φ (w : val), □ (τ w -∗ (∀ v, κ v -∗ Φ v) -∗ EWP (v w) <| ρ |> {{ Φ }}))%I.

(* Polymorphic type. *)
Definition sem_ty_forall `{irisGS eff_lang Σ} 
  (ρ : sem_row Σ) (C : sem_ty Σ → sem_ty Σ) : sem_ty Σ := 
    (λ v, ∀ τ, EWP (v <_>) <| ρ |> {{ C τ }})%I.

(* Existential type. *)
Definition sem_ty_exists `{irisGS eff_lang Σ} 
  (C : sem_ty Σ → sem_ty Σ) : sem_ty Σ := (λ v, ∃ τ, C τ v)%I.

(** Recursive types *)
Definition sem_ty_rec_pre {Σ} (C : sem_ty Σ → sem_ty Σ)
  (rec : sem_ty Σ) : sem_ty Σ := (λ v, ▷ (∃ rec', rec ≡ rec' ∧ C rec' v))%I.
Global Instance sem_ty_rec_pre_contractive {Σ} (C : sem_ty Σ → sem_ty Σ) :
  Contractive (sem_ty_rec_pre C).
Proof. solve_contractive. Qed.
Definition sem_ty_rec {Σ} (C : sem_ty Σ → sem_ty Σ) : sem_ty Σ :=
  fixpoint (sem_ty_rec_pre C).

Lemma sem_ty_equiv {Σ} v (τ τ' : sem_ty Σ) : 
  τ ≡ τ' → τ v ≡ τ' v.
Proof.
  intros Hτ. unfold equiv, ofe_equiv in Hτ. 
  simpl in Hτ. unfold discrete_fun_equiv in Hτ.
  by apply Hτ.
Qed.

Lemma sem_ty_dist {Σ} v (τ τ' : sem_ty Σ) n : 
  dist n τ τ' → dist n (τ v) (τ' v).
Proof.
  intros Hττ'. unfold dist, ofe_dist in Hττ'.
  simpl in Hττ'. unfold discrete_fun_dist in Hττ'.
  by apply Hττ'.
Qed.

Lemma sem_ty_rec_unfold {Σ} (C : sem_ty Σ → sem_ty Σ) `{!NonExpansive C} v :
  (sem_ty_rec C)%T v ⊣⊢ ▷ C (sem_ty_rec C)%T v.
Proof.
  rewrite {1}/sem_ty_rec.
  (*          
  ∙ f := sem_ty_rec_pre C : sem_ty → sem_ty
  ∙ fixpoint (sem_ty_rec_pre C) : sem_ty

  The equivalence we have from fixpoint_unfold is: 
    fixpoint f ≡ f (fixpoint f)

    Since fixpoint f : val -d> iProp, and
          f (fixpoint f) : val -d> iProp

  We want to get that given two sem_types are equivalent,
  if we apply them with the same value we get that 
  the result is also equivalent.

  So we want this equivalence:
    ∀ v, fixpoint f v ≡ f (fixpoint f) v

  But even though the equivalence instance for val -d> iProp
  is just that, Coq has trouble rewriting directly with fixpoint_unfold,
  because it is a function.
  As a result we fistly apply sem_ty_equiv lemma *)
  assert (fixpoint (sem_ty_rec_pre C) v ≡ sem_ty_rec_pre C (fixpoint (sem_ty_rec_pre C)) v).
  { apply sem_ty_equiv. apply fixpoint_unfold. }
  rewrite H. iSplit.
  - iIntros "(%rec' & #Hrec & HC) !>".
    set Ψ := λ τ, C τ v.
    assert (Ψ rec' = C rec' v) by done.
    assert (Ψ (sem_ty_rec C) = C (sem_ty_rec C) v) by done.
    rewrite <- H0. rewrite <- H1.
    iApply (internal_eq_rewrite rec' (sem_ty_rec C)).
    + intros n τ τ' Hττ'. unfold Ψ. apply sem_ty_dist. 
      by apply NonExpansive0.
    + by iApply internal_eq_sym.
    + iApply "HC".
  - iIntros "HC //=". iNext. iExists (sem_ty_rec C).
    by iFrame. 
Qed.

(* Empty Effect Row. *)
Definition sem_row_bot {Σ} : sem_row Σ := iEff_bottom.

(* Effect Row. *)
Definition sem_row_eff {Σ} (τ κ : sem_ty Σ) : sem_row Σ :=
  (>> (a : val) >> ! a {{ τ a }};
   << (b : val) << ? b {{ κ b }} @OS).

Lemma upcl_sem_row_eff {Σ} τ κ v Φ :
  iEff_car (upcl OS (sem_row_eff (Σ:=Σ) τ κ)) v Φ ⊣⊢
    (∃ a, ⌜ v = a ⌝ ∗ τ a ∗ (∀ b, κ b -∗ Φ b))%I.
Proof. by rewrite /sem_row_eff (upcl_tele' [tele _] [tele _]). Qed.

Lemma sem_row_eff_eq {Σ} τ κ v Φ :
  iEff_car (sem_row_eff (Σ:=Σ) τ κ) v Φ ⊣⊢
    (∃ a, ⌜ a = v ⌝ ∗ τ a ∗ (∀ b, κ b -∗ Φ b))%I.
Proof. by rewrite /sem_row_eff (iEff_tele_eq' [tele _] [tele _]). Qed.

(* Notations. *)
Notation "()" := sem_ty_unit : sem_ty_scope.
Notation "'𝔹'" := (sem_ty_bool) : sem_ty_scope.
Notation "'ℤ'" := (sem_ty_int) : sem_ty_scope.
Notation "'Moved'" := (sem_ty_moved) : sem_ty_scope.
Notation "τ '×' κ" := (sem_ty_prod τ%T κ%T)
  (at level 120, κ at level 200) : sem_ty_scope.
Infix "+" := (sem_ty_sum) : sem_ty_scope.

Notation "'Ref' τ" := (sem_ty_ref τ%T) 
  (at level 50) : sem_ty_scope.

Notation "'∀:' A , ρ , C " := (sem_ty_forall ρ (λ A, C%T)) 
  (at level 180) : sem_ty_scope.

Notation "'∃:' A , C " := (sem_ty_exists (λ A, C%T)) 
  (at level 180) : sem_ty_scope.

Notation "'μ:' A , C " := (sem_ty_rec (λ A, C%T)) 
  (at level 180) : sem_ty_scope.

Notation "⟨⟩" := sem_row_bot : sem_row_scope.
Notation "τ ⇒ κ" := (sem_row_eff τ%T κ%T) 
  (at level 100, κ at level 200) : sem_row_scope.

Notation "τ '-{' ρ '}-∘' κ" := (sem_ty_larr ρ%R τ%T κ%T)
  (at level 100, ρ, κ at level 200) : sem_ty_scope.
Notation "τ ⊸ κ" := (sem_ty_larr sem_row_bot τ%T κ%T)
  (at level 99, κ at level 200) : sem_ty_scope.

Notation "τ '-{' ρ '}->' κ" := (sem_ty_uarr ρ%R τ%T κ%T)
  (at level 100, ρ, κ at level 200) : sem_ty_scope.
Notation "τ → κ" := (sem_ty_uarr sem_row_bot τ%T κ%T)
  (at level 99, κ at level 200) : sem_ty_scope.


(* Derived Types *)

Definition ListF {Σ} (τ : sem_ty Σ) := λ α, (() + (τ × α))%T.

(* List type. *)
Definition sem_ty_list {Σ} (τ : sem_ty Σ) : sem_ty Σ := 
    sem_ty_rec (ListF τ).

Notation "'List' τ" := (sem_ty_list τ%T) 
  (at level 50) : sem_ty_scope.


(**  Prove that type formers are non-expansive and respect setoid equality. *)
Section types_properties.
  Context `{!heapGS Σ}.

  Ltac solve_non_expansive2 :=
    intros m x y Hxy x' y' Hxy'; try intros ?;
    unfold sem_ty_unit, sem_ty_int, sem_ty_bool,
           sem_ty_prod, sem_ty_sum, sem_ty_larr,
           sem_ty_uarr, sem_ty_ref, sem_ty_rec,
           sem_ty_list, sem_ty_forall, sem_ty_exists;
    repeat f_equiv; done || by apply sem_ty_dist.

  Global Instance sem_ty_prod_ne : NonExpansive2 (@sem_ty_prod Σ).
  Proof. solve_non_expansive2. Qed.

  Global Instance sem_ty_sum_ne : NonExpansive2 (@sem_ty_sum Σ).
  Proof. solve_non_expansive2. Qed.

  Global Instance sem_ty_larr_ne ρ : NonExpansive2 (sem_ty_larr ρ).
  Proof. solve_non_expansive2. Qed.

  Global Instance sem_ty_uarr_ne ρ : NonExpansive2 (sem_ty_uarr ρ).
  Proof. solve_non_expansive2. Qed.

  Global Instance sem_ty_ref_ne : NonExpansive2 (@sem_ty_ref Σ _).
  Proof. solve_non_expansive2. Qed.

  Global Instance sem_ty_forall_ne n ρ :
    Proper (pointwise_relation _ (dist n) ==> dist n) (sem_ty_forall ρ).
  Proof. intros ????. unfold sem_ty_forall; repeat f_equiv. Qed.

  Global Instance sem_ty_exist_ne n :
    Proper (pointwise_relation _ (dist n) ==> dist n) sem_ty_exists.
  Proof. intros ????. unfold sem_ty_exists; repeat f_equiv. 
         unfold pointwise_relation in H. by apply sem_ty_dist. Qed.

  Global Instance sem_ty_rec_ne n :
    Proper (pointwise_relation _ (dist n) ==> dist n) (@sem_ty_rec Σ).
  Proof.
    intros C1 C2 HA. unfold sem_ty_rec. apply fixpoint_ne.
    intros ??. unfold sem_ty_rec_pre. do 4 f_equiv. 
    by apply sem_ty_dist.
  Qed.

  Global Instance sem_ty_listF_ne τ : NonExpansive (@ListF Σ τ).
  Proof. intros ????. unfold ListF; by repeat f_equiv. Qed.

  Global Instance sem_ty_prod_proper : Proper ((≡) ==> (≡) ==> (≡)) (@sem_ty_prod Σ).
  Proof. solve_non_expansive2. Qed.

  Global Instance sem_ty_sum_proper : Proper ((≡) ==> (≡) ==> (≡)) (@sem_ty_sum Σ).
  Proof. solve_non_expansive2. Qed.

  Global Instance sem_ty_larr_proper ρ : Proper ((≡) ==> (≡) ==> (≡)) (sem_ty_larr ρ).
  Proof. solve_non_expansive2. Qed.

  Global Instance sem_ty_uarr_proper ρ : Proper ((≡) ==> (≡) ==> (≡)) (sem_ty_uarr ρ).
  Proof. solve_non_expansive2. Qed.

  Global Instance sem_ty_ref_proper : Proper ((≡) ==> (≡)) (@sem_ty_ref Σ _).
  Proof. intros ????. unfold sem_ty_ref; by repeat f_equiv. Qed.

  Global Instance sem_ty_forall_proper ρ:
    Proper (pointwise_relation _ (≡) ==> (≡)) (sem_ty_forall ρ).
  Proof. intros ????; unfold sem_ty_forall; repeat f_equiv. Qed.

  Global Instance sem_ty_exist_proper :
    Proper (pointwise_relation _ (≡) ==>(≡)) sem_ty_exists.
  Proof. 
    intros ????. unfold sem_ty_exists; repeat f_equiv.
    by apply sem_ty_equiv.
  Qed.

  Global Instance sem_ty_rec_proper :
    Proper (pointwise_relation _ (≡) ==>(≡)) (@sem_ty_rec Σ).
  Proof.
    intros C1 C2 HA. apply equiv_dist=> n.
    apply sem_ty_rec_ne=> A. by apply equiv_dist.
  Qed.

End types_properties.
