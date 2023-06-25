
(* sem_types.v *)

(* This file contains the definition of semantic types and row,
   together with the definition of base types and type formers.  
*)

From iris.proofmode Require Import base tactics.
From iris.base_logic.lib Require Import iprop invariants.

(* Hazel Reasoning *)
From program_logic Require Import weakest_precondition 
                                  state_reasoning.

(* Local imports *)
From affine_tes.lang Require Import hazel.
From affine_tes.logic Require Import iEff.


(** * Semantic Types. *)

Definition sem_ty Σ := val → (iProp Σ).

Declare Scope sem_ty_scope.
Bind Scope sem_ty_scope with sem_ty.
Delimit Scope sem_ty_scope with T.

(** * Semantic Row. *)

Definition sem_row Σ := iEff Σ.

Declare Scope sem_row_scope.
Bind Scope ieff_scope with sem_row.
Delimit Scope sem_row_scope with R.

(* Base types. *)
Definition sem_ty_unit {Σ} : sem_ty Σ := (λ v, ⌜ v = #() ⌝)%I.
Definition sem_ty_bool {Σ} : sem_ty Σ := (λ v, ∃ b : bool, ⌜ v = #b ⌝)%I.
Definition sem_ty_int {Σ} : sem_ty Σ := (λ v, ∃ n : Z, ⌜ v = #n ⌝)%I.

(* Reference Type *)
Definition tyN := nroot .@ "ty".

Definition sem_ty_ref `{!heapGS Σ} (τ : sem_ty Σ): sem_ty Σ := 
  (λ v, ∃ l : loc, ⌜ v = #l ⌝ ∗ □ (∀ w, (τ w) -∗ □ (τ w)) ∗
                   inv (tyN .@ l) (∃ w, l ↦ w ∗ (τ w)))%I.

(* Product type. *)
Definition sem_ty_prod {Σ} (τ κ : sem_ty Σ) : sem_ty Σ := 
  (λ v, ∃ v₁ v₂, ⌜v = (v₁, v₂)%V⌝ ∗ τ v₁ ∗ κ v₂)%I.

(* Linear Arrow type. *)
Definition sem_ty_larr `{irisGS eff_lang Σ} 
  (τ : sem_ty Σ)
  (ρ : sem_row Σ)
  (κ : sem_ty Σ) : sem_ty Σ :=
  (λ (v : val), ∀ (w : val), τ w -∗ EWP (v w) <| ρ |> {{ κ }})%I.

(* Unrestricted Arrow type. *)
Definition sem_ty_uarr `{irisGS eff_lang Σ} 
  (τ : sem_ty Σ)
  (ρ : sem_row Σ)
  (κ : sem_ty Σ) : sem_ty Σ :=
  (λ (v : val), ∀ (w : val), □ (τ w -∗ EWP (v w) <| ρ |> {{ κ }}))%I.


(* Polymorphic type. *)
Definition sem_ty_forall `{irisGS eff_lang Σ} 
  (C : sem_ty Σ → sem_ty Σ) : sem_ty Σ := (λ v, ∀ τ, C τ v)%I.

Fixpoint is_of_list_type {Σ} (l : val) (τ : sem_ty Σ ) (xs : list val) : (iProp Σ) :=
  match xs with
    | [] => ⌜ l = NILV ⌝
    | x :: xxs => ∃ tl, ⌜ l = CONSV x tl ⌝ ∗ τ x ∗ is_of_list_type tl τ xxs
  end
.

(* List type. *)
Definition sem_ty_list {Σ} (τ : sem_ty Σ) : sem_ty Σ := 
  (λ v, ∃ xs, is_of_list_type v τ xs)%I.

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
Notation "τ '×' κ" := (sem_ty_prod τ%T κ%T)
  (at level 120, κ at level 200) : sem_ty_scope.

Notation "'Ref' τ" := (sem_ty_ref τ%T) 
  (at level 50) : sem_ty_scope.

Notation "∀ A1 .. An , C" :=
  (sem_ty_forall (λ A1, .. (sem_ty_forall (λ An, C%T)) ..)) : sem_ty_scope.


Notation "'List' τ" := (sem_ty_list τ%T) 
  (at level 50) : sem_ty_scope.

Notation "⟨⟩" := sem_row_bot : sem_row_scope.
Notation "τ ⇒ κ" := (sem_row_eff τ%T κ%T) 
  (at level 100, κ at level 200) : sem_row_scope.

Notation "τ '-{' ρ '}-∘' κ" := (sem_ty_larr τ%T ρ%R κ%T)
  (at level 100, ρ, κ at level 200) : sem_ty_scope.
Notation "τ ⊸ κ" := (sem_ty_larr τ%T sem_row_bot κ%T)
  (at level 99, κ at level 200) : sem_ty_scope.

Notation "τ '-{' ρ '}->' κ" := (sem_ty_uarr τ%T ρ%R κ%T)
  (at level 100, ρ, κ at level 200) : sem_ty_scope.
Notation "τ → κ" := (sem_ty_uarr τ%T sem_row_bot κ%T)
  (at level 99, κ at level 200) : sem_ty_scope.

