(* interp.v *)

(* This file contains the definition of the interpretation of types, of rows,
   and of typing judgments. Types are interpreted as _semantic types_, which
   are Iris's predicates, rows are interpreted as _semantic row_ which is an iEff protocol,
   and typing judgments are
   interpreted as specifications written in terms of the extended weakest precondition
*)

From iris.proofmode Require Import base tactics classes.
From iris.base_logic.lib Require Import iprop.
From iris.program_logic Require Import weakestpre.
From language Require Import eff_lang.
From program_logic Require Import protocols weakest_precondition.
From affine_tes Require Import hazel_ext.

(** * Semantic Types. *)

Definition sem_ty Σ := val → iProp Σ.

Declare Scope sem_ty_scope.
Bind Scope sem_ty_scope with sem_ty.
Delimit Scope sem_ty_scope with sem_ty.

(** * Semantic Row. *)

Definition sem_row Σ := iEff Σ.

Bind Scope ieff_scope with sem_row.

Section sem_type_formers.

  (* Base types. *)
  Definition sem_ty_unit {Σ} : sem_ty Σ := (λ v, ⌜ v = #() ⌝)%I.

  Definition sem_ty_bool {Σ} : sem_ty Σ := (λ v, ∃ b : bool, ⌜ v = #b ⌝)%I.

  Definition sem_ty_int {Σ} : sem_ty Σ := (λ v, ∃ n : Z, ⌜ v = #n ⌝)%I.

  (* Product type. *)
  Definition sem_ty_prod {Σ} (A1 A2 : sem_ty Σ) : sem_ty Σ := 
    (λ v, ∃ v1 v2, ⌜v = (v1, v2)%V⌝ ∧ A1 v1 ∧ A2 v2)%I.

  (* Empty Effect Row. *)
  Definition sem_row_null {Σ} : (sem_row Σ) := iEff_bottom.

  (* Effect Row. *)
  Definition sem_row_eff {Σ} (A B : sem_ty Σ) : (sem_row Σ) :=
    (>> (a : val) >> ! a {{ A a }};
     << (b : val) << ? b {{ B b }} @OS).

  (* Arrow type. *)
  Definition sem_ty_arr `{!irisGS eff_lang Σ}
    (A : sem_ty Σ)
    (R : sem_row Σ)
    (B : sem_ty Σ) :=
    (λ (v : val), ∀ (w : val), A w -∗ EWP (v w) <| R |> {{ B }})%I.

End sem_type_formers.

(* Notations. *)
Notation "()" := sem_ty_unit : sem_ty_scope.
Infix "*" := sem_ty_prod : sem_ty_scope.
Notation "A '-{' R '}->' B" := (sem_ty_arr A R B)
  (at level 100, R, B at level 200) : sem_ty_scope.

Notation "⟨⟩" := sem_row_null : ieff_scope.
Notation "A ⇒ B" := (sem_row_eff A B) 
  (at level 100, B at level 200) : ieff_scope.

Definition env_sem_typed Σ (Γ : gmap string (sem_ty Σ)) 
                         (vs : gmap string val) :=
  
  ([∗ map] i ↦ A;v ∈ Γ; vs, A v)%I.
  
(* Semantic typing judgment. *)
Definition sem_typed `{!irisGS eff_lang Σ}
  (Γ  : gmap string (sem_ty Σ))
  (e  : expr)
  (ρ  : sem_row Σ)
  (α  : sem_ty Σ) : iProp Σ :=
    (∀ (vs : gmap string val),
        env_sem_typed Σ Γ vs -∗
        EWP (subst_map vs e) <| ρ |> {{ α }})%I.

Notation "Γ '|=' e : ρ : α" := (sem_typed e ρ α)
  (at level 74, e, ρ, α at next level) : bi_scope.


