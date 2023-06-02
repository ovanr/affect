(* interp.v *)

(* This file contains the definition of the interpretation of types, of rows,
   and of typing judgments. Types are interpreted as _semantic types_, which
   are Iris's predicates, rows are interpreted as _semantic rows_,
   and typing judgments are
   interpreted as specifications written in terms of the extended weakest precondition
*)

From iris.proofmode Require Export base tactics classes.
From language Require Export eff_lang.

(** * Semantic Types. *)

Definition sem_ty Σ := val → iProp Σ.

Declare Scope sem_ty_scope.
Bind Scope sem_ty_scope with sem_ty.
Delimit Scope sem_ty_scope with sem_ty.

