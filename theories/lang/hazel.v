(* hazel.v *)

(* This file imports the Hazel language from coq-hazel
   and additionally defines some extensions to it such as
   the let-pair construct and its eliminator.
*)

From iris.program_logic Require Export language.
From iris.heap_lang     Require Export locations.

(* Hazel language *)
From language Require Export eff_lang.

(* Local imports *)
From affine_tes.lang Require Export subst_map.

Definition pair_elim :=
  (λ: "x", λ: "f", "f" (Fst "x") (Snd "x"))%V.

Notation ELetPair x1 x2 e1 e2 :=
  (pair_elim e1 (Lam x1 (Lam x2 e2)))%E.

Notation "'let:' '(' x1 ',' x2 ')' := e1 'in' e2" := (ELetPair x1%binder x2%binder e1%E e2%E)
  (at level 200, x1, x2 at level 1, e1, e2 at level 200,
   format "'[' 'let:'  '(' x1 ',' x2 ')'  :=  '[' e1 ']'  'in'  '/' e2 ']'") : expr_scope.

Global Instance load_atomic (l : loc) :
  Atomic StronglyAtomic (Load $ Val $ LitV $ LitLoc l).
Proof.
  intros ?. simpl. intros ?????. unfold prim_step' in H.
  destruct κ; [|done].
  destruct efs; [|done]. inversion H. simplify_eq.
  destruct k as [|Ki K]; try destruct Ki; try naive_solver.
  - simpl in H0. simpl. simplify_eq. inversion H2. by exists v.
  - simpl in H0. simpl. simplify_eq.
    destruct K as [|Ki K]; try destruct Ki; try naive_solver.
    simpl in H0. simplify_eq. by inversion H2.
Qed.

Global Instance store_atomic (l : loc) (w : val) :
  Atomic StronglyAtomic (Store (Val $ LitV $ LitLoc l) (Val w)).
Proof.
 intros ?. simpl. intros ?????. unfold prim_step' in H.
 destruct κ; [|done].
 destruct efs; [|done]. inversion H. simplify_eq.
 destruct k as [|Ki K]; try destruct Ki; try naive_solver.
 - simpl in H0. simpl. simplify_eq. inversion H2.
   by exists (LitV $ LitUnit).
 - simpl in H0. simpl. simplify_eq.
   destruct K as [|Ki K]; try destruct Ki; try naive_solver.
   simpl in H0. simplify_eq. by inversion H2.
 - simpl in H0. simpl. simplify_eq.
   destruct K as [|Ki K]; try destruct Ki; try naive_solver.
   simpl in H1. simplify_eq. by inversion H2.
Qed.

