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

Notation ELetPair x1 x2 e1 e2 := (pair_elim e1 (Lam x1 (Lam x2 e2)))%E.

Notation "'let:' '(' x1 ',' x2 ')' := e1 'in' e2" := (ELetPair x1%binder x2%binder e1%E e2%E)
  (at level 200, x1, x2 at level 1, e1, e2 at level 200,
   format "'[' 'let:'  '(' x1 ',' x2 ')'  :=  '[' e1 ']'  'in'  '/' e2 ']'") : expr_scope.

(** Notations for lists. *)
Notation NIL := (InjL #()) (only parsing).
Notation NILV := (InjLV #()) (only parsing).
Notation CONS x xs := (InjR (Pair x xs)) (only parsing).
Notation CONSV x xs := (InjRV (PairV x xs)) (only parsing).

Notation ListMatch e1 e2 x e3 := 
  (Case e1 (Lam BAnon e2) (Lam (BNamed x) (App (App e3 (Fst (Var x))) (Snd (Var x))))) (only parsing).

Notation "'list-match:' e1 'with' 'CONS' x => xs => e3 | 'NIL' => e2 'end'" :=
  (ListMatch e1 e2 x%binder (Lam x%binder (Lam xs%binder e3)))
  (e1, x, xs, e2, e1 at level 200,
   format "'[hv' 'list-match:'  e1  'with'  '/  ' '[' 'CONS'  x  =>  xs  =>  '/  ' e3 ']'  '/' '[' |  'NIL'  =>  '/  ' e2 ']'  '/' 'end' ']'") : expr_scope.

(* Notations for type abstraction and application *) 
Notation "Λ: e" := (λ: <>, e)%E (at level 200, only parsing) : expr_scope.
Notation "Λ: e" := (λ: <>, e)%V (at level 200, only parsing) : val_scope.
Notation "e '<_>'" := (App e%E #()) (at level 10, only parsing) : expr_scope.

(* Existential type packing and unpacking functions *)
(* Since hazel is an untyped language there is no notion of packing a type 
 * into an existential type nor unpacking an existential type.
 * Instead we define pack/unpack as just the identity and application respectively
 * to simply get a syntactic distinction for when existential pack/unpacking is applied *)
Definition exist_pack : val := (λ: "x", "x")%V.
Definition exist_unpack : val := (λ: "x" "y", "x" "y")%V.

(* Notation for pack and unpack *)
Notation "'pack:' e" := (exist_pack e%E)
  (at level 200, e at level 200,
   format "'[' 'pack:'  e ']'") : expr_scope.

Notation "'unpack:' x := e1 'in' e2" := (exist_unpack (Lam x%binder e2%E) e1%E)
  (at level 200, x at level 1, e1, e2 at level 200,
   format "'[' 'unpack:'  x  :=  '[' e1 ']'  'in'  '/' e2 ']'") : expr_scope.
Notation "'unpack:' x := e1 'in' e2" := (exist_unpack (LamV x%binder e2%E) e1%E)
  (at level 200, x at level 1, e1, e2 at level 200,
   format "'[' 'unpack:'  x  :=  '[' e1 ']'  'in'  '/' e2 ']'") : val_scope.

(* Folding and unfolding recursive types *)
(* Similarly as hazel is untyped we introduce the fold/unfold functions
 * as being the identity functions.
 * This gives us a syntactic distinction for when fold/unfold can be applied
 * which is necessary to trigger a step in the operational semantics and thus
 * remove the ▷ later modality in the recursive type definition. *)
Definition rec_fold : val := (λ: "x", "x")%V.
Definition rec_unfold : val := (λ: "x", "x")%V.

(* Notations for fold and unfold *)
Notation "'fold:' e" := (rec_fold e%E)
  (at level 200, e at level 200,
   format "'[' 'fold:'  e ']'") : expr_scope.

Notation "'unfold:' e" := (rec_unfold e%E)
  (at level 200, e at level 200,
   format "'[' 'unfold:'  e ']'") : expr_scope.


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
