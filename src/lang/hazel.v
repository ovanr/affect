
(* Hazel language *)
From language Require Import eff_lang.
From program_logic Require Import protocols weakest_precondition tactics.

(* Local imports *)
From lang Require Import subst_map.


Definition pair_elim :=
  (λ: "x", λ: "f", "f" (Fst "x") (Snd "x"))%V.

Notation ELetPair x1 x2 e1 e2 :=
  (pair_elim e1 (Lam x1 (Lam x2 e2)))%E.

Notation "'let:' '(' x1 ',' x2 ')' := e1 'in' e2" := (ELetPair x1%binder x2%binder e1%E e2%E)
  (at level 200, x1, x2 at level 1, e1, e2 at level 200,
   format "'[' 'let:'  '(' x1 ',' x2 ')'  :=  '[' e1 ']'  'in'  '/' e2 ']'") : expr_scope.
