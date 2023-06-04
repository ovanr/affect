(* subst_map.v *)

(* This file contains the definition of `subst_map`,
   which substituted multiple values to an expression all at once.
   Proofs related to `subst_map` and `subst` are also provided.
*)

(* Hazel language *)
From language Require Import eff_lang.

Fixpoint subst_map (vs : gmap string val) (e : expr) : expr :=
  match e with
  | Val _ =>
      e
  | Var y =>
      if vs !! y is Some v then Val v else Var y
  | Do m e =>
      Do m (subst_map vs e)
  | Eff _ _ _  => e
  | TryWith e1 e2 e3 =>
      TryWith (subst_map vs e1) (subst_map vs e2) (subst_map vs e3)
  | Rec f y e =>
      Rec f y $ subst_map (binder_delete y (binder_delete f vs)) e
  | App e1 e2 =>
      App (subst_map vs e1) (subst_map vs e2)
  | UnOp op e =>
      UnOp op (subst_map vs e)
  | BinOp op e1 e2 =>
      BinOp op (subst_map vs e1) (subst_map vs e2)
  | If e0 e1 e2 =>
      If (subst_map vs e0) (subst_map vs e1) (subst_map vs e2)
  | Pair e1 e2 =>
      Pair (subst_map vs e1) (subst_map vs e2)
  | Fst e =>
      Fst (subst_map vs e)
  | Snd e =>
      Snd (subst_map vs e)
  | InjL e =>
      InjL (subst_map vs e)
  | InjR e =>
      InjR (subst_map vs e)
  | Case e0 e1 e2 =>
      Case (subst_map vs e0) (subst_map vs e1) (subst_map vs e2)
  | Alloc e =>
      Alloc (subst_map vs e)
  | Load e =>
      Load (subst_map vs e)
  | Store e1 e2 =>
      Store (subst_map vs e1) (subst_map vs e2)
  end
.

Lemma subst_map_empty e : subst_map ∅ e = e.
Proof.
  assert (∀ x, binder_delete x (∅:gmap _ val) = ∅) as Hdel.
  { intros [|x]; by rewrite /= ?delete_empty. }
  induction e; simplify_map_eq; rewrite ?Hdel; auto with f_equal.
Qed.

Lemma subst_map_insert x v vs e :
  subst_map (<[x:=v]>vs) e = subst x v (subst_map (delete x vs) e).
Proof.
  revert vs. induction e => vs; simplify_map_eq; auto with f_equal.
  - destruct (decide (x = x0)).
    { by simplify_map_eq. }
    simplify_map_eq.
    destruct (vs !! x0) eqn:H; first done.
    by simplify_option_eq.
  - destruct (decide _) as [[??]|[<-%dec_stable|[<-%dec_stable ?]]%not_and_l_alt].
    + rewrite !binder_delete_delete !binder_delete_insert; try done. 
      by rewrite IHe.
    + by rewrite /= delete_insert_delete delete_idemp.
    + by rewrite /= binder_delete_insert // delete_insert_delete
        !binder_delete_delete delete_idemp.
Qed.

Lemma subst_map_delete_subst x v vs e :
  subst_map (delete x vs) (subst x v e) = subst x v (subst_map (delete x vs) e).
Proof.
  revert vs. induction e=> vs; simplify_map_eq; auto with f_equal.
  - case (decide (x = x0)) as [?|?]; simplify_map_eq=> //.
    simplify_map_eq.
    destruct (vs !! x0) eqn:H; first done.
    by simplify_option_eq.
  - destruct (decide _) as [[??]|[<-%dec_stable|[<-%dec_stable ?]]%not_and_l_alt]; try done.
    by rewrite !binder_delete_delete; eauto with f_equal.
Qed.

Lemma subst_map_singleton x v e :
  subst_map {[x:=v]} e = subst x v e.
Proof. by rewrite subst_map_insert delete_empty subst_map_empty. Qed.
