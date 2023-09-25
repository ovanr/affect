
From stdpp Require Import base gmap.
From Coq Require Import String.

From language Require Export eff_lang.

Global Instance elem_binder_string : (ElemOf binder (list string)) | 10 := 
  (λ b xs, match b with
              BAnon => False%type
            | BNamed x => x ∈ xs
           end).

Definition cons_maybe {A} (x : binder * A) (xs : list (string * A)) : list (string * A) :=
  match x with
    (BAnon, _) => xs
  | (BNamed x', a) => (x',a) :: xs
  end.
Infix "::?" := cons_maybe (at level 60, right associativity) : list_scope.

Lemma binder_delete_union {A} x (vs ws : gmap string A) :
  binder_delete x (vs ∪ ws) = binder_delete x vs ∪ binder_delete x ws.
Proof. destruct x; first done; simpl. apply delete_union. Qed.

Global Instance delete_gmap_multiple K A `{ Countable K, EqDecision K, Delete K (gmap K A) } : 
  Delete (list K) (gmap K A) :=
  (fix delete_mult xs vs :=
      match xs with
        [] => vs
      | x :: xxs => delete x (delete_mult xxs vs)
      end).

Lemma delete_list_nil {A} (vs : gmap string A) :
  delete [] vs = vs.
Proof. done. Qed.

Lemma delete_list_cons {A} x (xs : list string) (vs : gmap string A) :
  delete (x :: xs) vs = delete x (delete xs vs).
Proof. done. Qed.

Lemma delete_list_delete {A} x (vs : gmap string A) :
  delete [x] vs = delete x vs.
Proof. done. Qed.

Lemma delete_list_empty {A} (xs : list string) :
  delete xs ∅ = (∅ : gmap string A).
Proof.
  induction xs; first done. 
  by rewrite delete_list_cons IHxs delete_empty.
Qed.

Lemma delete_list_commute {A}
  (x : string) (xs : list string) (vs : gmap string A) :
  delete x (delete xs vs) = delete xs (delete x vs).
Proof.
  induction xs; first done.
  assert (Hrw : ∀ (vs : gmap string A), delete (a :: xs) vs = delete a (delete xs vs)) by (by intros ?).
  rewrite !Hrw.
  by rewrite delete_commute IHxs.
Qed.

Lemma delete_list_singleton {A} (z : string) (xs : list string) (m : A) :
  z ∈ xs → delete xs {[z:=m]} = (∅ : gmap string A).
Proof.
  intros ?. induction xs; simpl; [inversion H|].
  set g := {[z := m]}.
  rewrite delete_list_cons.
  destruct (decide (z = a)).
  - subst. by rewrite delete_list_commute delete_singleton delete_list_empty. 
  - rewrite IHxs; first (apply delete_empty). 
    destruct (elem_of_cons xs z a) as [H' _].
    by edestruct H'.
Qed.
  
Lemma delete_list_singleton_ne {A} (z : string) (xs : list string) (m : A) :
  z ∉ xs → delete xs {[z:=m]} = ({[z:=m]} : gmap string A).
Proof.
  intros ?. induction xs; first done.
  destruct (not_elem_of_cons xs z a) as [[] _]; first done. 
  rewrite delete_list_cons IHxs; last done. 
  rewrite delete_insert_ne; last congruence. 
  by rewrite delete_empty insert_empty.
Qed.

Lemma lookup_difference_delete {A} z (vs ws : gmap string A) :
  (vs ∖ delete z ws) !! z = vs !! z.
Proof.
  destruct (vs !! z) eqn:H.
  - rewrite (difference_delete _ _ _ a); last done.
    by rewrite lookup_insert.
  - apply lookup_difference_None; auto.
Qed.

Lemma lookup_difference_delete_ne {A} i j (vs ws : gmap string A) :
  i ≠ j → (vs ∖ ws) !! j = (vs ∖ delete i ws) !! j.
Proof.
  intros H. destruct (ws !! j) eqn:H'.
  - destruct (lookup_difference_None vs ws j) as [_ ->]; last auto. 
    destruct (lookup_difference_None vs (delete i ws) j) as [_ ->]; first done.
    right. rewrite lookup_delete_ne; auto.
  - destruct (vs !! j) eqn:?.
    { destruct (lookup_difference_Some vs ws j a) as [_ ->]; auto.
      destruct (lookup_difference_Some vs (delete i ws) j a) as [_ ->]; first done.
      split; first done. rewrite lookup_delete_ne; auto. }
    destruct (lookup_difference_None vs ws j) as [_ ->]; auto.
    destruct (lookup_difference_None vs (delete i ws) j) as [_ ->]; auto.
Qed.

Lemma delete_list_delete_cons {A} (z : string) (xs : list string) (vs : gmap string A) :
  z ∈ xs → delete xs vs = delete (z :: xs) vs.
Proof.
  intros H. induction xs; [inversion H|].
  rewrite !delete_list_cons.
  destruct (elem_of_cons xs z a) as [[] _]; first done.
  - subst. by rewrite delete_idemp.
  - rewrite delete_commute. rewrite delete_list_cons in IHxs.
    by rewrite -IHxs.
Qed.

Lemma delete_list_elem_of (Γ : list string) x (vs : gmap string val) :
  x ∈ Γ → delete Γ vs = delete x (delete Γ vs).
Proof.
  intros Helem. induction Γ.
  { by destruct (not_elem_of_nil x). }
  destruct (decide (a = x)); first subst. 
  { by rewrite delete_idemp. }
  rewrite delete_commute -IHΓ; first done.
  by destruct (elem_of_cons Γ x a) as [[] _].
Qed.

Lemma lookup_delete_not_elem {A} (ys : list string) x (vs : gmap string A) : 
  x ∉ ys → delete ys vs !! x = vs !! x.
Proof.
  intros ?.
  induction ys; first done.
  rewrite delete_list_cons.
  edestruct (not_elem_of_cons ys) as [[] _]; first done.
  rewrite lookup_delete_ne; last done.
  by apply IHys. 
Qed.

Lemma lookup_union_delete_disjoint {A} (xs : list string) x (vs ws : gmap string A) :
  x ∉ xs → (vs ∪ ws ∖ delete xs ws) !! x = vs !! x.
Proof.
  intros ?.
  induction xs.
  { by rewrite delete_list_nil map_difference_diag map_union_empty. }
  edestruct (not_elem_of_cons xs) as [[] _]; first done. 
  rewrite delete_list_cons. 
  specialize (IHxs H1).
  destruct (vs !! x) eqn:H'.
  { by rewrite lookup_union_l. }
  apply lookup_union_None; split; first done.
  rewrite -lookup_difference_delete_ne; last done.
  erewrite lookup_union_None in IHxs. tauto.
Qed.

Lemma subset_cons_elem {A} (x : A) xs ys : 
  x :: xs ⊆ ys → x ∈ ys.
Proof.
  intros ?.
  destruct (elem_of_subseteq (x :: xs) ys) as [H' _].
  apply H'; first done. rewrite elem_of_cons; by left. 
Qed.

Lemma subset_cons {A} (x : A) xs ys : 
  x :: xs ⊆ ys → xs ⊆ ys.
Proof.
  intros Hseq. 
  apply (elem_of_subseteq xs ys). intros z Hz.
  apply (elem_of_subseteq (x :: xs) ys); first done.
  apply elem_of_cons. by right.
Qed.

Lemma disjoint_cons_not_elem {A} (x : A) xs ys : 
  x :: xs ## ys → x ∉ ys.
Proof.
  intros ?.
  destruct (elem_of_disjoint (x :: xs) ys) as [H' _].
  intros ?. eapply H'; try done. 
  rewrite elem_of_cons; by left. 
Qed.

Lemma disjoint_cons {A} (x : A) xs ys : 
  x :: xs ## ys → xs ## ys.
Proof.
  intros Hseq. 
  apply (elem_of_disjoint xs ys). intros z Hz.
  apply (elem_of_disjoint (x :: xs) ys); first done.
  apply elem_of_cons. by right.
Qed.
