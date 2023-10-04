
From iris.proofmode Require Import base tactics classes.

Lemma non_dep_fun_equiv A B x (f f' : A -d> B) : 
  f ≡ f' → f x ≡ f' x.
Proof. intros H. f_equiv. Qed.

Lemma non_dep_fun_dist A B x (f f' : A -d> B) n : 
  f ≡{n}≡ f' → (f x)≡{n}≡(f' x).
Proof. intros H. f_equiv. Qed.

Lemma non_dep_fun_dist2 A B C x y (f f' : A -d> B -d> C) n : 
  f ≡{n}≡ f' → (f x y)≡{n}≡(f' x y).
Proof. intros H. f_equiv. Qed.

Lemma non_dep_fun_dist3 A B C D x y z (f f' : A -d> B -d> C -d> D) n : 
  f ≡{n}≡ f' → (f x y z)≡{n}≡(f' x y z).
Proof. intros H. apply non_dep_fun_dist. f_equiv. Qed.

Lemma non_dep_fun_dist4 A B C D E x y z z' (f f' : A -d> B -d> C -d> D -d> E) n : 
  f ≡{n}≡ f' → (f x y z z')≡{n}≡(f' x y z z').
Proof. intros H. apply non_dep_fun_dist3. f_equiv. Qed.

Lemma non_dep_fun_dist5 A B C D E F x y z z' z'' (f f' : A -d> B -d> C -d> D -d> E -d> F) n : 
  f ≡{n}≡ f' → (f x y z z' z'')≡{n}≡(f' x y z z' z'').
Proof. intros H. apply non_dep_fun_dist4. f_equiv. Qed.
