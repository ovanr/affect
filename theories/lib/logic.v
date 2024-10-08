
From iris.proofmode Require Import base tactics classes.
From iris.program_logic Require Import weakestpre.

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

Global Instance non_expansive2_from_1 {A B C : ofe} (f : B -n> A) :
  NonExpansive2 (λ (x : B) (_ : C), f x).
Proof.
  intros ???????. by f_equiv.
Qed.

Global Instance non_expansive2_from_1' {A B C : ofe} (f : C -n> A) :
  NonExpansive2 (λ (_ : B) (x : C), f x).
Proof.
  intros ???????. by f_equiv.
Qed.

Global Instance non_expansive2_from_constant {A B C : ofe} (c : A) :
  NonExpansive2 (λ (_ : B) (_ : C), c).
Proof.
  intros ???????. done.
Qed.

Lemma prod_equivI_1 {PROP : bi} `{!BiInternalEq PROP} {A B : ofe} (x y : A * B) : 
    (x ≡ y : PROP) ⊢ x.1 ≡ y.1.
Proof. rewrite prod_equivI. iIntros "[$ _]". Qed.

Lemma prod_equivI_2 {PROP : bi} `{!BiInternalEq PROP} {A B : ofe} (x y : A * B) : 
  (x ≡ y : PROP) ⊢ x.2 ≡ y.2.
Proof. rewrite prod_equivI. iIntros "[_ $]". Qed.

Lemma intuitionistically_if_mono_alt {PROP : bi} m (P Q : PROP) : 
  □ (P -∗ Q) -∗ □?m P -∗ □?m Q.
Proof.
  iIntros "#H". destruct m; simpl; last done.
  iIntros "#HP !#". by iApply "H".
Qed.

Lemma intuitionistically_if_forall {PROP : bi} {A : Type} (Φ : A → PROP) m : 
  □?m (∀ x : A, Φ x) ⊢ ∀ x : A, □?m Φ x.
Proof. destruct m; simpl; last done. iApply bi.intuitionistically_forall. Qed.

Lemma forall_intuitionistically {Σ} {A : Type} (Φ : A → iProp Σ) : 
  (∀ x : A, □ Φ x) ⊢ □ (∀ x : A, Φ x).
Proof. iIntros "#H !# %". iApply "H". Qed.

Lemma forall_intuitionistically_if {Σ} {A : Type} (Φ : A → iProp Σ) m : 
  (∀ x : A, □? m (Φ x)) ⊢ □? m (∀ x : A, Φ x).
Proof. destruct m; simpl; last done. iApply forall_intuitionistically. Qed.
