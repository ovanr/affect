
(* sem_types.v *)

(* This file contains the definition of semantic types and signatures,
   together with the definition of base types and type formers.  
*)

From iris.proofmode Require Import base tactics.
From iris.algebra Require Import ofe list.
From iris.base_logic Require Export iprop upred invariants.

(* Hazel Reasoning *)
From hazel.program_logic Require Import weakest_precondition 
                                        state_reasoning
                                        protocols.

(* Local imports *)
From haffel.lib Require Import logic.
From haffel.lang Require Import hazel.
From haffel.lang Require Import subst_map.
From haffel.logic Require Import iEff.
From haffel.logic Require Import sem_def.

(* Base types. *)
Definition sem_ty_void {Σ} : sem_ty Σ := (λ v, False)%I.
Definition sem_ty_unit {Σ} : sem_ty Σ := (λ v, ⌜ v = #() ⌝)%I.
Definition sem_ty_bool {Σ} : sem_ty Σ := (λ v, ∃ b : bool, ⌜ v = #b ⌝)%I.
Definition sem_ty_int {Σ} : sem_ty Σ := (λ v, ∃ n : Z, ⌜ v = #n ⌝)%I.
Definition sem_ty_moved {Σ} : sem_ty Σ := (λ v, True)%I.

Definition sem_ty_cpy `{heapGS Σ} (τ : sem_ty Σ) : sem_ty Σ := (λ v, □ τ v)%I.

(* Copyable Reference Type *)
Definition tyN := nroot .@ "ty".
Definition sem_ty_ref_cpy `{heapGS Σ} (τ : sem_ty Σ): sem_ty Σ := 
  (λ v, ∃ l : loc, ⌜ v = #l ⌝ ∗ inv (tyN .@ l) (∃ w, l ↦ w ∗ τ w))%I.

(* Substructural Reference Type *)
Definition sem_ty_ref `{!heapGS Σ} (τ : sem_ty Σ): sem_ty Σ := 
  (λ v, ∃ l : loc, ⌜ v = #l ⌝ ∗ (∃ w, l ↦ w ∗ τ w))%I.

(* Product type. *)
Definition sem_ty_prod {Σ} (τ κ : sem_ty Σ) : sem_ty Σ := 
  (λ v, ∃ v₁ v₂, ⌜v = (v₁, v₂)%V⌝ ∗ τ v₁ ∗ κ v₂)%I.

(* Sum type. *)
Definition sem_ty_sum {Σ} (τ κ : sem_ty Σ) : sem_ty Σ :=
  (λ v, ∃ v', (⌜v = InjLV v'%V⌝ ∗ τ v') ∨ (⌜ v = InjRV v'⌝ ∗ κ v'))%I.

(* Affine Arrow type. *)
Definition sem_ty_aarr `{irisGS eff_lang Σ}
  (ρs : sem_sigs Σ)
  (τ : sem_ty Σ)
  (κ : sem_ty Σ) : sem_ty Σ :=
  (λ (v : val),
    ∀ (w : val),
      τ w -∗
      EWP (v w) <| fst ρs |> {| snd ρs |} {{ u, κ u }})%I.

(* Unrestricted Arrow type. *)
Definition sem_ty_uarr `{irisGS eff_lang Σ} 
  (ρs : sem_sigs Σ)
  (τ : sem_ty Σ)
  (κ : sem_ty Σ) : sem_ty Σ :=
  (λ (v : val), □ (
    ∀ (w : val),
      τ w -∗ 
      EWP (v w) <| fst ρs |> {| snd ρs |} {{ u, κ u }}))%I.

(* Polymorphic type. *)
Definition sem_ty_forall `{irisGS eff_lang Σ} 
  (ρs : sem_sigs Σ) (C : sem_ty Σ → sem_ty Σ) : sem_ty Σ := 
    (λ v, ∀ τ, □ EWP (v <_>) <| fst ρs |> {| snd ρs |} {{ C τ }})%I.

(* Polymorphic effect type. *)
(* why is value restriction also important here? *)
(* example: ∀ θ, ∀ τ, (τ -{ θ }-> ()) -{ θ }-> () *)
Definition sem_ty_sig_forall `{irisGS eff_lang Σ} 
  (τ : sem_sigs Σ → sem_ty Σ) : sem_ty Σ := 
    (λ v, ∀ θ, □ EWP (v <_>) {{ τ θ }})%I.

(* Existential type. *)
Definition sem_ty_exists `{irisGS eff_lang Σ} 
  (C : sem_ty Σ → sem_ty Σ) : sem_ty Σ := (λ v, ∃ τ, C τ v)%I.

(** Recursive types *)
Definition sem_ty_rec_pre {Σ} (C : sem_ty Σ → sem_ty Σ)
  (rec : sem_ty Σ) : sem_ty Σ := (λ v, ▷ (∃ rec', rec ≡ rec' ∧ C rec' v))%I.
Global Instance sem_ty_rec_pre_contractive {Σ} (C : sem_ty Σ → sem_ty Σ) :
  Contractive (sem_ty_rec_pre C).
Proof. solve_contractive. Qed.
Definition sem_ty_rec {Σ} (C : sem_ty Σ -d> sem_ty Σ) : sem_ty Σ :=
  fixpoint (sem_ty_rec_pre C).


Lemma sem_ty_rec_unfold {Σ} (C : sem_ty Σ → sem_ty Σ) `{!NonExpansive C} v :
  (sem_ty_rec C)%T v ⊣⊢ ▷ C (sem_ty_rec C)%T v. 
Proof.
  rewrite {1}/sem_ty_rec.
  assert (fixpoint (sem_ty_rec_pre C) v ≡ sem_ty_rec_pre C (fixpoint (sem_ty_rec_pre C)) v).
  { apply non_dep_fun_equiv. apply fixpoint_unfold. }
  rewrite H. iSplit.
  - iIntros "(%rec' & #Hrec & HC) !>".
      rewrite /sem_ty_rec.
      iAssert (C rec' ≡ C (fixpoint (sem_ty_rec_pre C)))%I as "#H".
      { by iRewrite "Hrec". }
      rewrite !discrete_fun_equivI. by iRewrite - ("H" $! v).
  - iIntros "HC //=". iNext. iExists (sem_ty_rec C).
    by iFrame. 
Qed.

(* Empty Effect Signature *)
Definition sem_sig_nil {Σ} : sem_sig Σ := iEff_bottom.

(* Universally Quantified, Recursive Effect Signature *)

Definition select_m (m : mode) (v : val) := 
  match m with
    OS => InjLV v
  | MS => InjRV v
  end.

(* Effect Signature *)
Definition sem_sig_eff_rec_pre {Σ} m (A B : sem_sig Σ -d> sem_ty Σ -d> sem_ty Σ) (rec : sem_sig Σ) : sem_sig Σ :=
  (>> (α : sem_ty Σ) (a : val) >> ! (select_m m a) {{ ▷ (∃ rec', rec ≡ rec' ∧ A rec' α a) }}; 
   << (b : val)                << ? b {{ ▷ (∃ rec', rec ≡ rec' ∧ B rec' α b) }} @m).

Global Instance sem_sig_eff_rec_pre_contractive {Σ} m (A B : sem_sig Σ -d> sem_ty Σ -d> sem_ty Σ) :
  Contractive (sem_sig_eff_rec_pre m A B).
Proof.
  intros ?????. 
  rewrite /sem_sig_eff_rec_pre iEffPre_exist_eq iEffPost_exist_eq /=.
  intros ?. simpl. do 3 f_equiv. rewrite iEffPre_base_eq /=.
  intros ?. simpl. do 2 f_equiv.
  { f_contractive. simpl in H. by do 4 f_equiv. }
  do 2 f_equiv. intros ?. rewrite /iEffPost_exist_def. do 3 f_equiv.
  rewrite iEffPost_base_eq /iEffPost_base_def. f_equiv. f_contractive.
  simpl in H. by do 4 f_equiv.
Qed.

Definition sem_sig_eff_rec {Σ} m (A B : sem_sig Σ → sem_ty Σ → sem_ty Σ) : sem_sig Σ :=
  fixpoint (sem_sig_eff_rec_pre m A B).

Lemma sem_sig_eff_rec_unfold {Σ} m (A B : sem_sig Σ → sem_ty Σ → sem_ty Σ) `{NonExpansive2 A, NonExpansive2 B} :
  (sem_sig_eff_rec m A B) ≡ 
    (>> (α : sem_ty Σ) (a : val) >> ! (select_m m a) {{ ▷ (A (sem_sig_eff_rec m A B) α a) }}; 
     << (b : val)                << ? b {{ ▷ (B (sem_sig_eff_rec m A B) α b) }} @m)%ieff.
Proof.
  rewrite {1} /sem_sig_eff_rec fixpoint_unfold {1} /sem_sig_eff_rec_pre.
  do 5 f_equiv. 
  - iSplit. 
    + iIntros "[% [#Hfix HA]] !>". 
      rewrite /sem_sig_eff_rec.
      iAssert (A rec' a ≡ A (fixpoint (sem_sig_eff_rec_pre m A B)) a)%I as "#H".
      { by iRewrite "Hfix". }
      rewrite discrete_fun_equivI. by iRewrite - ("H" $! a0).
    + iIntros "HA //=". iExists (sem_sig_eff_rec m A B).
      by iFrame. 
  - intros ?. rewrite iEffPost_base_eq /iEffPost_base_def.
    apply non_dep_fun_equiv. do 2 f_equiv. intros ?. do 2 f_equiv. iSplit.
    + iIntros "[% [#Hfix HB]]". 
      rewrite /sem_sig_eff_rec.
      iAssert (B rec' a ≡ B (fixpoint (sem_sig_eff_rec_pre m A B)) a)%I as "#H".
      { by iRewrite "Hfix". }
      rewrite discrete_fun_equivI. by iRewrite - ("H" $! a1).
    + iIntros "Hτ //=". iExists (sem_sig_eff_rec m A B).
      by iFrame. 
Qed.

Lemma sem_sig_eff_rec_unfold' {Σ} m (A B : sem_sig Σ -d> sem_ty Σ -d> sem_ty Σ) `{ NonExpansive2 A, NonExpansive2 B } v Φ:
  iEff_car (sem_sig_eff_rec m A B) v Φ ⊣⊢
    iEff_car (>> (α : sem_ty Σ) (a : val) >> ! (select_m m a) {{ ▷ (A (sem_sig_eff_rec m A B) α a) }}; 
              << (b : val)                << ? b {{ ▷ (B (sem_sig_eff_rec m A B) α b) }} @m)%ieff v Φ.
Proof.
  assert (Hequiv :
  iEff_car (sem_sig_eff_rec m A B) v Φ ⊣⊢
    iEff_car (>> (α : sem_ty Σ) (a : val) >> ! (select_m m a) {{ ▷ (A (sem_sig_eff_rec m A B) α a) }}; 
              << (b : val)                << ? b {{ ▷ (B (sem_sig_eff_rec m A B) α b) }} @m)%ieff v Φ).
  { f_equiv. apply non_dep_fun_equiv. by apply sem_sig_eff_rec_unfold. }
  by rewrite Hequiv.
Qed.

Lemma sem_sig_eff_rec_eq {Σ} m A B v Φ `{ NonExpansive2 A, NonExpansive2 B }:
  iEff_car (sem_sig_eff_rec (Σ:=Σ) m A B) v Φ ⊣⊢
    (∃ α a, ⌜ (select_m m a) = v ⌝ ∗ (▷ A (sem_sig_eff_rec m A B) α a) ∗ 
                        □? m (∀ b, (▷ B (sem_sig_eff_rec m A B) α b) -∗ Φ b))%I.
Proof. 
  etrans; [by apply sem_sig_eff_rec_unfold'|]. 
  by rewrite (iEff_tele_eq' [tele _ _] [tele _]) /=. 
Qed.

(* The sem_sig_eff_rec protocol is monotonic. *)
Global Instance sem_sig_eff_rec_mono_prot {Σ} A B `{ NonExpansive2 A, NonExpansive2 B }:
  MonoProt (@sem_sig_eff_rec Σ OS A B).
Proof.
  constructor. iIntros (???) "HΦ'".
  rewrite !sem_sig_eff_rec_eq /=.
  iIntros "(% & % & <- & Hτ & HκΦ)".
  iExists α, a. iSplitR; first done. iFrame. simpl.
  iIntros (b) "Hκ". iApply "HΦ'". by iApply "HκΦ".
Qed.

(* The sem_sig_eff_rec protocol is persistently monotonic. *)
Global Instance sem_sig_eff_rec_pers_mono_prot {Σ} A B `{ NonExpansive2 A, NonExpansive2 B }:
  PersMonoProt (@sem_sig_eff_rec Σ MS A B).
Proof.
  constructor. iIntros (???) "#HΦ'".
  rewrite !sem_sig_eff_rec_eq. simpl.
  iIntros "(% & % & <- & Hτ & #HκΦ)".
  iExists α, a. iSplitR; first done. iFrame. simpl.
  iIntros "!# %b Hκ". iApply "HΦ'". by iApply "HκΦ".
Qed.

Lemma upcl_sem_sig_rec_eff {Σ} m A B v Φ `{ NonExpansive2 A, NonExpansive2 B}:
  iEff_car (upcl m (sem_sig_eff_rec (Σ:=Σ) m A B)) v Φ ⊣⊢
    (∃ α a, ⌜ select_m m a = v ⌝ ∗ (▷ A (sem_sig_eff_rec m A B) α a) ∗ 
                        □? m (∀ b, (▷ B (sem_sig_eff_rec m A B) α b) -∗ Φ b))%I.
Proof.
  assert (Hequiv:
    iEff_car (upcl m (sem_sig_eff_rec m A B)) v Φ ≡ iEff_car (sem_sig_eff_rec m A B) v Φ).
  { f_equiv. apply non_dep_fun_equiv. destruct m; [by rewrite upcl_id|by rewrite pers_upcl_id]. }
  rewrite Hequiv. by apply sem_sig_eff_rec_eq.
Qed.

(* Notations. *)
Notation "⟨⟩" := (sem_sig_nil, sem_sig_nil) : sem_sig_scope.
Notation "⟨ ρ , ρ' ⟩" := (ρ%R, ρ'%R) : sem_sig_scope.
Notation "⟨ ρ , ⟩" := (ρ%R, sem_sig_nil) : sem_sig_scope.
Notation "⟨ , ρ' ⟩" := (sem_sig_nil, ρ'%R) : sem_sig_scope.
Notation "'μ∀TS:' θ , α , τ ⇒ κ" := (sem_sig_eff_rec OS (λ θ α, τ%T) (λ θ α, κ%T))
  (at level 100, τ, κ at level 200) : sem_sig_scope.

Notation "'μ∀TSₘ:' θ , α , τ ⇒ κ" := (sem_sig_eff_rec MS (λ θ α, τ%T) (λ θ α, κ%T))
  (at level 100, τ, κ at level 200) : sem_sig_scope.

Notation "'Void'" := sem_ty_void : sem_ty_scope.
Notation "()" := sem_ty_unit : sem_ty_scope.
Notation "'𝔹'" := (sem_ty_bool) : sem_ty_scope.
Notation "'ℤ'" := (sem_ty_int) : sem_ty_scope.
Notation "'Moved'" := (sem_ty_moved) : sem_ty_scope.
Notation "'! τ " := (sem_ty_cpy τ)
  (at level 10) : sem_ty_scope.
Notation "τ '×' κ" := (sem_ty_prod τ%T κ%T)
  (at level 120, κ at level 200) : sem_ty_scope.
Infix "+" := (sem_ty_sum) : sem_ty_scope.

Notation "'Ref' τ" := (sem_ty_ref τ%T) 
  (at level 50) : sem_ty_scope.

Notation "'Refᶜ' τ" := (sem_ty_ref_cpy τ%T) 
  (at level 50) : sem_ty_scope.

Notation "'∀T:' α , ρs ,  C " := (sem_ty_forall ρs%R (λ α, C%T)) 
  (at level 180) : sem_ty_scope.

Notation "'∀T:' α ,, C " := (sem_ty_forall (sem_sig_nil, sem_sig_nil) (λ α, C%T)) 
  (at level 180) : sem_ty_scope.

Notation "'∀R:' θ , C " := (sem_ty_sig_forall (λ θ, C%T)) 
  (at level 180) : sem_ty_scope.

Notation "'∃:' α , C " := (sem_ty_exists (λ α, C%T)) 
  (at level 180) : sem_ty_scope.

Notation "'μT:' α , C " := (sem_ty_rec (λ α, C%T))
  (at level 180) : sem_ty_scope.

Notation "τ '-{' ρs '}-∘' κ" := (sem_ty_aarr ρs%R τ%T κ%T)
  (at level 100, ρs, κ at level 200) : sem_ty_scope.
Notation "τ ⊸ κ" := (sem_ty_aarr (sem_sig_nil, sem_sig_nil) τ%T κ%T)
  (at level 99, κ at level 200) : sem_ty_scope.

Notation "τ '-{' ρs '}->' κ" := (sem_ty_uarr ρs%R τ%T κ%T)
  (at level 100, ρs, κ at level 200) : sem_ty_scope.
Notation "τ → κ" := (sem_ty_uarr (sem_sig_nil, sem_sig_nil) τ%T κ%T)
  (at level 99, κ at level 200) : sem_ty_scope.

(* Derived Types *)

Definition ListF {Σ} (τ : sem_ty Σ) := (λ α, () + (τ × α))%T.

(* List type. *)
Definition sem_ty_list {Σ} (τ : sem_ty Σ) : sem_ty Σ := 
    sem_ty_rec (ListF τ).

Notation "'List' τ" := (sem_ty_list τ%T) 
  (at level 50) : sem_ty_scope.

(* List type. *)
Definition sem_ty_option {Σ} (τ : sem_ty Σ) : sem_ty Σ := (() + τ)%T.

Notation "'Option' τ" := (sem_ty_option τ%T) 
  (at level 50) : sem_ty_scope.

(**  Prove that type formers are non-expansive and respect setoid equality. *)
Section types_properties.
  Context `{heapGS Σ}.

  Ltac solve_non_expansive :=
    repeat intros ?;
    unfold sem_ty_unit, sem_ty_int, sem_ty_bool, sem_ty_cpy,
           sem_ty_prod, sem_ty_sum, sem_ty_aarr,
           sem_ty_uarr, sem_ty_ref, sem_ty_ref_cpy,
           sem_ty_rec, sem_ty_list, sem_ty_forall, sem_ty_exists;
    repeat (f_equiv || done || intros ? || by apply non_dep_fun_dist).

  Global Instance sem_ty_cpy_ne : NonExpansive (sem_ty_cpy).
  Proof. solve_non_expansive. Qed.

  Global Instance sem_ty_prod_ne : NonExpansive2 (@sem_ty_prod Σ).
  Proof. solve_non_expansive. Qed.

  Global Instance sem_ty_sum_ne : NonExpansive2 (@sem_ty_sum Σ).
  Proof. solve_non_expansive. Qed.

  Global Instance sem_ty_aarr_ne : NonExpansive3 sem_ty_aarr.
  Proof. solve_non_expansive. Qed.

  Global Instance sem_ty_uarr_ne : NonExpansive3 sem_ty_uarr.
  Proof. solve_non_expansive. Qed.

  Global Instance sem_ty_ref_ne : NonExpansive (@sem_ty_ref Σ _).
  Proof. solve_non_expansive. Qed.

  Global Instance sem_ty_ref_cpy_ne : NonExpansive (@sem_ty_ref_cpy Σ _).
  Proof. solve_non_expansive. Qed.

  Global Instance sem_ty_forall_ne n ρs :
    Proper (pointwise_relation _ (dist n) ==> dist n) (sem_ty_forall ρs).
  Proof. intros ????. unfold sem_ty_forall; repeat f_equiv. Qed.

  Global Instance sem_ty_exist_ne n :
    Proper (pointwise_relation _ (dist n) ==> dist n) sem_ty_exists.
  Proof. intros ????. unfold sem_ty_exists; repeat f_equiv. 
         unfold pointwise_relation in H. by apply non_dep_fun_dist. Qed.

  Global Instance sem_ty_rec_ne :
    NonExpansive (@sem_ty_rec Σ).
  Proof.
    intros ????. unfold sem_ty_rec. apply fixpoint_ne.
    intros ??. unfold sem_ty_rec_pre. do 4 f_equiv. 
    by apply non_dep_fun_dist.
  Qed.

  Global Instance sem_ty_listF_ne τ : NonExpansive (@ListF Σ τ).
  Proof. intros ?????. rewrite /ListF. 
         apply non_dep_fun_dist. by repeat f_equiv.
  Qed.

  Global Instance sem_ty_listF_ne_2 : NonExpansive2 (@ListF Σ).
  Proof. intros ???????. unfold ListF; by repeat f_equiv. Qed.

  Global Instance sem_ty_list_ne : NonExpansive (@sem_ty_list Σ).
  Proof. intros ?????. unfold sem_ty_list. 
         apply non_dep_fun_dist. f_equiv. 
         rewrite /ListF. intros ?. by repeat f_equiv.
  Qed.

  Global Instance sem_ty_cpy_proper : Proper ((≡) ==> (≡)) sem_ty_cpy.
  Proof. solve_non_expansive. Qed.

  Global Instance sem_ty_prod_proper : Proper ((≡) ==> (≡) ==> (≡)) (@sem_ty_prod Σ).
  Proof. solve_non_expansive. Qed.

  Global Instance sem_ty_sum_proper : Proper ((≡) ==> (≡) ==> (≡)) (@sem_ty_sum Σ).
  Proof. solve_non_expansive. Qed.

  Global Instance sem_ty_aarr_proper : Proper ((≡) ==> (≡) ==> (≡) ==> (≡)) sem_ty_aarr.
  Proof. solve_non_expansive. Qed.

  Global Instance sem_ty_uarr_proper : Proper ((≡) ==> (≡) ==> (≡) ==> (≡)) sem_ty_uarr.
  Proof. solve_non_expansive. Qed.

  Global Instance sem_ty_ref_proper : Proper ((≡) ==> (≡)) (@sem_ty_ref Σ _).
  Proof. intros ????. unfold sem_ty_ref; by repeat f_equiv. Qed.

  Global Instance sem_ty_ref_cpy_proper : Proper ((≡) ==> (≡)) (@sem_ty_ref_cpy Σ _).
  Proof. intros ????. unfold sem_ty_ref_cpy; by repeat f_equiv. Qed.

  Global Instance sem_ty_forall_proper ρs :
    Proper (pointwise_relation _ (≡) ==> (≡)) (sem_ty_forall ρs).
  Proof. intros ????; unfold sem_ty_forall; repeat f_equiv. Qed.

  Global Instance sem_ty_exist_proper :
    Proper (pointwise_relation _ (≡) ==>(≡)) sem_ty_exists.
  Proof. 
    intros ????. unfold sem_ty_exists; repeat f_equiv.
    by apply non_dep_fun_equiv.
  Qed.

  Global Instance sem_ty_rec_proper :
    Proper (pointwise_relation _ (≡) ==>(≡)) (@sem_ty_rec Σ).
  Proof.
    intros C1 C2 HA. apply equiv_dist=> n.
    apply sem_ty_rec_ne=> A. by apply equiv_dist.
  Qed.

End types_properties.
