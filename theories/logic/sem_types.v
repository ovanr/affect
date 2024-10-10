
(* sem_types.v *)

(* This file contains the definition of semantic types *)

From iris.proofmode Require Import base tactics.
From iris.algebra Require Import ofe list.
From iris.base_logic Require Export iprop upred invariants.

(* Local imports *)
From affect.lib Require Import logic.
From affect.lang Require Import affect.
From affect.logic Require Import sem_def.
From affect.logic Require Import mode.
From affect.logic Require Import sem_sig.
From affect.logic Require Import sem_row.
From affect.logic Require Import ewpw.

(* Base types. *)
Definition sem_ty_bot {Σ} : sem_ty Σ := (λ v, False)%I.

Global Instance sem_ty_bot_instance {Σ} : Bottom (sem_ty Σ) := sem_ty_bot. 

Definition sem_ty_unit {Σ} : sem_ty Σ := (λ v, ⌜ v = #() ⌝)%I.
Definition sem_ty_bool {Σ} : sem_ty Σ := (λ v, ∃ b : bool, ⌜ v = #b ⌝)%I.
Definition sem_ty_int {Σ} : sem_ty Σ := (λ v, ∃ n : Z, ⌜ v = #n ⌝)%I.
Definition sem_ty_string {Σ} : sem_ty Σ := (λ v, ∃ s : string, ⌜ v = #(LitStr s)⌝)%I.
Definition sem_ty_top {Σ} : sem_ty Σ := (λ v, True)%I.

Global Instance sem_ty_top_instance {Σ} : Top (sem_ty Σ) := sem_ty_top. 
Global Instance sem_ty_inhabited {Σ} : Inhabited (sem_ty Σ) := populate sem_ty_top. 

Definition sem_ty_mbang {Σ} (m : mode) (τ : sem_ty Σ) : sem_ty Σ := (λ v, □? m (τ v))%I.

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

(* Arrow type. *)
Definition sem_ty_arr `{heapGS Σ} 
  (ρ : sem_row Σ)
  (τ : sem_ty Σ)
  (κ : sem_ty Σ) : sem_ty Σ :=
  (λ (v : val),
    ∀ (w : val),
      τ w -∗ 
      EWPW (v w) <| ρ |> {{ u, κ u}})%I.

(* Polymorphic type. *)
Definition sem_ty_type_forall {Σ} 
    (C : sem_ty Σ → sem_ty Σ) : sem_ty Σ := (λ v, ∀ τ, C τ v)%I.

(* Polymorphic effect type. *)
Definition sem_ty_row_forall {Σ} 
  (A : sem_row Σ → sem_ty Σ) : sem_ty Σ := (λ v, ∀ θ, A θ v)%I.

(* Polymorphic mode type. *)
Definition sem_ty_mode_forall {Σ} 
  (C : mode → sem_ty Σ) : sem_ty Σ := (λ v, ∀ ν, C ν v)%I.

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

Notation "'𝟙'" := sem_ty_unit : sem_ty_scope.
Notation "'𝔹'" := (sem_ty_bool) : sem_ty_scope.
Notation "'ℤ'" := (sem_ty_int) : sem_ty_scope.
Notation "'Str'" := (sem_ty_string) : sem_ty_scope.
Notation "![ m ] τ" := (sem_ty_mbang m τ) (at level 10) : sem_ty_scope.
Notation "! τ" := (sem_ty_mbang MS τ) (at level 9, τ at level 9) : sem_ty_scope.

Notation "τ '×' κ" := (sem_ty_prod τ%T κ%T) (at level 120) : sem_ty_scope.
Infix "+" := (sem_ty_sum) : sem_ty_scope.

Notation "'Ref' τ" := (sem_ty_ref τ%T) 
  (at level 50) : sem_ty_scope.

Notation "'Refᶜ' τ" := (sem_ty_ref_cpy τ%T) 
  (at level 50) : sem_ty_scope.

Notation "'∀ₜ' α , C " := (sem_ty_type_forall (λ α, C%T)) 
  (at level 180) : sem_ty_scope.

Notation "'∀ᵣ' θ , C " := (sem_ty_row_forall (λ θ, C%T)) 
  (at level 180) : sem_ty_scope.

Notation "'∀ₘ' ν , C " := (sem_ty_mode_forall (λ ν, C%T)) 
  (at level 180) : sem_ty_scope.

Notation "'∃ₜ' α , C " := (sem_ty_exists (λ α, C%T)) 
  (at level 180) : sem_ty_scope.

Notation "'μₜ' α , C " := (sem_ty_rec (λ α, C%T))
  (at level 180) : sem_ty_scope.

Notation "τ ⊸ κ" := (sem_ty_arr ⟨⟩%R τ%T κ%T)
  (at level 99, κ at level 200) : sem_ty_scope.

Notation "τ '-{' ρ '}-∘' κ" := (sem_ty_arr ρ%R τ%T κ%T)
  (at level 100, ρ, κ at level 200) : sem_ty_scope.

Notation "τ '-{' ρ '}-[' m ']->' κ" := (sem_ty_mbang m (sem_ty_arr ρ%R τ%T κ%T))%T
  (at level 100, m, ρ, κ at level 200) : sem_ty_scope.

Notation "τ '-[' m ']->' κ" := (sem_ty_mbang m (sem_ty_arr ⟨⟩%R τ%T κ%T))%T
  (at level 100, m, κ at level 200) : sem_ty_scope.

Notation "τ '-{' ρ '}->' κ" := (sem_ty_mbang MS (sem_ty_arr ρ%R τ%T κ%T))
  (at level 100, ρ, κ at level 200) : sem_ty_scope.

Notation "τ → κ" := (sem_ty_mbang MS (sem_ty_arr ⟨⟩%R τ%T κ%T))
  (at level 99, κ at level 200) : sem_ty_scope.

(* Derived Types *)
Definition ListF {Σ} (τ : sem_ty Σ) := (λ α, 𝟙 + (τ × α))%T.

(* List type. *)
Definition sem_ty_list {Σ} (τ : sem_ty Σ) : sem_ty Σ := 
    sem_ty_rec (ListF τ).

Notation "'List' τ" := (sem_ty_list τ%T) 
  (at level 50) : sem_ty_scope.

(* List type. *)
Definition sem_ty_option {Σ} (τ : sem_ty Σ) : sem_ty Σ := (𝟙 + τ)%T.

Notation "'Option' τ" := (sem_ty_option τ%T) 
  (at level 50) : sem_ty_scope.

(**  Prove that type formers are non-expansive and respect setoid equality. *)
Section types_properties.
  Context `{heapGS Σ}.

  Implicit Types σ : sem_sig Σ.

  Ltac solve_non_expansive :=
    repeat intros ?;
    unfold sem_ty_unit, sem_ty_int, sem_ty_bool, sem_ty_mbang,
           sem_ty_prod, sem_ty_sum, sem_ty_arr,
           sem_ty_ref, sem_ty_ref_cpy, 
           sem_ty_rec, sem_ty_list, sem_ty_type_forall, sem_ty_exists;
    repeat (f_equiv || done || intros ? || by apply non_dep_fun_dist).

  Global Instance sem_ty_mbang_ne m : NonExpansive (@sem_ty_mbang Σ m).
  Proof. solve_non_expansive. Qed.

  Global Instance sem_ty_prod_ne : NonExpansive2 (@sem_ty_prod Σ).
  Proof. solve_non_expansive. Qed.

  Global Instance sem_ty_sum_ne : NonExpansive2 (@sem_ty_sum Σ).
  Proof. solve_non_expansive. Qed.

  Global Instance sem_ty_arr_ne : NonExpansive3 sem_ty_arr.
  Proof. solve_non_expansive. Qed.

  Global Instance sem_ty_ref_ne : NonExpansive (@sem_ty_ref Σ _).
  Proof. solve_non_expansive. Qed.

  Global Instance sem_ty_ref_cpy_ne : NonExpansive (@sem_ty_ref_cpy Σ _).
  Proof. solve_non_expansive. Qed.

  Global Instance sem_ty_type_forall_ne n :
    Proper (pointwise_relation _ (dist n) ==> dist n) (@sem_ty_type_forall Σ).
  Proof.
    intros ????. unfold sem_ty_type_forall; repeat f_equiv. 
    by apply non_dep_fun_dist.
  Qed.

  Global Instance sem_ty_type_forall_row_ne n :
    Proper (pointwise_relation _ (dist n) ==> dist n) (@sem_ty_row_forall Σ).
  Proof.
    intros ????. unfold sem_ty_row_forall; repeat f_equiv.
    by apply non_dep_fun_dist.
  Qed.

  Global Instance sem_ty_type_forall_mode_ne n :
    Proper (pointwise_relation _ (dist n) ==> dist n) (@sem_ty_mode_forall Σ).
  Proof.
    intros ????. unfold sem_ty_mode_forall; repeat f_equiv. 
    by apply non_dep_fun_dist.
  Qed.

  Global Instance sem_ty_exist_ne n :
    Proper (pointwise_relation _ (dist n) ==> dist n) sem_ty_exists.
  Proof. 
    intros ????. unfold sem_ty_exists; repeat f_equiv. 
    by apply non_dep_fun_dist. 
  Qed.

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

  Global Instance sem_ty_mbang_proper m : Proper ((≡) ==> (≡)) (@sem_ty_mbang Σ m).
  Proof. solve_non_expansive. Qed.

  Global Instance sem_ty_prod_proper : Proper ((≡) ==> (≡) ==> (≡)) (@sem_ty_prod Σ).
  Proof. solve_non_expansive. Qed.

  Global Instance sem_ty_sum_proper : Proper ((≡) ==> (≡) ==> (≡)) (@sem_ty_sum Σ).
  Proof. solve_non_expansive. Qed.

  Global Instance sem_ty_arr_proper : Proper ((≡) ==> (≡) ==> (≡) ==> (≡)) sem_ty_arr.
  Proof. solve_non_expansive. Qed.

  Global Instance sem_ty_ref_proper : Proper ((≡) ==> (≡)) (@sem_ty_ref Σ _).
  Proof. intros ????. unfold sem_ty_ref; by repeat f_equiv. Qed.

  Global Instance sem_ty_ref_cpy_proper : Proper ((≡) ==> (≡)) (@sem_ty_ref_cpy Σ _).
  Proof. intros ????. unfold sem_ty_ref_cpy; by repeat f_equiv. Qed.

  Global Instance sem_ty_type_forall_proper :
    Proper (pointwise_relation _ (≡) ==> (≡)) (@sem_ty_type_forall Σ).
  Proof. 
    intros ????. unfold sem_ty_type_forall; repeat f_equiv. 
    by apply non_dep_fun_equiv. 
  Qed.

  Global Instance sem_ty_row_forall_proper :
    Proper (pointwise_relation _ (≡) ==> (≡)) (@sem_ty_row_forall Σ).
  Proof. 
    intros ????. unfold sem_ty_row_forall; repeat f_equiv. 
    by apply non_dep_fun_equiv. 
  Qed.

  Global Instance sem_ty_mode_forall_proper :
    Proper (pointwise_relation _ (≡) ==> (≡)) (@sem_ty_mode_forall Σ).
  Proof. 
    intros ????. unfold sem_ty_mode_forall; repeat f_equiv. 
    by apply non_dep_fun_equiv. 
  Qed.

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

  Global Instance sem_ty_mbang_persistent τ :
    (∀ v, Persistent (@sem_ty_mbang Σ MS τ v)).
  Proof. unfold sem_ty_mbang. simpl. apply _. Qed.

  Global Instance sem_ty_type_forall_type_persistent (C : sem_ty Σ → sem_ty Σ) v :
    (∀ τ w, Persistent (C τ w)) →
    Persistent ((sem_ty_type_forall C) v). 
  Proof. unfold sem_ty_type_forall. simpl. apply _. Qed.

  Global Instance sem_ty_row_forall_persistent (C : sem_row Σ → sem_ty Σ) v :
    (∀ τ w, Persistent (C τ w)) →
    Persistent ((sem_ty_row_forall C) v).
  Proof. unfold sem_ty_row_forall. simpl. apply _. Qed.

  Global Instance sem_ty_mode_forall_persistent (C : mode → sem_ty Σ) v :
    (∀ τ w, Persistent (C τ w)) →
    Persistent ((sem_ty_mode_forall C) v).
  Proof. unfold sem_ty_mode_forall. simpl. apply _. Qed.

End types_properties.

Section multi_types.
  
  Context `{heapGS Σ}.

  Implicit Types τ κ : sem_ty Σ.
  
  Class MultiT {Σ} (τ : sem_ty Σ) := {
    multi_ty : ⊢ (τ%T ≤ₜ ! τ%T)
  }.

  Global Arguments MultiT _ _%T.

  Global Instance multi_ty_persistent (τ : sem_ty Σ) `{! MultiT τ} :
    ∀ v, Persistent (τ v).
  Proof. 
    intros ?. inv MultiT0. 
    rewrite /ty_le /tc_opaque /sem_ty_mbang /= in multi_ty0.
    rewrite /Persistent. 
    iIntros "Hτ.". iDestruct (multi_ty0 with "Hτ.") as "#Hτ".
    by iModIntro.
  Qed.

End multi_types.

Section sub_typing.

  Context `{!heapGS Σ}.

  Implicit Types τ κ : sem_ty Σ.

  Lemma ty_le_refl (τ : sem_ty Σ) : ⊢ τ ≤ₜ τ.
  Proof. iIntros "!# % $". Qed.

  Lemma ty_le_trans (τ₁ τ₂ τ₃ : sem_ty Σ) :
    τ₁ ≤ₜ τ₂ -∗
    τ₂ ≤ₜ τ₃ -∗
    τ₁ ≤ₜ τ₃.
  Proof. 
    iIntros "#Hτ₁₂ #Hτ₂₃ !# %v Hτ₁". 
    iApply "Hτ₂₃". by iApply "Hτ₁₂".
  Qed.

  Lemma ty_le_bot (τ : sem_ty Σ) :
    ⊢ ⊥ ≤ₜ τ.
  Proof. iIntros "% !# []". Qed.

  Lemma ty_le_arr (τ₁ κ₁ τ₂ κ₂ : sem_ty Σ) (ρ ρ' : sem_row Σ) :
    ρ ≤ᵣ ρ' -∗
    τ₂ ≤ₜ τ₁ -∗
    κ₁ ≤ₜ κ₂ -∗
    (τ₁ -{ ρ }-∘ κ₁) ≤ₜ (τ₂ -{ ρ' }-∘ κ₂).
  Proof.
    iIntros "#Hρ  #Hτ₂₁ #Hκ₁₂ !# %v Hτκ₁". 
    rewrite /sem_ty_arr /=. iIntros "% Hτ₂".
    iApply (ewpw_sub with "Hρ").
    iApply (ewpw_mono with "[Hτκ₁ Hτ₂]").
    { iApply ("Hτκ₁" with "[Hτ₂]"); by iApply "Hτ₂₁". }
    iIntros "!# % Hκ !>". by iApply "Hκ₁₂".
  Qed.

  Lemma ty_le_ref (τ₁ τ₂ : sem_ty Σ) :
    τ₁ ≤ₜ τ₂ -∗
    (Ref τ₁) ≤ₜ (Ref τ₂).
  Proof.
    iIntros "#Hτ₁₂ !# %v (%l & -> & (%w & Hl & Hτw))".
    iExists l. iSplit; first done.
    iExists w. iFrame. by iApply "Hτ₁₂".
  Qed.

  Lemma ty_le_prod (τ₁ τ₂ κ₁ κ₂ : sem_ty Σ) :
    τ₁ ≤ₜ τ₂ -∗
    κ₁ ≤ₜ κ₂ -∗
    (τ₁ × κ₁) ≤ₜ (τ₂ × κ₂).
  Proof.
    iIntros "#Hτ₁₂ #Hκ₁₂ !# %v (%w₁ & %w₂ & -> &Hw₁ & Hw₂)".
    iExists w₁, w₂. iSplit; first done. iSplitL "Hw₁".
    { by iApply "Hτ₁₂". }
    by iApply "Hκ₁₂".
  Qed.
  
  Lemma ty_le_sum (τ₁ τ₂ κ₁ κ₂ : sem_ty Σ) :
    τ₁ ≤ₜ τ₂ -∗
    κ₁ ≤ₜ κ₂ -∗
    (τ₁ + κ₁) ≤ₜ (τ₂ + κ₂).
  Proof.
    iIntros "#Hτ₁₂ #Hκ₁₂ !# %v (%v' & [(-> & Hτ₁)|(-> & Hκ₁)])"; iExists v'. 
    - iLeft. iSplit; first done. by iApply "Hτ₁₂".
    - iRight. iSplit; first done. by iApply "Hκ₁₂". 
  Qed.

  Corollary ty_le_option (τ₁ τ₂ : sem_ty Σ) :
    τ₁ ≤ₜ τ₂ -∗
    (Option τ₁) ≤ₜ (Option τ₂).
  Proof. iIntros "#?". iApply ty_le_sum; last done. iIntros "!# % $". Qed.

  Lemma ty_le_type_forall (τ₁ τ₂ : sem_ty Σ → sem_ty Σ) :
    (∀ α, τ₁ α ≤ₜ τ₂ α) -∗
    (∀ₜ α, τ₁ α)%T ≤ₜ (∀ₜ α, τ₂ α).
  Proof. iIntros "#Hτ₁₂ !# %v Hτ₁ %τ /=". by iApply "Hτ₁₂". Qed.

  Lemma ty_le_row_forall (τ₁ τ₂ : sem_row Σ → sem_ty Σ) :
    (∀ θ, τ₁ θ ≤ₜ τ₂ θ) -∗
    (∀ᵣ θ, τ₁ θ) ≤ₜ (∀ᵣ θ, τ₂ θ).
  Proof. iIntros "#Hτ₁₂ !# %v Hτ₁ %τ /=". by iApply "Hτ₁₂". Qed.

  Lemma ty_le_mode_forall (τ₁ τ₂ : mode → sem_ty Σ) :
    (∀ ν, τ₁ ν ≤ₜ τ₂ ν) -∗
    (∀ₘ ν, τ₁ ν) ≤ₜ (∀ₘ ν, τ₂ ν).
  Proof. iIntros "#Hτ₁₂ !# %v Hτ₁ %τ /=". by iApply "Hτ₁₂". Qed.

  Lemma ty_le_exists (τ₁ τ₂ : sem_ty Σ → sem_ty Σ) :
    (∀ α, τ₁ α ≤ₜ τ₂ α) -∗
    (∃ₜ α, τ₁ α) ≤ₜ (∃ₜ α, τ₂ α).
  Proof.
    iIntros "#Hτ₁₂ !# %v (%α & Hα) //=".
    iExists α. by iApply "Hτ₁₂".
  Qed.

  Lemma ty_le_rec (τ₁ τ₂ : sem_ty Σ -> sem_ty Σ) `{NonExpansive τ₁, NonExpansive τ₂} :
    □ (∀ α α', (α ≤ₜ α') -∗ τ₁ α ≤ₜ τ₂ α') -∗
    (μₜ α, τ₁ α) ≤ₜ (μₜ α, τ₂ α).
  Proof.
    iIntros "#Hτ₁₂ !#". iLöb as "IH". iIntros "%v Hτ₁".
    iApply sem_ty_rec_unfold.
    rewrite sem_ty_rec_unfold. iNext.
    iApply ("Hτ₁₂" with "[] Hτ₁").
    rewrite /ty_le /tc_opaque. iApply "IH".
  Qed.
  
  Corollary ty_le_list (τ₁ τ₂ : sem_ty Σ) :
    τ₁ ≤ₜ τ₂ -∗
    List τ₁ ≤ₜ List τ₂.
  Proof.
    rewrite /sem_ty_list. iIntros "#Hτ₁₂".
    iApply ty_le_rec. iIntros "!# % % Hαα'".
    iApply ty_le_sum; first iApply ty_le_refl.
    by iApply ty_le_prod.
  Qed.

  Lemma ty_le_mbang_intro_os τ : ⊢ τ ≤ₜ ![OS] τ.
  Proof. iIntros "!# %v H". rewrite /sem_ty_mbang //. Qed.

  Corollary ty_le_mbang_intro_void m τ : ⊢ ⊥ ≤ₜ ![m] τ.
  Proof. iApply ty_le_bot. Qed.

  Global Instance multi_ty_void : @MultiT Σ ⊥.
  Proof. constructor. iApply ty_le_mbang_intro_void. Qed.

  Lemma ty_le_mbang_intro_unit m : ⊢ 𝟙 ≤ₜ@{ Σ } ![m] 𝟙.
  Proof. 
    iIntros "!# %v ->". 
    iApply bi.intuitionistically_intuitionistically_if. 
    iIntros "!# //".
  Qed.

  Global Instance multi_ty_unit : @MultiT Σ 𝟙.
  Proof. constructor. iApply ty_le_mbang_intro_unit. Qed.
  
  Lemma ty_le_mbang_intro_bool m : ⊢ 𝔹 ≤ₜ@{ Σ } ![m] 𝔹.
  Proof. 
    iIntros "!# %v (% & ->)". 
    iApply bi.intuitionistically_intuitionistically_if. 
    iIntros "!#". by iExists b.
  Qed.

  Global Instance multi_ty_bool : @MultiT Σ 𝔹.
  Proof. constructor. iApply ty_le_mbang_intro_bool. Qed.

  Lemma ty_le_mbang_intro_int m : ⊢ ℤ ≤ₜ@{ Σ } ![m] ℤ.
    iIntros "!# %v (% & ->)". 
    iApply bi.intuitionistically_intuitionistically_if. 
    iIntros "!#". by iExists n.
  Qed.

  Global Instance multi_ty_int : @MultiT Σ ℤ.
  Proof. constructor. iApply ty_le_mbang_intro_int. Qed.
  
  Lemma ty_le_mbang_intro_top m : ⊢ ⊤ ≤ₜ@{ Σ } ![m] ⊤.
  Proof. 
    iIntros "!# %v _". 
    iApply bi.intuitionistically_intuitionistically_if. 
    by iIntros "!#".
  Qed.

  Global Instance multi_ty_top : @MultiT Σ ⊤.
  Proof. constructor. iApply ty_le_mbang_intro_top. Qed.

  Lemma ty_le_mbang_idemp m τ : ⊢ (![m] τ ≤ₜ ![m] (![m] τ)).
  Proof. 
    iIntros "!# %v H".
    iApply bi.intuitionistically_if_idemp. 
    iApply "H".
  Qed.

  Global Instance multi_ty_mbang τ : MultiT (! τ).
  Proof. constructor. iApply ty_le_mbang_idemp. Qed.

  Corollary ty_le_mbang_intro_uarr τ ρ κ : ⊢ (τ -{ ρ }-> κ) ≤ₜ (! (τ -{ ρ }-> κ)).
  Proof. iApply ty_le_mbang_idemp. Qed.

  Corollary multi_ty_uarr τ ρ κ : MultiT (τ -{ ρ }-> κ).
  Proof. apply _. Qed.

  Lemma ty_le_mbang_intro_prod τ κ m : τ ≤ₜ ![m] τ -∗ κ ≤ₜ ![m] κ -∗ (τ × κ) ≤ₜ ![m] (τ × κ).
  Proof. 
    iIntros "#Hτle #Hκle !# %v (% & % & -> & Hτ & Hκ)". 
    iDestruct ("Hτle" with "Hτ") as "Hτ".
    iDestruct ("Hκle" with "Hκ") as "Hκ". 
    iDestruct (bi.intuitionistically_if_sep_2 with "[Hτ Hκ]") as "H"; first iFrame.
    iApply (bi.intuitionistically_if_mono with "H").
    iIntros "[Hκ Hτ]". iExists v₁, v₂. by iFrame.
  Qed.

  Global Instance multi_ty_prod τ κ `{!MultiT τ} `{!MultiT κ} : MultiT (τ × κ).
  Proof. constructor. inv MultiT0. inv MultiT1. by iApply ty_le_mbang_intro_prod. Qed.

  Lemma ty_le_mbang_intro_sum τ κ m : τ ≤ₜ ![m] τ -∗ κ ≤ₜ ![m] κ -∗ (τ + κ) ≤ₜ ![m] (τ + κ).
  Proof.
    iIntros "#Hτle #Hκle !# %v (% & [(-> & Hτ)|(-> & Hκ)])". 
    - iDestruct ("Hτle" with "Hτ") as "Hτ". 
      iApply (bi.intuitionistically_if_mono with "Hτ").
      iIntros "Hτ". iExists v'. iLeft. by iFrame.
    - iDestruct ("Hκle" with "Hκ") as "Hκ".
      iApply (bi.intuitionistically_if_mono with "Hκ").
      iIntros "Hκ". iExists v'. iRight. by iFrame.
  Qed.

  Global Instance multi_ty_sum τ κ `{!MultiT τ} `{!MultiT κ} : MultiT (τ + κ).
  Proof. constructor. inv MultiT0. inv MultiT1. by iApply ty_le_mbang_intro_sum. Qed.

  Lemma ty_le_mbang_intro_type_forall (C : sem_ty Σ → sem_ty Σ) m :
    (∀ α, (C α) ≤ₜ ![m] (C α)) -∗ (∀ₜ α, C α) ≤ₜ ![m] (∀ₜ α, C α).
  Proof. 
    iIntros "#Hle % !# H". rewrite /sem_ty_mbang /sem_ty_type_forall.
    iApply forall_intuitionistically_if. iIntros (τ).
    iApply ("Hle" with "H").
  Qed.

  Global Instance multi_ty_type_forall (C : sem_ty Σ → sem_ty Σ) `{! ∀ α, MultiT (C α) } : 
    MultiT (∀ₜ α, C α).
  Proof. 
    constructor. iApply ty_le_mbang_intro_type_forall. 
    iIntros (τ). specialize (H τ). inv H. iApply multi_ty0.
  Qed.

  Lemma ty_le_mbang_intro_row_forall (C : sem_row Σ → sem_ty Σ) m :
    (∀ θ, (C θ) ≤ₜ ![m] (C θ)) -∗ (∀ᵣ θ, C θ) ≤ₜ ![m] (∀ᵣ θ, C θ).
  Proof. 
    iIntros "#Hle % !# H". rewrite /sem_ty_mbang /sem_ty_row_forall.
    iApply forall_intuitionistically_if. iIntros (ρ).
    iApply ("Hle" with "H").
  Qed.
  
  Global Instance multi_ty_row_forall (C : sem_row Σ → sem_ty Σ) `{! ∀ θ, MultiT (C θ) } : 
    MultiT (∀ᵣ θ, C θ).
  Proof. 
    constructor. iApply ty_le_mbang_intro_row_forall. 
    iIntros (τ). specialize (H τ). inv H. iApply multi_ty0.
  Qed.

  Lemma ty_le_mbang_intro_mode_forall (C : mode → sem_ty Σ) m :
    (∀ ν, (C ν) ≤ₜ ![m] (C ν)) -∗ (∀ₘ ν, C ν) ≤ₜ ![m] (∀ₘ ν, C ν).
  Proof. 
    iIntros "#Hle % !# H". rewrite /sem_ty_mbang /sem_ty_mode_forall.
    iApply forall_intuitionistically_if. iIntros (m').
    iApply ("Hle" with "H").
  Qed.

  Global Instance multi_ty_mode_forall (C : mode → sem_ty Σ) `{ ∀ ν, MultiT (C ν) } : 
    MultiT (∀ₘ ν, C ν).
  Proof. 
    constructor. iApply ty_le_mbang_intro_mode_forall. 
    iIntros (τ). specialize (H τ). inv H. iApply multi_ty0.
  Qed.

  Lemma ty_le_mbang_intro_ref_cpy τ m : ⊢ (Refᶜ τ) ≤ₜ ![m] (Refᶜ τ).
  Proof. 
    iIntros "!# % #H". 
    iApply bi.intuitionistically_intuitionistically_if. 
    iIntros "!# //".
  Qed.

  Global Instance multi_ty_ref_cpy τ : MultiT (Refᶜ τ).
  Proof. constructor. iApply ty_le_mbang_intro_ref_cpy. Qed.

  Lemma ty_le_mbang_intro_exists A m : (∀ α, (A α) ≤ₜ ![m] (A α)) -∗ (∃ₜ α, A α) ≤ₜ ![m] (∃ₜ α, A α).
  Proof. 
    iIntros "#H !# % [%α Hτ']". 
    iDestruct ("H" with "Hτ'") as "Hτ".
    iApply (bi.intuitionistically_if_mono with "Hτ").
    iIntros "HA". by iExists α.
  Qed.

  Global Instance multi_ty_exists A `{ ∀ α, MultiT (A α) } : MultiT (∃ₜ α, A α).
  Proof. 
    constructor. iApply ty_le_mbang_intro_exists.
    iIntros (τ). specialize (H τ). inv H. iApply multi_ty0.
  Qed.

  Corollary ty_le_mbang_intro_option τ m : τ ≤ₜ ![m] τ -∗ (Option τ) ≤ₜ ![m] (Option τ).
  Proof. 
    iIntros "#H". 
    iApply ty_le_mbang_intro_sum; [iApply ty_le_mbang_intro_unit|done]. 
  Qed.

  Corollary multi_ty_option τ `{! MultiT τ } : MultiT (Option τ). 
  Proof. apply _. Qed. 

  Lemma ty_le_mbang_intro_rec m (C : sem_ty Σ → sem_ty Σ) `{NonExpansive C} :
    □ (∀ α, (α ≤ₜ ![m] α) -∗ C α ≤ₜ ![m] (C α)) -∗
    (μₜ α, C α) ≤ₜ ![m] (μₜ α, C α).
  Proof. 
    iIntros "#H". destruct m; simpl; first iApply ty_le_refl.
    iIntros "!# %v Hτα".
    iLöb as "IH" forall (v).
    rewrite {1} sem_ty_rec_unfold.
    assert (fixpoint (sem_ty_rec_pre C) v ≡ sem_ty_rec_pre C (fixpoint (sem_ty_rec_pre C)) v).
    { apply non_dep_fun_equiv. apply fixpoint_unfold. }
    rewrite {4} /sem_ty_rec /sem_ty_mbang H {1} /sem_ty_rec_pre. simpl.
    iApply bi.later_intuitionistically. iNext. iExists (fixpoint (sem_ty_rec_pre C)).
    iSpecialize ("H" $! (μₜ α, C α)%T with "[IH]").
    { iIntros "% !# //". }
    iDestruct ("H" $! v with "Hτα") as "#Hτα'". iIntros "!#".
    iSplit; first done. iApply "Hτα'".
  Qed.

  (* The premise uses the unfolded ty_le definition instead of MultiT because it lives in iProp.
     As a result, to prove MultiT for rec types we have to manually prove the instance 
     using the ty_le_mbang_intro_* instances *)
  Global Instance multi_ty_rec (C : sem_ty Σ → sem_ty Σ) `{NonExpansive C} : 
    (∀ α, (α ≤ₜ ! α) -∗ C α ≤ₜ ! (C α)) →
    MultiT (μₜ α, C α).
  Proof. 
    constructor. iApply ty_le_mbang_intro_rec. 
    iIntros "!# % H". specialize (H α).
    by iApply H.
  Qed.

  Corollary ty_le_mbang_intro_list τ m : τ ≤ₜ ![m] τ -∗ (List τ) ≤ₜ ![m] (List τ).
  Proof.
    iIntros "#Hτ". iApply ty_le_mbang_intro_rec.
    iIntros "!# % #Hα". 
    iApply ty_le_mbang_intro_sum; [iApply ty_le_mbang_intro_unit|].
    by iApply ty_le_mbang_intro_prod.
  Qed.

  Global Instance multi_ty_list τ `{! MultiT τ } : MultiT (List τ).
  Proof. constructor. inv MultiT0. by iApply ty_le_mbang_intro_list. Qed.

  Lemma ty_le_mbang_elim (m : mode) (τ : sem_ty Σ) :
    ⊢ (![m] τ) ≤ₜ τ.
  Proof. iIntros "!# % H". iDestruct (bi.intuitionistically_if_elim with "H") as "$". Qed.

  Lemma ty_le_mbang_comp m m' (τ τ' : sem_ty Σ) :
    m' ≤ₘ m -∗ τ ≤ₜ τ' -∗ 
    (![m] τ) ≤ₜ (![m'] τ').
  Proof. 
    iIntros "#Hmm' #Hττ'". 
    iIntros "!# % Hτ". destruct m.
    - iDestruct (mode_le_OS_inv with "Hmm'") as "->".
      rewrite /sem_ty_mbang /=. by iApply "Hττ'".
    - rewrite /sem_ty_mbang /=. iDestruct "Hτ" as "#Hτ".
      iApply bi.intuitionistically_intuitionistically_if. iIntros "!#".
      by iApply "Hττ'". 
  Qed.

  Lemma ty_le_mbang_comm m m' (τ : sem_ty Σ) :
    ⊢ ![m] (![m'] τ) ≤ₜ ![m'] (![m] τ). 
  Proof.
    destruct m, m'.
    - iApply ty_le_refl.
    - iApply ty_le_trans; first iApply ty_le_mbang_elim. 
      iApply ty_le_mbang_comp.
      { iApply mode_le_refl. }
      iApply ty_le_mbang_intro_os.
    - iApply ty_le_trans; first iApply ty_le_mbang_comp.
      { iApply mode_le_refl. }
      { iApply ty_le_mbang_elim. }
      iApply ty_le_mbang_intro_os.
    - iApply ty_le_refl.
  Qed.

  Lemma ty_le_mbang_type_forall (C : sem_ty Σ → sem_ty Σ) m :
    ⊢ (∀ₜ α, ![m] (C α))%T ≤ₜ ![m] (∀ₜ α, C α).
  Proof. 
    iIntros "!# %v Hτ". 
    iApply forall_intuitionistically_if. iIntros (τ).
    iApply "Hτ".
  Qed.

  Lemma ty_le_type_forall_mbang (C : sem_ty Σ → sem_ty Σ) m :
    ⊢ ![m] (∀ₜ α, C α) ≤ₜ (∀ₜ α, ![m] (C α))%T.
  Proof. 
    iIntros "!# %v Hτ".  
    iDestruct (intuitionistically_if_forall with "Hτ") as "Hτ". 
    iApply "Hτ".
  Qed.

  Lemma ty_le_mbang_row_forall (C : sem_row Σ → sem_ty Σ) m :
    ⊢ (∀ᵣ θ, ![m] (C θ))%T ≤ₜ ![m] (∀ᵣ θ, C θ).
  Proof. 
    iIntros "!# %v Hτ". 
    iApply forall_intuitionistically_if. iIntros (τ).
    iApply "Hτ".
  Qed.

  Lemma ty_le_row_forall_mbang (C : sem_row Σ → sem_ty Σ) m :
    ⊢ ![m] (∀ᵣ θ, C θ) ≤ₜ (∀ᵣ θ, ![m] (C θ))%T.
  Proof. 
    iIntros "!# %v Hτ".  
    iDestruct (intuitionistically_if_forall with "Hτ") as "Hτ". 
    iApply "Hτ".
  Qed.

  Lemma ty_le_mbang_mode_forall (C : mode → sem_ty Σ) m :
    ⊢ (∀ₘ ν, ![m] (C ν))%T ≤ₜ ![m] (∀ₘ ν, C ν).
  Proof. 
    iIntros "!# %v Hτ". 
    iApply forall_intuitionistically_if. iIntros (τ).
    iApply "Hτ".
  Qed.

  Lemma ty_le_mode_forall_mbang (C : mode → sem_ty Σ) m :
    ⊢ ![m] (∀ₘ ν, C ν) ≤ₜ (∀ₘ ν, ![m] (C ν))%T.
  Proof. 
    iIntros "!# %v Hτ".  
    iDestruct (intuitionistically_if_forall with "Hτ") as "Hτ". 
    iApply "Hτ".
  Qed.

  Corollary ty_le_uarr (τ₁ κ₁ τ₂ κ₂ : sem_ty Σ) (ρ ρ' : sem_row Σ) :
    ρ ≤ᵣ ρ' -∗
    τ₂ ≤ₜ τ₁ -∗
    κ₁ ≤ₜ κ₂ -∗
    (τ₁ -{ ρ }-> κ₁) ≤ₜ (τ₂ -{ ρ' }-> κ₂).
  Proof.
    iIntros "#Hρ  #Hτ₂₁ #Hκ₁₂". 
    iApply ty_le_mbang_comp; first iApply mode_le_refl. 
    by iApply ty_le_arr.
  Qed.
      
  Corollary ty_le_u2aarr (τ κ : sem_ty Σ) (ρ : sem_row Σ) :
    ⊢ (τ -{ ρ }-> κ) ≤ₜ (τ -{ ρ }-∘ κ).
  Proof. apply ty_le_mbang_elim. Qed.

End sub_typing.

Section row_type_sub.

  (* Subsumption relation on rows wrt to types *)
  
  Global Instance row_type_sub_multi_ty {Σ} (ρ : sem_row Σ) (τ : sem_ty Σ) `{! MultiT τ} : ρ ᵣ⪯ₜ τ.
  Proof.
    constructor.
    iIntros "%w %v %Φ !# Hρ #Hτ".
    iApply (pmono_prot_prop _ (sem_row_car ρ) with "[] Hρ").
    iIntros "!# % H". iFrame. rewrite /sem_ty_mbang /= //.
  Qed.
  
  Global Instance row_type_sub_mfbang_mbang {Σ} (m : mode) (ρ : sem_row Σ) (τ : sem_ty Σ) : ¡[ m ] ρ ᵣ⪯ₜ (![ m ] τ).
  Proof. 
    destruct m; first apply _. 
    apply row_type_sub_multi_ty. apply _.
  Qed.
  
End row_type_sub.

Section mode_type_sub.

  (* Subsumption relation on modes wrt to types *)

  Global Instance mode_type_sub_multi_ty {Σ} m (τ : sem_ty Σ) `{! MultiT τ } : m ₘ⪯ₜ τ.
  Proof. 
    constructor. iIntros "% #Hτ". 
    by iApply bi.intuitionistically_intuitionistically_if.
  Qed.

  Global Instance mode_type_sub_mbang {Σ} m (τ : sem_ty Σ) : m ₘ⪯ₜ (![m] τ).
  Proof. 
    constructor. iIntros "% Hτ". 
    iApply bi.intuitionistically_if_idemp. iApply "Hτ".
  Qed.
  
End mode_type_sub.
