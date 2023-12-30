
(* sem_types.v *)

(* This file contains the definition of semantic types,
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
From haffel.lang Require Import haffel.
From haffel.lang Require Import subst_map.
From haffel.logic Require Import iEff.
From haffel.logic Require Import sem_def.
From haffel.logic Require Import sem_sig.
From haffel.logic Require Import ewpw.

(* Base types. *)
Definition sem_ty_void {Σ} : sem_ty Σ := (λ v, False)%I.
Definition sem_ty_unit {Σ} : sem_ty Σ := (λ v, ⌜ v = #() ⌝)%I.
Definition sem_ty_bool {Σ} : sem_ty Σ := (λ v, ∃ b : bool, ⌜ v = #b ⌝)%I.
Definition sem_ty_int {Σ} : sem_ty Σ := (λ v, ∃ n : Z, ⌜ v = #n ⌝)%I.
Definition sem_ty_moved {Σ} : sem_ty Σ := (λ v, True)%I.

Definition sem_ty_cpy {Σ} (τ : sem_ty Σ) : sem_ty Σ := (λ v, □ τ v)%I.

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
Definition sem_ty_aarr `{heapGS Σ}
  (ρ : sem_row Σ)
  (τ : sem_ty Σ)
  (κ : sem_ty Σ) : sem_ty Σ :=
  (λ (v : val),
    ∀ (w : val),
      τ w -∗
      EWPW (v w) <| ρ |> {{ u, κ u }})%I.

(* Unrestricted Arrow type. *)
Definition sem_ty_uarr `{heapGS Σ} 
  (ρ : sem_row Σ)
  (τ : sem_ty Σ)
  (κ : sem_ty Σ) : sem_ty Σ :=
  (λ (v : val), □ (
    ∀ (w : val),
      τ w -∗ 
      EWPW (v w) <| ρ |> {{ u, κ u}}))%I.

(* Polymorphic type. *)
Definition sem_ty_forall `{heapGS Σ} 
    (C : sem_ty Σ → sem_ty Σ) : sem_ty Σ := 
    (λ v, ∀ τ, □ EWPW (v <_>)%E {{ v, C τ v }})%I.

(* Polymorphic effect type. *)
Definition sem_ty_row_forall `{heapGS Σ} 
  (A : sem_row Σ → sem_ty Σ) : sem_ty Σ := 
    (λ v, ∀ θ, □ EWPW (v <_>)%E {{ v, A θ v }})%I.

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

Notation "'∀T:' α , C " := (sem_ty_forall (λ α, C%T)) 
  (at level 180) : sem_ty_scope.

Notation "'∀R:' θ , C " := (sem_ty_row_forall (λ θ, C%T)) 
  (at level 180) : sem_ty_scope.

Notation "'∃:' α , C " := (sem_ty_exists (λ α, C%T)) 
  (at level 180) : sem_ty_scope.

Notation "'μT:' α , C " := (sem_ty_rec (λ α, C%T))
  (at level 180) : sem_ty_scope.

Notation "τ '-{' ρ '}-∘' κ" := (sem_ty_aarr ρ%R τ%T κ%T)
  (at level 100, ρ, κ at level 200) : sem_ty_scope.
Notation "τ ⊸ κ" := (sem_ty_aarr ⊥ τ%T κ%T)
  (at level 99, κ at level 200) : sem_ty_scope.

Notation "τ '-{' ρ '}->' κ" := (sem_ty_uarr ρ%R τ%T κ%T)
  (at level 100, ρ, κ at level 200) : sem_ty_scope.
Notation "τ → κ" := (sem_ty_uarr ⊥ τ%T κ%T)
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

  Implicit Types σ : sem_sig Σ.

  Ltac solve_non_expansive :=
    repeat intros ?;
    unfold sem_ty_unit, sem_ty_int, sem_ty_bool, sem_ty_cpy,
           sem_ty_prod, sem_ty_sum, sem_ty_aarr,
           sem_ty_uarr, sem_ty_ref, sem_ty_ref_cpy, 
           sem_ty_rec, sem_ty_list, sem_ty_forall, sem_ty_exists;
    repeat (f_equiv || done || intros ? || by apply non_dep_fun_dist).

  Global Instance sem_ty_cpy_ne : NonExpansive (@sem_ty_cpy Σ).
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

  Global Instance sem_ty_forall_ne n :
    Proper (pointwise_relation _ (dist n) ==> dist n) sem_ty_forall.
  Proof. intros ????. unfold sem_ty_forall. 
         do 3 f_equiv. f_equiv. by apply non_dep_fun_dist.
  Qed.

  Global Instance sem_ty_forall_row_ne n :
    Proper (pointwise_relation _ (dist n) ==> dist n) sem_ty_row_forall.
  Proof. intros ????. unfold sem_ty_row_forall. 
         do 3 f_equiv. f_equiv. by apply non_dep_fun_dist.
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

  Global Instance sem_ty_cpy_proper : Proper ((≡) ==> (≡)) (@sem_ty_cpy Σ).
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

  Global Instance sem_ty_forall_proper :
    Proper (pointwise_relation _ (≡) ==> (≡)) sem_ty_forall.
  Proof. 
    intros ????. unfold sem_ty_forall; repeat f_equiv. 
    by apply non_dep_fun_equiv. 
  Qed.

  Global Instance sem_ty_sig_forall_proper :
    Proper (pointwise_relation _ (≡) ==> (≡)) sem_ty_row_forall.
  Proof. 
    intros ????. unfold sem_ty_row_forall; repeat f_equiv. 
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

End types_properties.

Section sub_typing.

  Context `{!heapGS Σ}.

  Lemma ty_le_refl (τ : sem_ty Σ) : ⊢ τ ≤T τ.
  Proof. iIntros "!# % $". Qed.
  
  Lemma ty_le_trans (τ₁ τ₂ τ₃ : sem_ty Σ) :
    τ₁ ≤T τ₂ -∗
    τ₂ ≤T τ₃ -∗
    τ₁ ≤T τ₃.
  Proof. 
    iIntros "#Hτ₁₂ #Hτ₂₃ !# %v Hτ₁". 
    iApply "Hτ₂₃". by iApply "Hτ₁₂".
  Qed.
  
  Lemma ty_le_void (τ : sem_ty Σ) :
    ⊢ Void ≤T τ.
  Proof. iIntros "% !# []". Qed.

  Lemma ty_le_cpy_intro (τ : sem_ty Σ) :
    copy_ty τ -∗
    τ ≤T '! τ.
  Proof. 
    iIntros "#Hcpy !# %v Hτ". 
    iDestruct ("Hcpy" with "Hτ") as "#Hτ'".
    iIntros "!# {$#Hτ'}". 
  Qed.
        
  Lemma ty_le_cpy_elim (τ : sem_ty Σ) :
    ⊢ ('! τ) ≤T τ.
  Proof. iIntros "!# %v #$". Qed.

  Lemma ty_le_cpy_comp (τ τ' : sem_ty Σ) :
    τ ≤T τ' -∗ ('! τ) ≤T ('! τ').
  Proof. 
    iIntros "#Hττ' !# %v #H!τ !#". 
    by iApply "Hττ'".
  Qed.

  Lemma ty_le_u2aarr (τ κ : sem_ty Σ) (ρ : sem_row Σ) :
    ⊢ (τ -{ ρ }-> κ) ≤T (τ -{ ρ }-∘ κ).
  Proof.
    iIntros "!# %v #Hτκ". iIntros (w) "Hτ /=".
    by iApply "Hτκ".
  Qed.

  Lemma ty_le_aarr (τ₁ κ₁ τ₂ κ₂ : sem_ty Σ) (ρ ρ' : sem_row Σ) :
    ρ ≤R ρ' -∗
    τ₂ ≤T τ₁ -∗
    κ₁ ≤T κ₂ -∗
    (τ₁ -{ ρ }-∘ κ₁) ≤T (τ₂ -{ ρ' }-∘ κ₂).
  Proof.
    iIntros "#Hρ  #Hτ₂₁ #Hκ₁₂ !# %v Hτκ₁ %w Hτ₂".
    iApply (ewpw_sub with "Hρ").
    iApply (ewpw_mono with "[Hτκ₁ Hτ₂]").
    { iApply ("Hτκ₁" with "[Hτ₂]"); by iApply "Hτ₂₁". }
    iIntros "!# % Hκ !>". by iApply "Hκ₁₂".
  Qed.
  
  Lemma ty_le_uarr (τ₁ κ₁ τ₂ κ₂ : sem_ty Σ) (ρ ρ' : sem_row Σ) :
    ρ ≤R ρ' -∗
    τ₂ ≤T τ₁ -∗
    κ₁ ≤T κ₂ -∗
    (τ₁ -{ ρ }-> κ₁) ≤T (τ₂ -{ ρ' }-> κ₂).
  Proof.
    iIntros "#Hρ #Hτ₂₁ #Hκ₁₂ !# %v #Hτκ₁ %w !# Hτ₂".
    iApply (ewpw_sub with "Hρ").
    iApply (ewpw_mono with "[Hτκ₁ Hτ₂]").
    { iApply ("Hτκ₁" with "[Hτ₂]"); by iApply "Hτ₂₁". }
    iIntros "!# % Hκ !>". by iApply "Hκ₁₂".
  Qed.
  
  Lemma ty_le_ref (τ₁ τ₂ : sem_ty Σ) :
    τ₁ ≤T τ₂ -∗
    (Ref τ₁) ≤T (Ref τ₂).
  Proof.
    iIntros "#Hτ₁₂ !# %v (%l & -> & (%w & Hl & Hτw))".
    iExists l. iSplit; first done.
    iExists w. iFrame. by iApply "Hτ₁₂".
  Qed.

  Lemma ty_le_prod (τ₁ τ₂ κ₁ κ₂ : sem_ty Σ) :
    τ₁ ≤T τ₂ -∗
    κ₁ ≤T κ₂ -∗
    (τ₁ × κ₁) ≤T (τ₂ × κ₂).
  Proof.
    iIntros "#Hτ₁₂ #Hκ₁₂ !# %v (%w₁ & %w₂ & -> &Hw₁ & Hw₂)".
    iExists w₁, w₂. iSplit; first done. iSplitL "Hw₁".
    { by iApply "Hτ₁₂". }
    by iApply "Hκ₁₂".
  Qed.
  
  Lemma ty_le_sum (τ₁ τ₂ κ₁ κ₂ : sem_ty Σ) :
    τ₁ ≤T τ₂ -∗
    κ₁ ≤T κ₂ -∗
    (τ₁ + κ₁) ≤T (τ₂ + κ₂).
  Proof.
    iIntros "#Hτ₁₂ #Hκ₁₂ !# %v (%v' & [(-> & Hτ₁)|(-> & Hκ₁)])"; iExists v'. 
    - iLeft. iSplit; first done. by iApply "Hτ₁₂".
    - iRight. iSplit; first done. by iApply "Hκ₁₂". 
  Qed.

  Lemma ty_le_option (τ₁ τ₂ : sem_ty Σ) :
    τ₁ ≤T τ₂ -∗
    (Option τ₁) ≤T (Option τ₂).
  Proof. iIntros "#?". iApply ty_le_sum; last done. iIntros "!# % $". Qed.

  Lemma ty_le_forall (τ₁ τ₂ : sem_ty Σ → sem_ty Σ) :
    (∀ α, τ₁ α ≤T τ₂ α) -∗
    (∀T: α, τ₁ α)%T ≤T (∀T: α, τ₂ α).
  Proof.
    iIntros "#Hτ₁₂ !# %v #Hτ₁ %τ !#".
    iApply (ewpw_mono with "[Hτ₁]"); [iApply "Hτ₁"|].
    iIntros "!# % Hτ !>". by iApply "Hτ₁₂".
  Qed.

  Lemma ty_le_sig_forall (τ₁ τ₂ : sem_row Σ → sem_ty Σ) :
    (∀ θ, τ₁ θ ≤T τ₂ θ) -∗
    (∀R: θ, τ₁ θ) ≤T (∀R: θ, τ₂ θ).
  Proof.
    iIntros "#Hτ₁₂ !# %v #Hτ₁ %σ !#".
    iApply (ewpw_mono with "[Hτ₁]"); [iApply "Hτ₁"|].
    iIntros "!# % Hτ₁σ !>".
    iApply ("Hτ₁₂" $! σ with "Hτ₁σ").
  Qed.

  Lemma ty_le_exists (τ₁ τ₂ : sem_ty Σ → sem_ty Σ) :
    (∀ α, τ₁ α ≤T τ₂ α) -∗
    (∃: α, τ₁ α) ≤T (∃: α, τ₂ α).
  Proof.
    iIntros "#Hτ₁₂ !# %v (%α & Hα) //=".
    iExists α. by iApply "Hτ₁₂".
  Qed.

  Lemma ty_le_rec (τ₁ τ₂ : sem_ty Σ -> sem_ty Σ) `{NonExpansive τ₁, NonExpansive τ₂} :
    □ (∀ α α', (α ≤T α') -∗ τ₁ α ≤T τ₂ α') -∗
    (μT: α, τ₁ α) ≤T (μT: α, τ₂ α).
  Proof.
    iIntros "#Hτ₁₂ !#". iLöb as "IH". iIntros "%v Hτ₁".
    iApply sem_ty_rec_unfold.
    rewrite sem_ty_rec_unfold. iNext.
    iApply ("Hτ₁₂" with "[] Hτ₁").
    rewrite /ty_le /tc_opaque. iApply "IH".
  Qed.

  Lemma ty_le_list (τ₁ τ₂ : sem_ty Σ) :
    τ₁ ≤T τ₂ -∗
    List τ₁ ≤T List τ₂.
  Proof.
    iIntros "#Hτ₁₂ !# %v HLτ₁". unfold sem_ty_list.
    iLöb as "IH" forall (v).
    iApply sem_ty_rec_unfold.
    rewrite sem_ty_rec_unfold. iNext.
    iDestruct "HLτ₁" as "(%v' & [(-> & Hunit)|(-> & (%w₁ & %w₂ & -> & Hτ₁ & Hμ))])".
    { iExists v'; iLeft. by iFrame. }
    iExists (w₁, w₂)%V. iRight. iSplit; first done.
    iExists w₁, w₂; iSplit; first done.
    iSplitL "Hτ₁"; [by iApply "Hτ₁₂"|by iApply "IH"].
  Qed.
  
End sub_typing.

