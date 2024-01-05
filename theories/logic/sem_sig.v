(* sem_sig.v *)

(* This file contains the definition of semantic signatures. *)

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
From haffel.logic Require Import sem_def.
From haffel.logic Require Import mode.

Lemma sem_sig_to_ieff {Σ} (σ σ' : sem_sig Σ) : 
    σ ≤S σ' -∗ iEff_le σ.2 σ'.2.
Proof. iIntros "[_ $]". Qed.

(* Universally Quantified, Recursive Effect Signature *)

(* Effect Signature *)
Definition sem_sig_eff_rec_pre {Σ} m (A B : sem_sig Σ -d> sem_ty Σ -d> sem_ty Σ) (rec : sem_sig Σ) : sem_sig Σ :=
  (m, >> (α : sem_ty Σ) (a : val) >> ! a {{ ▷ (∃ rec', rec ≡ rec' ∧ A rec' α a) }}; 
      << (b : val)                << ? b {{ ▷ (∃ rec', rec ≡ rec' ∧ B rec' α b) }} @m)%ieff.

Global Instance sem_sig_eff_rec_pre_contractive {Σ} m (A B : sem_sig Σ -d> sem_ty Σ -d> sem_ty Σ) :
  Contractive (sem_sig_eff_rec_pre m A B).
Proof.
  intros ????.
  rewrite /sem_sig_eff_rec_pre iEffPre_exist_eq iEffPost_exist_eq /=. f_equiv.
  intros ??. simpl. do 3 f_equiv. rewrite iEffPre_base_eq /=.
  intros ?. simpl. do 2 f_equiv.
  { f_contractive. simpl in H. by do 4 f_equiv. }
  do 2 f_equiv. rewrite /iEffPost_exist_def. do 3 f_equiv.
  rewrite iEffPost_base_eq /iEffPost_base_def. do 2 f_equiv. f_contractive.
  simpl in H. by do 4 f_equiv.
Qed.

Definition sem_sig_eff_rec {Σ} m (A B : sem_sig Σ → sem_ty Σ → sem_ty Σ) : sem_sig Σ :=
  fixpoint (sem_sig_eff_rec_pre m A B).

Lemma sem_sig_eff_rec_unfold {Σ} m (A B : sem_sig Σ → sem_ty Σ → sem_ty Σ) `{NonExpansive2 A, NonExpansive2 B} :
  (sem_sig_eff_rec m A B) ≡ 
    (m, >> (α : sem_ty Σ) (a : val) >> ! a {{ ▷ (A (sem_sig_eff_rec m A B) α a) }}; 
        << (b : val)                << ? b {{ ▷ (B (sem_sig_eff_rec m A B) α b) }} @m)%ieff.
Proof.
  rewrite {1} /sem_sig_eff_rec fixpoint_unfold {1} /sem_sig_eff_rec_pre.
  do 6 f_equiv. 
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

Lemma sem_sig_eff_rec_unfold_1 {Σ} m (A B : sem_sig Σ → sem_ty Σ → sem_ty Σ) `{NonExpansive2 A, NonExpansive2 B} :
  (sem_sig_eff_rec m A B).1 ≡ m.
Proof. by rewrite sem_sig_eff_rec_unfold. Qed.

Lemma sem_sig_eff_rec_unfold_2 {Σ} m (A B : sem_sig Σ -d> sem_ty Σ -d> sem_ty Σ) `{ NonExpansive2 A, NonExpansive2 B } :
  (sem_sig_eff_rec m A B).2 ≡
    (>> (α : sem_ty Σ) (a : val) >> ! a {{ ▷ (A (sem_sig_eff_rec m A B) α a) }}; 
     << (b : val)                << ? b {{ ▷ (B (sem_sig_eff_rec m A B) α b) }} @m)%ieff.
Proof. by rewrite {1} sem_sig_eff_rec_unfold. Qed.

Lemma sem_sig_eff_rec_unfold_iEff {Σ} m (A B : sem_sig Σ -d> sem_ty Σ -d> sem_ty Σ) `{ NonExpansive2 A, NonExpansive2 B } v Φ:
  iEff_car (sem_sig_eff_rec m A B).2 v Φ ⊣⊢
    iEff_car (>> (α : sem_ty Σ) (a : val) >> ! a {{ ▷ (A (sem_sig_eff_rec m A B) α a) }}; 
              << (b : val)                << ? b {{ ▷ (B (sem_sig_eff_rec m A B) α b) }} @m)%ieff v Φ.
Proof.
  assert (Hequiv :
  iEff_car (sem_sig_eff_rec m A B).2 v Φ ⊣⊢
    iEff_car (>> (α : sem_ty Σ) (a : val) >> ! a {{ ▷ (A (sem_sig_eff_rec m A B) α a) }}; 
              << (b : val)                << ? b {{ ▷ (B (sem_sig_eff_rec m A B) α b) }} @m)%ieff v Φ).
  { f_equiv. apply non_dep_fun_equiv. by apply sem_sig_eff_rec_unfold. }
  by rewrite Hequiv.
Qed.

Lemma sem_sig_eff_rec_eq {Σ} m A B v Φ `{ NonExpansive2 A, NonExpansive2 B }:
  iEff_car (sem_sig_eff_rec (Σ:=Σ) m A B).2 v Φ ⊣⊢
    (∃ α a, ⌜ a = v ⌝ ∗ (▷ A (sem_sig_eff_rec m A B) α a) ∗ 
                        □? m (∀ b, (▷ B (sem_sig_eff_rec m A B) α b) -∗ Φ b))%I.
Proof. 
  etrans; [by apply sem_sig_eff_rec_unfold_iEff|]. 
  by rewrite (iEff_tele_eq' [tele _ _] [tele _]) /=. 
Qed.

(* The sem_sig_eff_rec protocol is monotonic. *)
Global Instance sem_sig_eff_rec_mono_prot {Σ} A B `{ NonExpansive2 A, NonExpansive2 B }:
  MonoProt (@sem_sig_eff_rec Σ OS A B).2.
Proof.
  constructor. iIntros (???) "HΦ'".
  rewrite !sem_sig_eff_rec_eq /=.
  iIntros "(% & % & <- & Hτ & HκΦ)".
  iExists α, a. iSplitR; first done. iFrame. simpl.
  iIntros (b) "Hκ". iApply "HΦ'". by iApply "HκΦ".
Qed.

(* The sem_sig_eff_rec protocol is persistently monotonic. *)
Global Instance sem_sig_eff_rec_pers_mono_prot {Σ} A B `{ NonExpansive2 A, NonExpansive2 B }:
  PersMonoProt (@sem_sig_eff_rec Σ MS A B).2.
Proof.
  constructor. iIntros (???) "#HΦ'".
  rewrite !sem_sig_eff_rec_eq. simpl.
  iIntros "(% & % & <- & Hτ & #HκΦ)".
  iExists α, a. iSplitR; first done. iFrame. simpl.
  iIntros "!# %b Hκ". iApply "HΦ'". by iApply "HκΦ".
Qed.

Lemma upcl_sem_sig_rec_eff {Σ} m A B v Φ `{ NonExpansive2 A, NonExpansive2 B}:
  iEff_car (upcl m (sem_sig_eff_rec (Σ:=Σ) m A B).2) v Φ ⊣⊢
    (∃ α a, ⌜ a = v ⌝ ∗ (▷ A (sem_sig_eff_rec m A B) α a) ∗ 
                        □? m (∀ b, (▷ B (sem_sig_eff_rec m A B) α b) -∗ Φ b))%I.
Proof.
  assert (Hequiv:
    iEff_car (upcl m (sem_sig_eff_rec m A B).2) v Φ ≡ iEff_car (sem_sig_eff_rec m A B).2 v Φ).
  { f_equiv. apply non_dep_fun_equiv. destruct m; [by rewrite upcl_id|by rewrite pers_upcl_id]. }
  rewrite Hequiv. by apply sem_sig_eff_rec_eq.
Qed.

(* Notations. *)
Notation "'μ∀TS:' θ , α , τ ⇒ κ | m " := (sem_sig_eff_rec m (λ θ α, τ%T) (λ θ α, κ%T))
  (at level 100, m, τ, κ at level 200) : sem_sig_scope.


Definition sem_sig_os {Σ} (σ : sem_sig Σ) : sem_sig Σ := (σ.1, upcl OS σ.2).
Notation "¡ σ" := (sem_sig_os σ) (at level 10) : sem_sig_scope.

(* One-Shot Signatures *)

Definition mono_prot {Σ} (Ψ : iEff Σ) : iProp Σ := 
  ∀ (v : val) (Φ Φ' : val → iPropI Σ),
              (∀ w : val, Φ w -∗ Φ' w) -∗
              iEff_car Ψ v Φ -∗ iEff_car Ψ v Φ'.

Class OSSig {Σ} (σ : sem_sig Σ) := { 
  monotonic_prot : (⊢ mono_prot σ.2)
}.

Lemma mono_prot_os_sig {Σ} (σ : sem_sig Σ) `{!MonoProt σ.2 }: OSSig σ.
Proof. inv MonoProt0. constructor. iIntros (v Φ Φ'). 
       iApply (monotonic_prot0 v Φ Φ'). 
Qed.
  
Global Instance sig_rec_eff_os_os_sig {Σ} (A B : sem_sig Σ → sem_ty Σ → sem_ty Σ) `{ NonExpansive2 A, NonExpansive2 B} : 
  OSSig (μ∀TS: θ, α, A θ α ⇒ B θ α | OS)%S.
Proof. 
  apply mono_prot_os_sig.
  by apply sem_sig_eff_rec_mono_prot.
Qed.
  
Global Instance sig_os_os_sig {Σ} (σ : sem_sig Σ) : OSSig (¡ σ)%S.
Proof. 
  apply mono_prot_os_sig.
  apply upcl_mono_prot.
Qed.


(* Sub-Typing on Signatures *)

Lemma sig_le_refl {Σ} (σ : sem_sig Σ) : ⊢ σ ≤S σ.
Proof. iSplit;[iApply mode_le_refl|iApply iEff_le_refl]. Qed.

Lemma sig_le_trans {Σ} (σ₁ σ₂ σ₃: sem_sig Σ) : 
    σ₁ ≤S σ₂ -∗
    σ₂ ≤S σ₃ -∗
    σ₁ ≤S σ₃. 
Proof. 
  iIntros "[#Hm₁₂ #Hp₁₂] [#Hm₂₃ #Hp₂₃]"; rewrite /sig_le /tc_opaque. 
  iSplitL.
  - by iApply mode_le_trans.
  - iApply iEff_le_trans; [iApply "Hp₁₂"|iApply "Hp₂₃"].
Qed.

Lemma sig_le_eff_rec {Σ} m₁ m₂ (ι₁ ι₂ κ₁ κ₂ : sem_sig Σ → sem_ty Σ → sem_ty Σ)
  `{NonExpansive2 ι₁, NonExpansive2 ι₂, NonExpansive2 κ₁, NonExpansive2 κ₂ } :
  m₁ ≤M m₂ -∗
  □ (∀ α σ σ', σ ≤S σ' -∗ (ι₁ σ α) ≤T (ι₂ σ' α)) -∗
  □ (∀ α σ σ', σ ≤S σ' -∗ (κ₂ σ' α) ≤T (κ₁ σ α)) -∗
  (μ∀TS: θ , α , ι₁ θ α ⇒ κ₁ θ α | m₁) ≤S (μ∀TS: θ , α , ι₂ θ α ⇒ κ₂ θ α | m₂).
Proof.
  iIntros "#Hmle #Hι₁₂ #Hκ₂₁". iLöb as "IH". iSplitL.
  { by rewrite !sem_sig_eff_rec_unfold_1 /=. }
  iIntros (v Φ) "!#".
  rewrite !sem_sig_eff_rec_eq.
  iIntros "(%α & %w & <- & Hι₁ & HκΦ₁)".
  iExists α, w; iSplitR; first done.
  iSplitL "Hι₁".
  { iNext. iApply ("Hι₁₂" with "IH Hι₁"). }
  simpl. destruct m₁, m₂; rewrite /mode_le; eauto; simpl.
  - iIntros (b) "Hκ₂". iApply "HκΦ₁".
    iNext. iApply ("Hκ₂₁" with "IH Hκ₂").
  - iDestruct "Hmle" as "[%|%]"; discriminate.
  - iIntros (b) "Hκ₂". iApply "HκΦ₁".
    iNext. iApply ("Hκ₂₁" with "IH Hκ₂").
  - iDestruct "HκΦ₁" as "#HκΦ₁".
    iIntros "!# %b Hκ₂". iApply "HκΦ₁".
    iNext. iApply ("Hκ₂₁" with "IH Hκ₂").
Qed.

Lemma sig_le_os_intro {Σ} (σ : sem_sig Σ) :
  ⊢ σ ≤S (¡ σ).
Proof.
  rewrite /sem_sig_os. iSplit; [iApply mode_le_refl|].
  iIntros (v Φ) "!# Hσ". simpl.
  iExists Φ. iFrame. iIntros "% $".
Qed.

Lemma sig_le_os_elim {Σ} (σ : sem_sig Σ) `{! OSSig σ} :
  ⊢ ¡ σ ≤S σ.
Proof.
  rewrite /sem_sig_os. iSplit; [iApply mode_le_refl|].
  iIntros (v Φ) "!# (%Φ' & Hσ & Himp)". simpl.
  destruct OSSig0 as []. 
  iApply (monotonic_prot0 with "Himp Hσ").
Qed.
  
Lemma sig_le_os_comp {Σ} (σ σ' : sem_sig Σ) :
  σ ≤S σ' -∗ (¡ σ) ≤S (¡ σ').
Proof.
  iIntros "[#Hlem #Hleσ]". 
  iSplitL "Hlem"; first done.
  by iApply iEff_le_upcl.
Qed.
