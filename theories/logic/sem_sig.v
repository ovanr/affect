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

(* Universally Quantified Effect Signatures *)

(* Effect Signature *)
Definition sem_sig_eff {Σ} m (A B : sem_ty Σ -d> sem_ty Σ) : sem_sig Σ :=
  (m, >> (α : sem_ty Σ) (a : val) >> ! a {{ ▷ (A α a) }}; 
      << (b : val)                << ? b {{ ▷ (B α b) }} @m)%ieff.

Lemma sem_sig_eff_unfold {Σ} m (A B : sem_ty Σ → sem_ty Σ) `{NonExpansive A, NonExpansive B} :
  (sem_sig_eff m A B) ≡ 
    (m, >> (α : sem_ty Σ) (a : val) >> ! a {{ ▷ (A α a) }}; 
        << (b : val)                << ? b {{ ▷ (B α b) }} @m)%ieff.
Proof. rewrite {1} /sem_sig_eff //. Qed.

Lemma sem_sig_eff_unfold_1 {Σ} m (A B : sem_ty Σ → sem_ty Σ) `{NonExpansive A, NonExpansive B} :
  (sem_sig_eff m A B).1 ≡ m.
Proof. by rewrite sem_sig_eff_unfold. Qed.

Lemma sem_sig_eff_unfold_2 {Σ} m (A B : sem_ty Σ -d> sem_ty Σ) `{ NonExpansive A, NonExpansive B } :
  (sem_sig_eff m A B).2 ≡
    (>> (α : sem_ty Σ) (a : val) >> ! a {{ ▷ (A α a) }}; 
     << (b : val)                << ? b {{ ▷ (B α b) }} @m)%ieff.
Proof. by rewrite sem_sig_eff_unfold. Qed.

Lemma sem_sig_eff_unfold_iEff {Σ} m (A B : sem_ty Σ -d> sem_ty Σ) `{ NonExpansive A, NonExpansive B } v Φ:
  iEff_car (sem_sig_eff m A B).2 v Φ ⊣⊢
    iEff_car (>> (α : sem_ty Σ) (a : val) >> ! a {{ ▷ (A α a) }}; 
              << (b : val)                << ? b {{ ▷ (B α b) }} @m)%ieff v Φ.
Proof.
  assert (Hequiv :
  iEff_car (sem_sig_eff m A B).2 v Φ ⊣⊢
    iEff_car (>> (α : sem_ty Σ) (a : val) >> ! a {{ ▷ (A α a) }}; 
              << (b : val)                << ? b {{ ▷ (B α b) }} @m)%ieff v Φ).
  { f_equiv. apply non_dep_fun_equiv. by apply sem_sig_eff_unfold. }
  by rewrite Hequiv.
Qed.

Lemma sem_sig_eff_eq {Σ} m A B v Φ `{ NonExpansive A, NonExpansive B }:
  iEff_car (sem_sig_eff (Σ:=Σ) m A B).2 v Φ ⊣⊢
    (∃ α a, ⌜ a = v ⌝ ∗ ▷ (A α a) ∗ 
                        □? m (∀ b, ▷ (B α b) -∗ Φ b))%I.
Proof. 
  etrans; [by apply sem_sig_eff_unfold_iEff|]. 
  by rewrite (iEff_tele_eq' [tele _ _] [tele _]) /=. 
Qed.

(* The sem_sig_eff protocol is monotonic. *)
Global Instance sem_sig_eff_mono_prot {Σ} A B `{ NonExpansive A, NonExpansive B }:
  MonoProt (@sem_sig_eff Σ OS A B).2.
Proof.
  constructor. iIntros (???) "HΦ'".
  rewrite !sem_sig_eff_eq /=.
  iIntros "(% & % & <- & Hτ & HκΦ)".
  iExists α, a. iSplitR; first done. iFrame. simpl.
  iIntros (b) "Hκ". iApply "HΦ'". by iApply "HκΦ".
Qed.

(* The sem_sig_eff protocol is persistently monotonic. *)
Global Instance sem_sig_eff_pers_mono_prot {Σ} A B `{ NonExpansive A, NonExpansive B }:
  PersMonoProt (@sem_sig_eff Σ MS A B).2.
Proof.
  constructor. iIntros (???) "#HΦ'".
  rewrite !sem_sig_eff_eq. simpl.
  iIntros "(% & % & <- & Hτ & #HκΦ)".
  iExists α, a. iSplitR; first done. iFrame. simpl.
  iIntros "!# %b Hκ". iApply "HΦ'". by iApply "HκΦ".
Qed.

Lemma upcl_sem_sig_eff {Σ} m A B v Φ `{ NonExpansive A, NonExpansive B}:
  iEff_car (upcl m (sem_sig_eff (Σ:=Σ) m A B).2) v Φ ⊣⊢
    (∃ α a, ⌜ a = v ⌝ ∗ ▷ (A α a) ∗ 
                        □? m (∀ b, ▷ (B α b) -∗ Φ b))%I.
Proof.
  assert (Hequiv:
    iEff_car (upcl m (sem_sig_eff m A B).2) v Φ ≡ iEff_car (sem_sig_eff m A B).2 v Φ).
  { f_equiv. apply non_dep_fun_equiv. destruct m; [by rewrite upcl_id|by rewrite pers_upcl_id]. }
  rewrite Hequiv. by apply sem_sig_eff_eq.
Qed.

(* Notations. *)
Notation "'∀S:' α , τ ⇒ κ | m " := (sem_sig_eff m (λ α, τ%T) (λ α, κ%T))
  (at level 100, m, τ, κ at level 200) : sem_sig_scope.

Definition sem_sig_os {Σ} (σ : sem_sig Σ) : sem_sig Σ := (σ.1, upcl OS σ.2).
Notation "¡ σ" := (sem_sig_os σ) (at level 10) : sem_sig_scope.

(* One-Shot Signatures *)

Definition mono_prot {Σ} (Ψ : iEff Σ) : iProp Σ := 
  ∀ (v : val) (Φ Φ' : val → iPropI Σ),
              (∀ w : val, Φ w -∗ Φ' w) -∗
              (iEff_car Ψ v Φ) -∗ (iEff_car Ψ v Φ').

Class OSSig {Σ} (σ : sem_sig Σ) := { 
  monotonic_prot : (⊢ mono_prot σ.2)
}.

Lemma mono_prot_os_sig {Σ} (σ : sem_sig Σ) `{!MonoProt σ.2 }: OSSig σ.
Proof. inv MonoProt0. constructor. iIntros (v Φ Φ') "HPost Hσ". 
       iApply (monotonic_prot0 v Φ Φ' with "HPost Hσ"). 
Qed.
  
Global Instance sig_eff_os_os_sig {Σ} (A B : sem_ty Σ → sem_ty Σ) `{ NonExpansive A, NonExpansive B} : 
  OSSig (∀S: α, A α ⇒ B α | OS)%S.
Proof. 
  apply mono_prot_os_sig.
  by apply sem_sig_eff_mono_prot.
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

Lemma sig_le_eff {Σ} m₁ m₂ (ι₁ ι₂ κ₁ κ₂ : sem_ty Σ → sem_ty Σ)
  `{NonExpansive ι₁, NonExpansive ι₂, NonExpansive κ₁, NonExpansive κ₂ } :
  m₁ ≤M m₂ -∗
  □ (∀ α, (ι₁ α) ≤T (ι₂ α)) -∗
  □ (∀ α, (κ₂ α) ≤T (κ₁ α)) -∗
  (∀S: α , ι₁ α ⇒ κ₁ α | m₁) ≤S (∀S: α , ι₂ α ⇒ κ₂ α | m₂).
Proof.
  iIntros "#Hmle #Hι₁₂ #Hκ₂₁". iSplitL.
  { by rewrite !sem_sig_eff_unfold_1 /=. }
  iIntros (v Φ) "!#".
  rewrite !sem_sig_eff_eq.
  iIntros "(%α & %w & <- & Hι₁ & HκΦ₁)".
  iExists α, w; iSplitR; first done.
  iSplitL "Hι₁".
  { iApply ("Hι₁₂" with "Hι₁"). }
  simpl. destruct m₁, m₂; rewrite /mode_le; eauto; simpl.
  - iIntros (b) "Hκ₂". iApply "HκΦ₁".
    iApply ("Hκ₂₁" with "Hκ₂").
  - iDestruct "Hmle" as "[%|%]"; discriminate.
  - iIntros (b) "Hκ₂". iApply "HκΦ₁".
    iApply ("Hκ₂₁" with "Hκ₂").
  - iDestruct "HκΦ₁" as "#HκΦ₁".
    iIntros "!# %b Hκ₂". iApply "HκΦ₁".
    iApply ("Hκ₂₁" with "Hκ₂").
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
