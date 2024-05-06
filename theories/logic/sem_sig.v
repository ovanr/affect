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
    σ ≤S σ' -∗ iEff_le σ σ'.
Proof. iIntros "H". rewrite /sig_le. iApply "H". Qed.

(* Single Variable Universally Quantified Effect Signatures *)
(* Effect Signature *)
Definition sem_sig_eff {Σ} m (A B : sem_ty Σ -d> sem_ty Σ) : sem_sig Σ :=
  (>> (α : sem_ty Σ) (a : val) >> ! a {{ ▷ (A α a) }}; 
   << (b : val)                << ? b {{ ▷ (B α b) }} @m)%ieff.

Lemma sem_sig_eff_unfold {Σ} m (A B : sem_ty Σ -d> sem_ty Σ) :
  (sem_sig_eff m A B) ≡
    (>> (α : sem_ty Σ) (a : val) >> ! a {{ ▷ (A α a) }}; 
     << (b : val)                << ? b {{ ▷ (B α b) }} @m)%ieff.
Proof. by rewrite /sem_sig_eff. Qed.

Lemma sem_sig_eff_unfold_iEff {Σ} m (A B : sem_ty Σ -d> sem_ty Σ) v Φ:
  iEff_car (sem_sig_eff m A B) v Φ ⊣⊢
    iEff_car (>> (α : sem_ty Σ) (a : val) >> ! a {{ ▷ (A α a) }}; 
              << (b : val)                << ? b {{ ▷ (B α b) }} @m)%ieff v Φ.
Proof. done. Qed.

Lemma sem_sig_eff_eq {Σ} m A B v Φ :
  iEff_car (@sem_sig_eff Σ m A B) v Φ ⊣⊢
    (∃ α a, ⌜ a = v ⌝ ∗ ▷ (A α a) ∗ 
                        □? m (∀ b, ▷ (B α b) -∗ Φ b))%I.
Proof. 
  etrans; [by apply sem_sig_eff_unfold_iEff|]. 
  by rewrite (iEff_tele_eq' [tele _ _] [tele _]) /=. 
Qed.

(* The sem_sig_eff protocol is monotonic. *)
Global Instance sem_sig_eff_mono_prot {Σ} A B :
  MonoProt (@sem_sig_eff Σ OS A B).
Proof.
  constructor. iIntros (???) "HΦ'".
  rewrite !sem_sig_eff_eq /=.
  iIntros "(% & % & <- & Hτ & HκΦ)".
  iExists α, a. iSplitR; first done. iFrame. simpl.
  iIntros (b) "Hκ". iApply "HΦ'". by iApply "HκΦ".
Qed.

(* The sem_sig_eff protocol is persistently monotonic. *)
Global Instance sem_sig_eff_pers_mono_prot {Σ} A B :
  PersMonoProt (@sem_sig_eff Σ MS A B).
Proof.
  constructor. iIntros (???) "#HΦ'".
  rewrite !sem_sig_eff_eq. simpl.
  iIntros "(% & % & <- & Hτ & #HκΦ)".
  iExists α, a. iSplitR; first done. iFrame. simpl.
  iIntros "!# %b Hκ". iApply "HΦ'". by iApply "HκΦ".
Qed.

Lemma upcl_sem_sig_eff {Σ} m A B v Φ :
  iEff_car (upcl m (@sem_sig_eff Σ m A B)) v Φ ⊣⊢
    (∃ α a, ⌜ a = v ⌝ ∗ ▷ (A α a) ∗ 
                        □? m (∀ b, ▷ (B α b) -∗ Φ b))%I.
Proof.
  assert (Hequiv:
    iEff_car (upcl m (sem_sig_eff m A B)) v Φ ≡ iEff_car (sem_sig_eff m A B) v Φ).
  { f_equiv. apply non_dep_fun_equiv. destruct m; [by rewrite upcl_id|by rewrite pers_upcl_id]. }
  rewrite Hequiv. by apply sem_sig_eff_eq.
Qed.

(* Notations. *)
Notation "'∀S:' α , τ ⇒ κ | m " := (sem_sig_eff m (λ α, τ%T) (λ α, κ%T))
  (at level 100, m, τ, κ at level 200) : sem_sig_scope.

(* Multiple Variable Universally Quantified Effect Signatures *)

(* Effect Signature *)
Definition sem_sig_prot {Σ} {TT : tele} m (A B : TT → sem_ty Σ) : sem_sig Σ :=
  (>>.. (αs : TT) >> >> (a : val) >>  ! a {{ ▷ (A αs a) }}; 
                     << (b : val) <<  ? b {{ ▷ (B αs b) }} @m)%ieff.

Lemma sem_sig_prot_unfold {Σ} {TT : tele} m (A B : TT → sem_ty Σ) :
  (sem_sig_prot m A B) ≡ 
  (>>.. (αs : TT) >> >> (a : val) >> ! a {{ ▷ (A αs a) }}; 
                     << (b : val) << ? b {{ ▷ (B αs b) }} @m)%ieff.
Proof. rewrite /sem_sig_prot //. Qed.

Lemma sem_sig_prot_unfold_iEff {Σ} {TT : tele} m (A B : TT → sem_ty Σ) v Φ:
  iEff_car (sem_sig_prot m A B) v Φ ⊣⊢
    iEff_car (>>.. (αs : TT) >> >> (a : val) >> ! a {{ ▷ (A αs a) }}; 
                                << (b : val) << ? b {{ ▷ (B αs b) }} @m)%ieff v Φ.
Proof. done. Qed.

Lemma sem_sig_prot_eq {Σ} {TT : tele} m A B v Φ :
  iEff_car (@sem_sig_prot Σ TT m A B) v Φ ⊣⊢
    (∃.. αs, ∃ a, ⌜ a = v ⌝ ∗ ▷ (A αs a) ∗ 
                             □? m (∀ b, ▷ (B αs b) -∗ Φ b))%I.
Proof. 
  rewrite iEffPre_texist_eq. do 2 f_equiv.
  rewrite (iEff_tele_eq' [tele _] [tele _]) //. 
Qed.

(* The sem_sig_prot protocol is monotonic. *)
Global Instance sem_sig_prot_mono_prot {Σ} {TT : tele} A B :
  MonoProt (@sem_sig_prot Σ TT OS A B).
Proof.
  constructor. iIntros (???) "HΦ'".
  rewrite !sem_sig_prot_eq /=.
  iIntros "(% & % & <- & Hτ & HκΦ)".
  iExists αs, a. iSplitR; first done. iFrame. simpl.
  iIntros (b) "Hκ". iApply "HΦ'". by iApply "HκΦ".
Qed.

(* The sem_sig_eff protocol is persistently monotonic. *)
Global Instance sem_sig_prot_pers_mono_prot {Σ} {TT : tele} A B :
  PersMonoProt (@sem_sig_prot Σ TT MS A B).
Proof.
  constructor. iIntros (???) "#HΦ'".
  rewrite !sem_sig_prot_eq. simpl.
  iIntros "(% & % & <- & Hτ & #HκΦ)".
  iExists αs, a. iSplitR; first done. iFrame. simpl.
  iIntros "!# %b Hκ". iApply "HΦ'". by iApply "HκΦ".
Qed.

Lemma upcl_sem_sig_prot {Σ} {TT : tele} m A B v Φ :
  iEff_car (upcl m (@sem_sig_prot Σ TT m A B)) v Φ ⊣⊢
    (∃.. αs, ∃ a, ⌜ a = v ⌝ ∗ ▷ (A αs a) ∗ 
                              □? m (∀ b, ▷ (B αs b) -∗ Φ b))%I.
Proof.
  assert (Hequiv:
    iEff_car (upcl m (sem_sig_prot m A B)) v Φ ≡ iEff_car (sem_sig_prot m A B) v Φ).
  { f_equiv. apply non_dep_fun_equiv. destruct m; [by rewrite upcl_id|by rewrite pers_upcl_id]. }
  rewrite Hequiv. by apply sem_sig_prot_eq.
Qed.

(* Notations. *)
Notation "'∀S.:' x .. y , κ ⇒ ι | m" := 
  (sem_sig_prot m
  (@tele_app ((TeleS (λ x, .. (TeleS (λ y, TeleO)) ..))) (sem_ty _) (λ x, .. (λ y, κ%T) ..)) 
  (@tele_app ((TeleS (λ x, .. (TeleS (λ y, TeleO)) ..))) (sem_ty _) (λ x, .. (λ y, ι%T) ..))) 
  (at level 200, x binder, y binder, right associativity,
   format "'[ ' '∀S.:' x .. y ']' , κ ⇒ ι | m") : sem_sig_scope.

(* Notations. *)
Notation "'∀S..:' tt , κ ⇒ ι | m" := 
  (sem_sig_prot m (λ tt, κ%T) (λ tt, ι%T))
  (at level 200, tt binder, right associativity,
   format "'[ ' '∀S..:' tt , κ ⇒ ι | m ']'") : sem_sig_scope.

(* Eval cbn in (∀S.: (α : sem_ty Σ), (sem_ty_prod α α) ⇒ (sem_ty_cpy α) | OS)%S. *)

Definition sem_sig_os {Σ} (σ : sem_sig Σ) : sem_sig Σ := (upcl OS σ).
Notation "¡ σ" := (sem_sig_os σ) (at level 10) : sem_sig_scope.

(* One-Shot Signatures *)

Definition mono_prot {Σ} (Ψ : iEff Σ) : iProp Σ := 
  ∀ (v : val) (Φ Φ' : val → iPropI Σ),
              (∀ w : val, Φ w -∗ Φ' w) -∗
              (iEff_car Ψ v Φ) -∗ (iEff_car Ψ v Φ').

Class OSSig {Σ} (σ : sem_sig Σ) := { 
  monotonic_prot : (⊢ mono_prot σ)
}.

Lemma mono_prot_os_sig {Σ} (σ : sem_sig Σ) `{!MonoProt σ }: OSSig σ.
Proof. inv MonoProt0. constructor. iIntros (v Φ Φ') "HPost Hσ". 
       iApply (monotonic_prot0 v Φ Φ' with "HPost Hσ"). 
Qed.
  
Global Instance sig_eff_os_os_sig {Σ}  (A B : sem_ty Σ → sem_ty Σ) :
  OSSig (∀S: α, A α ⇒ B α | OS)%S.
Proof. 
  apply mono_prot_os_sig.
  by apply sem_sig_eff_mono_prot.
Qed.
  
Global Instance sig_prot_os_os_sig {TT : tele} {Σ} (A B : tele → sem_ty Σ) :
  OSSig (∀S.: αs, A αs ⇒ B αs | OS)%S.
Proof. 
  apply mono_prot_os_sig.
  by apply sem_sig_prot_mono_prot.
Qed.
  
Global Instance sig_os_os_sig {Σ} (σ : sem_sig Σ) : OSSig (¡ σ)%S.
Proof. 
  apply mono_prot_os_sig.
  apply upcl_mono_prot.
Qed.

(* Sub-Typing on Signatures *)

Lemma sig_le_refl {Σ} (σ : sem_sig Σ) : ⊢ σ ≤S σ.
Proof. iApply iEff_le_refl. Qed.

Lemma sig_le_trans {Σ} (σ₁ σ₂ σ₃: sem_sig Σ) : 
    σ₁ ≤S σ₂ -∗
    σ₂ ≤S σ₃ -∗
    σ₁ ≤S σ₃. 
Proof. 
  iIntros "#Hp₁₂ #Hp₂₃"; rewrite /sig_le /tc_opaque. 
  iApply iEff_le_trans; [iApply "Hp₁₂"|iApply "Hp₂₃"].
Qed.

Lemma sig_le_eff {Σ} m₁ m₂ (ι₁ ι₂ κ₁ κ₂ : sem_ty Σ → sem_ty Σ) :
  m₁ ≤M m₂ -∗
  □ (∀ α, (ι₁ α) ≤T (ι₂ α)) -∗
  □ (∀ α, (κ₂ α) ≤T (κ₁ α)) -∗
  (∀S: α , ι₁ α ⇒ κ₁ α | m₁) ≤S (∀S: α , ι₂ α ⇒ κ₂ α | m₂).
Proof.
  iIntros "#Hmle #Hι₁₂ #Hκ₂₁". 
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

Lemma sig_le_prot {Σ} {TT : tele} m₁ m₂ (ι₁ ι₂ κ₁ κ₂ : TT → sem_ty Σ) :
  m₁ ≤M m₂ -∗
  □ (∀.. α, (ι₁ α) ≤T (ι₂ α)) -∗
  □ (∀.. α, (κ₂ α) ≤T (κ₁ α)) -∗
  (∀S..: α , ι₁ α ⇒ κ₁ α | m₁) ≤S (∀S..: α , ι₂ α ⇒ κ₂ α | m₂).
Proof.
  iIntros "#Hmle #Hι₁₂ #Hκ₂₁". 
  iIntros (v Φ) "!#".
  rewrite !sem_sig_prot_eq.
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
  rewrite /sem_sig_os. 
  iIntros (v Φ) "!# Hσ". simpl.
  iExists Φ. iFrame. iIntros "% $".
Qed.

Lemma sig_le_os_elim {Σ} (σ : sem_sig Σ) `{! OSSig σ} :
  ⊢ ¡ σ ≤S σ.
Proof.
  rewrite /sem_sig_os. 
  iIntros (v Φ) "!# (%Φ' & Hσ & Himp)". simpl.
  destruct OSSig0 as []. 
  iApply (monotonic_prot0 with "Himp Hσ").
Qed.
  
Lemma sig_le_os_comp {Σ} (σ σ' : sem_sig Σ) :
  σ ≤S σ' -∗ (¡ σ) ≤S (¡ σ').
Proof.
  iIntros "#Hleσ". 
  rewrite /sig_le /sem_sig_os /tc_opaque.
  by iApply iEff_le_upcl.
Qed.
