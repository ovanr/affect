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

(* Universally Quantified Effect Signatures *)

(* Effect Signature *)
Program Definition sem_sig_eff {Σ} {TT : tele} m (A B : TT → sem_ty Σ) : sem_sig Σ :=
  @SemSig Σ (>>.. (αs : TT) >> >> (a : val) >>  ! a {{ ▷ (A αs a) }}; 
                            << (b : val) <<  ? b {{ ▷ (B αs b) }} @m)%ieff _.
Next Obligation.
  iIntros (????????) "#HΦ". 
  rewrite ! iEffPre_texist_eq iEffPre_exist_eq /=.
  rewrite iEffPre_base_eq iEffPost_exist_eq /iEffPost_exist_def iEffPost_base_eq /iEffPost_base_def /=.
  iIntros "(%tt & % & -> & HA & HP)". iExists tt, v.
  iFrame. iSplitR; first done.
  destruct m; simpl; 
    last (iDestruct "HP" as "#HP"; iIntros "!>");
    iIntros "% H"; iApply "HΦ"; by iApply "HP".
Qed.

Lemma sem_sig_eff_eq {Σ} {TT : tele} m A B v Φ :
  iEff_car (@sem_sig_eff Σ TT m A B) v Φ ⊣⊢
    (∃.. αs, ∃ a, ⌜ a = v ⌝ ∗ ▷ (A αs a) ∗ 
                             □? m (∀ b, ▷ (B αs b) -∗ Φ b))%I.
Proof. 
  rewrite iEffPre_texist_eq. do 2 f_equiv.
  rewrite (iEff_tele_eq' [tele _] [tele _]) //. 
Qed.

(* The sem_sig_eff protocol is monotonic. *)
Global Instance sem_sig_eff_mono_prot {Σ} {TT : tele} A B :
  MonoProt (@sem_sig_eff Σ TT OS A B).
Proof.
  constructor. iIntros (???) "HΦ'".
  rewrite !sem_sig_eff_eq /=.
  iIntros "(% & % & <- & Hτ & HκΦ)".
  iExists αs, a. iSplitR; first done. iFrame. simpl.
  iIntros (b) "Hκ". iApply "HΦ'". by iApply "HκΦ".
Qed.

(* The sem_sig_eff protocol is persistently monotonic. *)
Global Instance sem_sig_eff_pers_mono_prot {Σ} {TT : tele} A B :
  PersMonoProt (@sem_sig_eff Σ TT MS A B).
Proof.
  constructor. iIntros (???) "#HΦ'".
  rewrite !sem_sig_eff_eq. simpl.
  iIntros "(% & % & <- & Hτ & #HκΦ)".
  iExists αs, a. iSplitR; first done. iFrame. simpl.
  iIntros "!# %b Hκ". iApply "HΦ'". by iApply "HκΦ".
Qed.

Lemma upcl_sem_sig_eff {Σ} {TT : tele} m A B v Φ :
  iEff_car (upcl m (@sem_sig_eff Σ TT m A B)) v Φ ⊣⊢
    (∃.. αs, ∃ a, ⌜ a = v ⌝ ∗ ▷ (A αs a) ∗ 
                              □? m (∀ b, ▷ (B αs b) -∗ Φ b))%I.
Proof.
  assert (Hequiv:
    iEff_car (upcl m (sem_sig_eff m A B)) v Φ ≡ iEff_car (sem_sig_eff m A B) v Φ).
  { f_equiv. apply non_dep_fun_equiv. destruct m; [by rewrite upcl_id|by rewrite pers_upcl_id]. }
  rewrite Hequiv. by apply sem_sig_eff_eq.
Qed.

(* Notations. *)
Notation "'∀S..:' tt , κ '=[' m ']=>' ι" := 
  (sem_sig_eff m (λ tt, κ%T) (λ tt, ι%T))
  (at level 200, tt binder, right associativity,
   format "'[ ' '∀S..:' tt ,  κ  =[ m ]=>  ι  ']'") : sem_sig_scope.

Notation "'∀S:' x .. y , κ '=[' m ']=>' ι" := 
  (sem_sig_eff m
  (@tele_app ((TeleS (λ x, .. (TeleS (λ y, TeleO)) ..))) (sem_ty _) (λ x, .. (λ y, κ%T) ..)) 
  (@tele_app ((TeleS (λ x, .. (TeleS (λ y, TeleO)) ..))) (sem_ty _) (λ x, .. (λ y, ι%T) ..))) 
  (at level 200, x binder, y binder, right associativity,
   format "'[ ' '∀S:' x .. y ,  κ  =[ m ]=>  ι  ']'") : sem_sig_scope.

(* Eval cbn in (∀S.: (α : sem_ty Σ), (sem_ty_prod α α) =[ OS ]=> (sem_ty_cpy α))%S. *)

Program Definition sem_sig_os {Σ} (σ : sem_sig Σ) : sem_sig Σ := @SemSig Σ (upcl OS σ) _.
Next Obligation.
  iIntros (?????) "#HΦ Hσ". 
  pose proof (upcl_mono_prot σ) as []. 
  iApply (monotonic_prot with "HΦ Hσ").
Qed.

Notation "¡ σ" := (sem_sig_os σ) (at level 10) : sem_sig_scope.

Global Instance sem_sig_os_ne {Σ} : NonExpansive (@sem_sig_os Σ).
Proof.
  intros ????. rewrite /sem_sig_os. intros ?.
  apply non_dep_fun_dist. simpl.
  intros ??. apply non_dep_fun_dist. simpl.
  intros ?. do 3 f_equiv. apply non_dep_fun_dist.
  by apply iEff_car_ne.
Qed.

Global Instance sem_sig_os_proper {Σ} : Proper ((≡) ==> (≡)) (@sem_sig_os Σ).
Proof. apply ne_proper. apply _. Qed.

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
  
Global Instance sig_eff_os_os_sig {TT : tele} {Σ} (A B : tele_arg TT → sem_ty Σ) :
  OSSig (∀S..: αs , (A αs) =[ OS ]=> (B αs))%S.
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
Proof. iApply iEff_le_refl. Qed.

Lemma sig_le_trans {Σ} (σ₁ σ₂ σ₃: sem_sig Σ) : 
    σ₁ ≤S σ₂ -∗
    σ₂ ≤S σ₃ -∗
    σ₁ ≤S σ₃. 
Proof. 
  iIntros "#Hp₁₂ #Hp₂₃"; rewrite /sig_le /tc_opaque. 
  iApply iEff_le_trans; [iApply "Hp₁₂"|iApply "Hp₂₃"].
Qed.

Lemma sig_le_eff {Σ} {TT : tele} m₁ m₂ (ι₁ ι₂ κ₁ κ₂ : tele_arg TT → sem_ty Σ) :
  m₁ ≤M m₂ -∗
  □ (∀.. α, (ι₁ α) ≤T (ι₂ α)) -∗
  □ (∀.. α, (κ₂ α) ≤T (κ₁ α)) -∗
  (∀S..: α , ι₁ α =[ m₁ ]=> κ₁ α) ≤S (∀S..: α , ι₂ α =[ m₂ ]=> κ₂ α).
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

Lemma sig_le_eff_mode {Σ} {TT : tele} (ι κ : tele_arg TT → sem_ty Σ) :
  ⊢ (∀S..: α , ι α =[ MS ]=> κ α) ≤S (∀S..: α , ι α =[ OS ]=> κ α).
Proof. iApply sig_le_eff; first iApply mode_le_MS; iIntros "!# % % !# $". Qed.

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
