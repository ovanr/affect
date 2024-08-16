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
From affect.lib Require Import logic.
From affect.lang Require Import affect.
From affect.logic Require Import sem_def.
From affect.logic Require Import mode.

(* Universally Quantified Effect Signature *)
Program Definition sem_sig_eff {Σ} {TT : tele} : (TT -d> sem_ty Σ) -d> (TT -d> sem_ty Σ) -d> sem_sig Σ :=
  λ A B,
  @PMonoProt Σ (>>.. (αs : TT) >> >> (a : val) >> ! a {{ (A αs a) }}; 
                                  << (b : val) << ? b {{ (B αs b) }} @MS)%ieff _.
Next Obligation.
  iIntros (???????) "#HΦ". 
  rewrite ! iEffPre_texist_eq iEffPre_exist_eq /=.
  rewrite iEffPre_base_eq iEffPost_exist_eq /iEffPost_exist_def iEffPost_base_eq /iEffPost_base_def /=.
  iIntros "(%tt & % & -> & HA & HP)". iExists tt, v.
  iFrame. iSplitR; first done.
  iDestruct "HP" as "#HP"; iIntros "!>".
  iIntros "% H"; iApply "HΦ"; by iApply "HP".
Qed.

Lemma sem_sig_eff_eq {Σ} {TT : tele} A B v Φ :
  iEff_car (@sem_sig_eff Σ TT A B) v Φ ⊣⊢
    (∃.. αs, ∃ a, ⌜ a = v ⌝ ∗ (A αs a) ∗ 
                            □ (∀ b, (B αs b) -∗ Φ b))%I.
Proof. 
  rewrite iEffPre_texist_eq. do 2 f_equiv.
  rewrite (iEff_tele_eq' [tele _] [tele _]) //. 
Qed.

(* Flip-Bang Signature *)
Program Definition sem_sig_flip_mbang {Σ} (m : mode) (σ : sem_sig Σ) : sem_sig Σ := @PMonoProt Σ (upcl m σ) _.
Next Obligation.
  iIntros (??????) "#HΦ Hσ". 
  destruct m.
  - pose proof (upcl_mono_prot σ) as []. 
    iApply (monotonic_prot with "HΦ Hσ").
  - pose proof (pers_upcl_pers_mono_prot σ) as [].
    iApply (pers_monotonic_prot with "HΦ Hσ").
Qed.

(* Notations. *)
Notation "'∀S..:' tt , κ '=>' ι" := 
  (sem_sig_eff (λ tt, κ%T) (λ tt, ι%T))
  (at level 200, tt binder, right associativity,
   format "'[ ' '∀S..:' tt ,  κ  =>  ι  ']'") : sem_sig_scope.

Notation "'∀S:' x .. y , κ '=>' ι" := 
  (sem_sig_eff 
  (@tele_app ((TeleS (λ x, .. (TeleS (λ y, TeleO)) ..))) (sem_ty _) (λ x, .. (λ y, κ%T) ..)) 
  (@tele_app ((TeleS (λ x, .. (TeleS (λ y, TeleO)) ..))) (sem_ty _) (λ x, .. (λ y, ι%T) ..))) 
  (at level 200, x binder, y binder, right associativity,
   format "'[ ' '∀S:' x .. y ,  κ  =>  ι  ']'") : sem_sig_scope.

Notation "¡[ m ] σ" := (sem_sig_flip_mbang m σ) (at level 10) : sem_sig_scope.

Notation "'∀S..:' tt , κ '=[' m ']=>' ι" := 
  (sem_sig_flip_mbang m (sem_sig_eff (λ tt, κ%T) (λ tt, ι%T)))
  (at level 200, tt binder, right associativity,
   format "'[ ' '∀S..:' tt ,  κ  =[ m ]=>  ι  ']'") : sem_sig_scope.

Notation "'∀S:' x .. y , κ '=[' m ']=>' ι" := 
  (sem_sig_flip_mbang m (
    (sem_sig_eff 
    (@tele_app ((TeleS (λ x, .. (TeleS (λ y, TeleO)) ..))) (sem_ty _) (λ x, .. (λ y, κ%T) ..)) 
    (@tele_app ((TeleS (λ x, .. (TeleS (λ y, TeleO)) ..))) (sem_ty _) (λ x, .. (λ y, ι%T) ..))))) 
  (at level 200, x binder, y binder, right associativity,
   format "'[ ' '∀S:' x .. y ,  κ  =[ m ]=>  ι  ']'") : sem_sig_scope.

Lemma sem_sig_eff_mbang_eq {Σ} {TT : tele} A B m v Φ :
  iEff_car (@sem_sig_flip_mbang Σ m (@sem_sig_eff Σ TT A B)) v Φ ⊣⊢
    (∃.. αs, ∃ a, ⌜ a = v ⌝ ∗ (A αs a) ∗ 
                            □? m (∀ b, (B αs b) -∗ Φ b))%I.
Proof. 
  rewrite /sem_sig_flip_mbang /=. 
  iSplit.
  - iIntros "(%Φ' & Hσ & HPost)". rewrite sem_sig_eff_eq.
    iDestruct "Hσ" as "(%tt & % & %Heq & HA & HPost')".
    iExists tt, a. iFrame. iSplit; first done. 
    iDestruct (bi.intuitionistically_intuitionistically_if m with "HPost'") as "HPost'".
    iDestruct (bi.intuitionistically_if_sep_2 with "[HPost HPost']") as "HPosts".
    { by iSplitL "HPost". }
    iApply (bi.intuitionistically_if_mono with "HPosts"). 
    iIntros "[H1 H2] % HB". iApply "H1". by iApply "H2".
  - iIntros "(%tt & % & %Heq & HA & HPost')".
    iExists (λ b, B tt b). iFrame. rewrite sem_sig_eff_eq.
    iExists tt, a. iFrame; iSplit; eauto.
Qed.

Section sig_properties.

Global Instance sem_sig_eff_ne2 {Σ} {TT : tele} :
  NonExpansive2 (@sem_sig_eff Σ TT).
Proof.
  iIntros (???????). rewrite /sem_sig_eff.
  intros ??. apply pmono_prot_distI. 
  intros ??. rewrite ! iEffPre_texist_eq /=. 
  f_equiv. intros ?.
  rewrite ! iEffPre_exist_eq /=. 
  f_equiv. intros ?. f_equiv. apply non_dep_fun_dist. do 2 f_equiv.
  { apply non_dep_fun_dist. f_equiv. }
  f_equiv. intros ?. 
  rewrite iEffPost_base_eq /iEffPost_base_def. intros ?.
  f_equiv. apply non_dep_fun_dist. f_equiv.
Qed.

Global Instance sem_sig_eff_ne {Σ} {TT : tele} A :
  NonExpansive (@sem_sig_eff Σ TT A).
Proof. iIntros (????). by f_equiv. Qed.

Global Instance sem_sig_eff_alt_ne {Σ} {TT : tele} :
  NonExpansive (@sem_sig_eff Σ TT).
Proof. iIntros (?????). by f_equiv. Qed.

Global Instance sem_sig_eff_pers_mono_prot {Σ} {TT : tele} A B :
  PersMonoProt (@sem_sig_eff Σ TT A B).
Proof. constructor. iApply pmono_prot_prop. Qed.

Lemma upcl_sem_sig_eff {Σ} {TT : tele} A B v Φ :
  iEff_car (upcl MS (@sem_sig_eff Σ TT A B)) v Φ ⊣⊢
    (∃.. αs, ∃ a, ⌜ a = v ⌝ ∗ (A αs a) ∗ □ (∀ b, (B αs b) -∗ Φ b))%I.
Proof.
  assert (Hequiv: iEff_car (upcl MS (sem_sig_eff A B)) v Φ ≡ iEff_car (sem_sig_eff A B) v Φ).
  { f_equiv. apply non_dep_fun_equiv. by rewrite pers_upcl_id. }
  rewrite Hequiv. by apply sem_sig_eff_eq.
Qed.

Global Instance sem_sig_flip_mbang_mono_prot {Σ} σ :
  MonoProt (@sem_sig_flip_mbang Σ OS σ).
Proof. constructor. apply upcl_mono_prot. Qed.

Global Instance sem_sig_flip_mbang_ne {Σ} m : NonExpansive (@sem_sig_flip_mbang Σ m).
Proof.
  rewrite /sem_sig_flip_mbang. 
  intros ?????.
  apply non_dep_fun_dist. simpl.
  intros ??. apply non_dep_fun_dist. simpl.
  intros ?. do 3 f_equiv. apply non_dep_fun_dist.
  by apply iEff_car_ne.
Qed.

Global Instance sem_sig_flip_mbang_proper {Σ} m : Proper ((≡) ==> (≡)) (@sem_sig_flip_mbang Σ m).
Proof. apply ne_proper. apply _. Qed.

End sig_properties.

Section once_sig.

  (* Once Constraint *)
  
  Class OnceS {Σ} (σ : sem_sig Σ) := {
    sig_le_mfbang_elim : (⊢ (¡[ OS ] σ) ≤ₛ σ)
  }.

End once_sig.

Section sig_sub_typing.

  (* Subtyping on Signatures *)
  
  Lemma sig_le_refl {Σ} (σ : sem_sig Σ) : ⊢ σ ≤ₛ σ.
  Proof. iApply iEff_le_refl. Qed.
  
  Lemma sig_le_trans {Σ} (σ₁ σ₂ σ₃: sem_sig Σ) : 
      σ₁ ≤ₛ σ₂ -∗
      σ₂ ≤ₛ σ₃ -∗
      σ₁ ≤ₛ σ₃. 
  Proof. 
    iIntros "#Hp₁₂ #Hp₂₃"; rewrite /sig_le /tc_opaque. 
    iApply iEff_le_trans; [iApply "Hp₁₂"|iApply "Hp₂₃"].
  Qed.
  
  Lemma sig_le_eff {Σ} {TT : tele} (ι₁ ι₂ κ₁ κ₂ : tele_arg TT → sem_ty Σ) :
    □ (∀.. α, (ι₁ α) ≤ₜ (ι₂ α)) -∗
    □ (∀.. α, (κ₂ α) ≤ₜ (κ₁ α)) -∗
    (∀S..: α , ι₁ α => κ₁ α) ≤ₛ (∀S..: α , ι₂ α => κ₂ α).
  Proof.
    iIntros "#Hι₁₂ #Hκ₂₁". 
    iIntros (v Φ) "!#".
    rewrite !sem_sig_eff_eq.
    iIntros "(%α & %w & <- & Hι₁ & HκΦ₁)".
    iExists α, w; iSplitR; first done.
    iSplitL "Hι₁".
    { iApply ("Hι₁₂" with "Hι₁"). }
    simpl. iDestruct "HκΦ₁" as "#HκΦ₁".
    iIntros "!# %b Hκ₂". iApply "HκΦ₁".
    iApply ("Hκ₂₁" with "Hκ₂").
  Qed.
  
  Lemma sig_le_mfbang_intro {Σ} m (σ : sem_sig Σ) :
    ⊢ σ ≤ₛ (¡[ m ] σ).
  Proof.
    rewrite /sem_sig_flip_mbang. 
    iIntros (v Φ) "!# Hσ". simpl.
    iExists Φ. iFrame. simpl. 
    iApply bi.intuitionistically_intuitionistically_if.
    iIntros "!# % $".
  Qed.
  
  Lemma sig_le_mfbang_elim_ms {Σ} (σ : sem_sig Σ) :
    ⊢ (¡[ MS ] σ) ≤ₛ σ.
  Proof.
    rewrite /sem_sig_flip_mbang. 
    iIntros (v Φ) "!# (%Φ' & Hσ & HPost)". simpl.
    by iApply (@pmono_prot_prop Σ σ with "HPost").
  Qed.
  
  Lemma sig_le_mfbang_comp {Σ} (m m' : mode) (σ σ' : sem_sig Σ) :
    m' ≤ₘ m -∗ σ ≤ₛ σ' -∗ 
    (¡[ m ] σ) ≤ₛ (¡[ m' ] σ').
  Proof.
    iIntros "#Hlem #Hleσ". destruct m.
    - iDestruct (mode_le_OS_inv with "Hlem") as "->".
      rewrite /sig_le /sem_sig_flip_mbang /tc_opaque.
      by iApply iEff_le_upcl.
    - iApply sig_le_trans; first iApply sig_le_mfbang_elim_ms. 
      iApply sig_le_trans; first iApply (sig_le_mfbang_intro m').
      rewrite /sig_le /sem_sig_flip_mbang /tc_opaque.
      by iApply iEff_le_upcl.
  Qed.
  
  Lemma sig_le_mfbang_idemp {Σ} m (σ : sem_sig Σ) :
    ⊢ (¡[ m ] (¡[ m ] σ)) ≤ₛ ((¡[ m ] σ)).
  Proof. 
    iIntros (v Φ) "!# (%Φ' & (%Φ'' & H & HPost') & HPost)". 
    rewrite /sem_sig_flip_mbang /=.
    iDestruct (bi.intuitionistically_if_sep_2 with "[HPost HPost']") as "HP"; first iFrame.
    iExists Φ''. iFrame.
    iApply (bi.intuitionistically_if_mono with "HP").
    iIntros "[H1 H2] % HΦ''". iApply ("H2" with "[H1 HΦ'']"). 
    by iApply "H1".
  Qed.

  Global Instance sig_fbang_once_sig {Σ} (σ : sem_sig Σ) : OnceS (¡[ OS ] σ)%S.
  Proof. constructor. iIntros. iApply sig_le_mfbang_idemp. Qed.

  Global Instance sig_eff_os_once {TT : tele} {Σ} (A B : tele_arg TT → sem_ty Σ) :
    OnceS (∀S..: αs , (A αs) =[ OS ]=> (B αs))%S.
  Proof. apply _. Qed.
  
  Lemma sig_le_mfbang_comm {Σ} m m' (σ : sem_sig Σ) :
    ⊢ (¡[ m ] (¡[ m' ] σ)) ≤ₛ (¡[ m' ] (¡[ m ] σ)).
  Proof. 
    destruct m, m'.
    - iApply sig_le_refl.
    - iApply sig_le_trans; first iApply sig_le_mfbang_comp.
      { iApply mode_le_refl. }
      { iApply sig_le_mfbang_elim_ms. }
      iApply sig_le_mfbang_intro.
    - iApply sig_le_trans; first iApply sig_le_mfbang_elim_ms.
      iApply sig_le_mfbang_comp; first iApply mode_le_refl. 
      iApply sig_le_mfbang_intro.
    - iApply sig_le_refl.
  Qed.
  
  Corollary sig_le_eff_mode {Σ} {TT : tele} (ι κ : tele_arg TT → sem_ty Σ) :
    ⊢ (∀S..: α , ι α =[ MS ]=> κ α) ≤ₛ (∀S..: α , ι α =[ OS ]=> κ α).
  Proof. 
    iApply sig_le_mfbang_comp; first iApply mode_le_MS. 
    iApply sig_le_refl. 
  Qed.

End sig_sub_typing.
