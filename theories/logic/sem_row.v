
(* sem_row.v *)

(* This file contains the definition of semantic rows. *)

From iris.proofmode Require Import base tactics.
From iris.algebra Require Import ofe gmap.
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
From affect.logic Require Import sem_sig.

Program Definition sem_row_nil {Σ} : sem_row Σ := @SemRow Σ ⊥ _. 
Next Obligation. iIntros (???) "[]". Qed.
Global Instance sem_row_bottom {Σ} : Bottom (sem_row Σ) := sem_row_nil.

Program Definition sem_row_cons {Σ} (op : operation) : sem_sig Σ -d> sem_row Σ -d> sem_row Σ :=
    λ σ ρ, (@SemRow Σ (@PMonoProt Σ (IEff 
              (λ v, λne Φ, ∃ (op' : operation) (v' : val), 
                           ⌜ v = (effect op', v')%V ⌝ ∗
                            if decide (op = op') then 
                                ▷ (iEff_car σ v' Φ)
                            else
                                iEff_car ρ (effect op', v')%V Φ)%I) _) _).
Next Obligation. 
  intros ?????????. repeat f_equiv; last done. simpl. 
  destruct a0; by repeat f_equiv. 
Qed.
Next Obligation. 
  iIntros (???????) "#HPost (%op' & %v' & -> & H)". simpl.
  iExists op', v'. iSplit; first done.
  destruct (decide (op = op')).
  - iApply (pmono_prot_prop Σ σ with "HPost H").
  - iApply (pmono_prot_prop Σ ρ with "HPost H").
Qed.
Next Obligation.
  iIntros (??????) "(%op' & %v' & -> & H)". by iExists op', v'.
Qed.

Program Definition sem_row_flip_bang {Σ} (ρ : sem_row Σ) : sem_row Σ := 
  @SemRow Σ (@PMonoProt Σ (upcl OS ρ) _) _.
Next Obligation.
  iIntros (?????) "#HΦ Hσ".
  pose proof (upcl_mono_prot ρ) as []. 
  iApply (monotonic_prot with "HΦ Hσ").
Qed.
Next Obligation.
  iIntros (????) "(%Φ' & Hρ & _)".
  iApply (sem_row_prop _ ρ with "Hρ").
Qed.

(* generalised flip-bang row *)
Notation "¡_[ m ] ρ" := (
  match m with
      OS => sem_row_flip_bang ρ
    | MS => ρ
  end) (at level 10) : sem_row_scope.

Definition sem_row_rec {Σ} (R : sem_row Σ → sem_row Σ) `{Contractive R} : sem_row Σ :=
  fixpoint R.

Lemma sem_row_rec_unfold {Σ} (R : sem_row Σ → sem_row Σ) `{Contractive R} :
  sem_row_rec R ≡ R (sem_row_rec R).
Proof. rewrite /sem_row_rec {1} fixpoint_unfold //. Qed.

Lemma sem_row_rec_unfold_iEff {Σ} (R : sem_row Σ → sem_row Σ) `{Contractive R} v Φ:
  iEff_car (sem_row_rec R) v Φ ≡ iEff_car (R (sem_row_rec R)) v Φ.
Proof. f_equiv. apply non_dep_fun_equiv. rewrite {1}sem_row_rec_unfold //. Qed.

(*  Properties *)

Global Instance sem_row_cons_ne {Σ} op : NonExpansive2 (@sem_row_cons Σ op).
Proof. 
  intros ???????. rewrite /sem_row_cons. 
  intros ??. simpl. do 7 f_equiv; first f_equiv; apply non_dep_fun_dist; by f_equiv.  
Qed.
Global Instance sem_row_cons_Proper {Σ} op : Proper ((≡) ==> (≡) ==> (≡)) (@sem_row_cons Σ op).
Proof. apply ne_proper_2. apply _. Qed.
Global Instance sem_row_cons_contractive {Σ} op n : Proper (dist_later n ==> dist n ==> dist n) (@sem_row_cons Σ op).
Proof. 
  intros ???????. rewrite /sem_row_cons. 
  intros ?. simpl. do 6 f_equiv; first f_contractive; f_equiv; apply non_dep_fun_dist; by f_equiv.
Qed.

Global Instance sem_row_flip_bang_ne {Σ} : NonExpansive (@sem_row_flip_bang Σ).
Proof. intros ?????. rewrite /sem_row_flip_bang. intros ?. simpl. 
       do 4 f_equiv. apply non_dep_fun_dist; by f_equiv. Qed.
Global Instance sem_row_flip_bang_Proper {Σ} : Proper ((≡) ==> (≡)) (@sem_row_flip_bang Σ).
Proof. apply ne_proper. apply _. Qed.

Global Instance sem_row_flip_bang_rec_contractive {Σ} (R : sem_row Σ -d> sem_row Σ) `{Contractive R} : 
  Contractive (λ θ, sem_row_flip_bang (R θ)).
Proof.
  intros ??????. rewrite /sem_row_flip_bang. simpl.
  do 4 f_equiv. apply non_dep_fun_dist. by apply Contractive0.
Qed. 

(* Notations. *)

Notation "⟨⟩" := (sem_row_nil) : sem_row_scope.
Notation "opσ · ρ" := (sem_row_cons opσ.1%S opσ.2%S ρ%R) (at level 80, right associativity) : sem_row_scope.
Notation "¡ ρ" := (sem_row_flip_bang ρ%R) (at level 10) : sem_row_scope.
Notation "'μR:' θ , ρ " := (sem_row_rec (λ θ, ρ%R)) (at level 50) : sem_row_scope.

(* One-Shot Rows *)

Global Instance row_nil_once {Σ} : Once (⟨⟩ : sem_row Σ)%R.
Proof. constructor. rewrite /= /sem_row_nil. iIntros (v Φ Φ') "_ []". Qed.

Global Instance row_cons_once {Σ} (ρ : sem_row Σ) op (σ : sem_sig Σ) `{! Once σ, ! Once ρ } :
  Once ((op, σ) · ρ).
Proof.
  constructor. rewrite /sem_row_cons /=. 
  iIntros (v Φ Φ') "HPost (%op' & %v' & -> & H)".
  destruct (decide (op = op')) as [->|].
  - iExists op', v'; iSplit; try done. 
    rewrite decide_True; last auto. 
    inv H. iDestruct (monotonic_prot with "HPost") as "Hσ".
    by iApply "Hσ".
  - iExists op', v'; iSplit; try done. 
    rewrite decide_False; last auto.
    inv H0. iDestruct (monotonic_prot with "HPost") as "Hρ".
    by iApply "Hρ".
Qed.

Global Instance row_fbang_once {Σ} (ρ : sem_row Σ) : Once (¡ ρ)%R.
Proof.
  constructor. rewrite /sem_row_flip_bang.
  pose proof (upcl_mono_prot ρ) as []. iIntros (???).
  iIntros "HPost /= H". 
  iApply (monotonic_prot v Φ Φ' with "HPost H").
Qed.

Global Instance row_rec_once {Σ} (R : sem_row Σ → sem_row Σ) `{Contractive R} :
  (∀ θ, Once (R θ)) → Once (μR: θ, R θ).
Proof.
  intros H. constructor. 
  iIntros (???) "HPost H". rewrite !sem_row_rec_unfold_iEff.
  specialize (H (μR: θ, R θ)%R). inv H. by iApply (monotonic_prot with "HPost").
Qed.

(* Substructurality relation on rows wrt to types and environments *)

Definition mono_prot_on_prop {Σ} (Ψ : iEff Σ) (P : iProp Σ) : iProp Σ :=
  □ (∀ v Φ, iEff_car Ψ v Φ -∗ P -∗ iEff_car Ψ v (λ w, Φ w ∗ P))%I.

(* For semantic signatures, being monotonic on all propositions is the same as being monotonic
   because semantic signatures are persistently monotonic by definition *)
Lemma mono_prot_on_prop_monotonic {Σ} (σ : sem_sig Σ) : 
  (⊢ ∀ P, mono_prot_on_prop σ P) ↔ MonoProt σ.
Proof.
  split.
  - iIntros (H). constructor. iIntros (v Φ Φ') "Hpost HΨ".
    iDestruct (H with "HΨ Hpost") as "H".
    iApply (pmono_prot_prop _ σ with "[] H").
    { iIntros "!# % [HΦ HPost]". by iApply "HPost". }
  - iIntros (H) "%P %v %Φ !# Hσ HP". inv H.
    iApply (monotonic_prot with "[HP] Hσ"). iIntros (?) "$ //".
Qed.

Definition row_type_sub {Σ} (ρ : sem_row Σ) (τ : sem_ty Σ) : iProp Σ := 
  (∀ v, mono_prot_on_prop ρ (τ v)).

Notation "ρ ≼ₜ τ" := (row_type_sub ρ%R τ%T)%I (at level 80) : bi_scope.

Lemma row_type_sub_once {Σ} (ρ : sem_row Σ) (τ : sem_ty Σ) `{Once ρ} : ⊢ ρ ≼ₜ τ.
Proof.
  iIntros (w v Φ) "!# Hρ Hτ".
  iApply (monotonic_prot v Φ (λ w', Φ w' ∗ τ w)%I with "[Hτ] Hρ").
  iIntros "% $ //".
Qed.

Lemma row_type_sub_fbang {Σ} (ρ : sem_row Σ) (τ : sem_ty Σ) : ⊢ (¡ ρ) ≼ₜ τ.
Proof.
  iApply row_type_sub_once.
Qed.

Definition row_env_sub {Σ} (ρ : sem_row Σ) (Γ : env Σ) : iProp Σ := 
  (∀ vs, mono_prot_on_prop ρ (⟦ Γ ⟧ vs)).

Notation "ρ ≼ₑ Γ" := (row_env_sub ρ%R Γ%T) (at level 80) : bi_scope.

Lemma row_env_sub_once {Σ} (ρ : sem_row Σ) (Γ : env Σ) `{Once ρ} : ⊢ ρ ≼ₑ Γ.
Proof.
  iIntros (γ v Φ) "!# Hρ HΓ".
  iApply (monotonic_prot v Φ (λ w', Φ w' ∗ ⟦ Γ ⟧ γ)%I with "[HΓ] Hρ").
  iIntros "% $ //".
Qed.

Lemma row_env_sub_fbang {Σ} (ρ : sem_row Σ) (Γ : env Σ) : ⊢ (¡ ρ) ≼ₑ Γ.
Proof. iApply row_env_sub_once. Qed.

(* Subsumption relation on rows *)

Lemma row_le_refl {Σ} (ρ : sem_row Σ) :
  ⊢ ρ ≤R ρ.
Proof. iApply iEff_le_refl. Qed.

Lemma row_le_trans {Σ} (ρ₁ ρ₂ ρ₃ : sem_row Σ) :
  ρ₁ ≤R ρ₂ -∗ 
  ρ₂ ≤R ρ₃ -∗
  ρ₁ ≤R ρ₃.
Proof. iApply iEff_le_trans. Qed.

Lemma row_le_nil {Σ} (ρ : sem_row Σ) : 
  ⊢ ⟨⟩ ≤R ρ.
Proof. iApply iEff_le_bottom. Qed.

Lemma row_le_cons_comp {Σ} (ρ ρ' : sem_row Σ) (op : operation) (σ σ' : sem_sig Σ) : 
  σ ≤S σ' -∗ ρ ≤R ρ' -∗ 
  (op, σ) · ρ ≤R (op, σ') · ρ'.
Proof.
  iIntros "#Hσσ' #Hρρ'". rewrite /sem_row_cons /=. 
  iIntros (??) "!# (%op' & %v' & -> & H)".
  iExists op', v'; iSplit; first done.
  destruct (decide (op = op')); first (by iApply "Hσσ'"). 
  by iApply "Hρρ'".
Qed.

Lemma row_le_rec_unfold {Σ} (R : sem_row Σ → sem_row Σ) `{Contractive R} :
  ⊢ (μR: θ, R θ) ≤R R (μR: θ, R θ).
Proof. rewrite {1} sem_row_rec_unfold //. iApply row_le_refl. Qed.

Lemma row_le_rec_fold {Σ} (R : sem_row Σ → sem_row Σ) `{ Contractive R }:
  ⊢ R (μR: θ, R θ) ≤R (μR: θ, R θ).
Proof. rewrite - {1} sem_row_rec_unfold. iApply row_le_refl. Qed.

Lemma row_le_mfbang_cons {Σ} op m σ (ρ : sem_row Σ) :
  ⊢ ¡_[ m ] ((op, σ) · ρ) ≤R (op, ¡_[ m ] σ)%S · (¡_[ m ] ρ).
Proof. 
  rewrite /sem_row_flip_bang. destruct m; last iApply row_le_refl.
  iIntros (??) "!# (%Φ' & (%op' & %v' & -> & H) & Hpost)". simpl.
  iExists op', v'. iSplit; first done.
  destruct (decide (op = op')); first iNext; iExists Φ'; iFrame. 
Qed.

Corollary row_le_mfbang_cons_os {Σ} op m (σ : sem_sig Σ) (ρ : sem_row Σ) `{Once σ}:
  ⊢ ¡_[ m ] ((op, σ) · ρ) ≤R (op, σ)%S · (¡_[ m ] ρ).
Proof. 
  iApply row_le_trans; first iApply row_le_mfbang_cons.
  iApply row_le_cons_comp; last iApply row_le_refl.
  iApply sig_le_mfbang_elim.
Qed.

Corollary row_le_mfbang_cons_eff {Σ} op m {TT : tele} (ι κ : tele_arg TT → sem_ty Σ) (ρ : sem_row Σ) :
  ⊢ ¡_[ m ] ((op, ∀S..: α , ι α =[ m ]=> κ α) · ρ) ≤R (op, (∀S..: α , ι α =[ m ]=> κ α)%S) · (¡_[ m ] ρ).
Proof. 
  iApply row_le_trans; first iApply row_le_mfbang_cons.
  iApply row_le_cons_comp; last iApply row_le_refl.
  iApply sig_le_mfbang_elim_eff.
Qed.

Lemma row_le_mfbang_comp {Σ} (m : mode) (ρ ρ' : sem_row Σ) :
  ρ ≤R ρ' -∗
  ¡_[ m ] ρ ≤R ¡_[ m ] ρ'. 
Proof. 
  iIntros "#Hle". destruct m; last iApply "Hle".
  rewrite /sem_row_flip_bang. 
  iIntros (??) "!# (%Φ' & Hρ & Hpost)". simpl.
  iExists Φ'. iFrame. by iApply "Hle".
Qed.

Lemma row_le_mfbang_intro {Σ} (m : mode) (ρ : sem_row Σ) :
  ⊢ ρ ≤R ¡_[ m ] ρ. 
Proof. 
  destruct m; last iApply row_le_refl.
  rewrite /sem_row_flip_bang. iIntros (??) "!# Hρ". simpl.
  iExists Φ. iFrame. iIntros (?) "$ //".
Qed.

Lemma row_le_mfbang_elim {Σ} m (ρ : sem_row Σ) `{! Once ρ}:
  ⊢ ¡_[m] ρ ≤R ρ. 
Proof. 
  destruct m; simpl; last iApply row_le_refl.
  rewrite /sem_row_flip_bang. iIntros (??) "!# (%Φ' & Hρ & Hpost)". simpl.
  inv H. by iApply (monotonic_prot with "Hpost").
Qed.

Lemma row_le_mfbang_comm {Σ} m m' (ρ : sem_row Σ) :
  ⊢ ¡_[m] (¡_[m'] ρ) ≤R ¡_[m'] (¡_[m] ρ).
Proof. 
  destruct m, m'; iApply row_le_refl.
Qed.

Lemma row_le_mfbang_mode_le {Σ} m m' (ρ : sem_row Σ) :
  ⊢ m' ≤M m -∗ (¡_[m] ρ) ≤R (¡_[m'] ρ).
Proof. 
  iIntros "H". destruct m.
  - iDestruct (mode_le_OS_inv with "H") as "->".
    iApply sig_le_refl.
  - iApply row_le_mfbang_intro.
Qed.

Corollary row_le_fbang_nil {Σ} m :
   ⊢ ¡_[m] ⟨⟩%R ≤R (⟨⟩%R : sem_row Σ).
Proof. 
  destruct m; simpl; last iApply row_le_refl.
  apply (row_le_mfbang_elim OS). apply _. 
Qed.

Corollary row_le_fbang_idemp {Σ} m (ρ : sem_row Σ) :
   ⊢ ¡_[m] (¡_[m] ρ) ≤R ¡_[m] ρ.
Proof. 
  destruct m; simpl; last iApply row_le_refl.
  apply (row_le_mfbang_elim OS). apply _. 
Qed.

Corollary row_le_mfbang_rec {Σ} (m : mode) (R : sem_row Σ → sem_row Σ) `{ Contractive R }: 
  (∀ θ, ¡_[ m ] (R θ) ≤R (R θ)) -∗ ¡_[ m ] (μR: θ, R θ) ≤R (μR: θ, R θ).
Proof. 
  iIntros "#Hle". destruct m; last iApply row_le_refl.
  iApply row_le_trans.
  { iApply (row_le_mfbang_comp OS). iApply row_le_rec_unfold. }
  iApply row_le_trans; first iApply "Hle". 
  iApply row_le_rec_fold.
Qed.

Lemma row_le_swap_second {Σ} (op op' : operation) (σ σ' : sem_sig Σ) (ρ : sem_row Σ) : 
  op ≠ op' →
  ⊢ (op, σ) · (op', σ') · ρ ≤R (op', σ') · (op, σ) · ρ. 
Proof. 
  iIntros (Hneq). rewrite /sem_row_cons /=.
  iIntros (??) "!# (%op'' & %v'' & %Heq & H)". simpl.
  destruct (decide (op = op'')) as [->|].
  - iExists op'', v''. iSplit; first done.
    rewrite decide_False; last done.
    iExists op'', v''; iSplit; first done.
    rewrite decide_True //.
  - iDestruct "H" as "(%op''' & %v''' & %Heq' & H)".
    destruct (decide (op' = op''')) as [->|].
    + iExists op'', v''; iSplit; first done.
      simplify_eq. rewrite decide_True //.
    + iExists op''', v''; iSplit; first by simplify_eq.
      simplify_eq. rewrite decide_False //.
      iExists op''', v'''. iSplit; first done.
      rewrite decide_False //.
Qed.

Corollary row_le_swap_third {Σ} (op op' op'' : operation) (σ σ' σ'' : sem_sig Σ) (ρ : sem_row Σ) : 
  op ≠ op' → op' ≠ op'' → op'' ≠ op →
  ⊢ (op, σ) · (op', σ') · (op'', σ'') · ρ ≤R (op'', σ'') · (op, σ) · (op', σ') · ρ. 
Proof. 
  iIntros (???). 
  iApply row_le_trans; first iApply row_le_cons_comp; [iApply sig_le_refl|by iApply row_le_swap_second|].
  by iApply row_le_swap_second.
Qed.

Corollary row_le_swap_fourth {Σ} (op op' op'' op''' : operation) (σ σ' σ'' σ''': sem_sig Σ) (ρ : sem_row Σ) : 
  op ≠ op' → op ≠ op'' → op ≠ op''' → op' ≠ op'' → op' ≠ op''' → op'' ≠ op''' → 
  ⊢ (op, σ) · (op', σ') · (op'', σ'') · (op''', σ''') · ρ ≤R 
    (op''', σ''') · (op, σ) · (op', σ') · (op'', σ'') · ρ.
Proof. 
  iIntros (??????). 
  iApply row_le_trans; first iApply row_le_cons_comp; [iApply sig_le_refl|by iApply row_le_swap_third|].
  by iApply row_le_swap_second.
Qed.
