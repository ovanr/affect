
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
              (λ v, λne Φ, ∃ (op' : operation) (s : nat) (v' : val), 
                            ⌜ v = (effect op', #s, v')%V ⌝ ∗
                            if decide (op = op') then 
                              match s with
                                0 => ▷ (iEff_car σ v' Φ)
                              | S s' => iEff_car ρ (effect op', #s', v')%V Φ
                              end
                            else
                                iEff_car ρ (effect op', #s, v')%V Φ)%I) _) _).
Next Obligation. 
  intros ?????????. repeat f_equiv; last done. simpl. 
  destruct a0; by repeat f_equiv. 
Qed.
Next Obligation. 
  iIntros (???????) "#HPost (%op' & %s & %v' & -> & H)". simpl.
  iExists op', s, v'. iSplit; first done.
  destruct (decide (op = op')).
  - destruct s.
    { iNext. iApply (pmono_prot_prop Σ σ with "HPost H"). }
    iApply (pmono_prot_prop Σ ρ with "HPost H").
  - iApply (pmono_prot_prop Σ ρ with "HPost H").
Qed.
Next Obligation.
  iIntros (??????) "(%op' & %s & %v' & -> & H)". by iExists op', s, v'.
Qed.

Program Definition sem_row_tun {Σ} (op : operation) : sem_row Σ -d> sem_row Σ :=
    λ ρ, (@SemRow Σ (@PMonoProt Σ (IEff 
              (λ v, λne Φ, ∃ (op' : operation) (s : nat) (v' : val), 
                            ⌜ v = (effect op', #s, v')%V ⌝ ∗
                            if decide (op = op') then 
                              match s with
                                0 => False
                              | S s' => iEff_car ρ (effect op', #s', v')%V Φ
                              end
                            else
                                iEff_car ρ (effect op', #s, v')%V Φ)%I) _) _).
Next Obligation. 
  intros ????????. repeat f_equiv; last done. simpl. 
  destruct a0; by repeat f_equiv. 
Qed.
Next Obligation. 
  iIntros (??????) "#HPost (%op' & %s & %v' & -> & H)". simpl.
  iExists op', s, v'. iSplit; first done.
  destruct (decide (op = op')).
  - destruct s; first done.
    iApply (pmono_prot_prop Σ ρ with "HPost H").
  - iApply (pmono_prot_prop Σ ρ with "HPost H").
Qed.
Next Obligation.
  iIntros (?????) "(%op' & %s & %v' & -> & H)". by iExists op', s, v'.
Qed.

Program Definition sem_row_os {Σ} (ρ : sem_row Σ) : sem_row Σ := 
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
  intros ??. simpl. do 8 f_equiv. destruct a0; first f_equiv;
  f_equiv; apply non_dep_fun_dist; by f_equiv.  
  f_equiv. apply non_dep_fun_dist. by f_equiv.
Qed.
Global Instance sem_row_cons_Proper {Σ} op : Proper ((≡) ==> (≡) ==> (≡)) (@sem_row_cons Σ op).
Proof. apply ne_proper_2. apply _. Qed.
Global Instance sem_row_cons_contractive {Σ} op n : Proper (dist_later n ==> dist n ==> dist n) (@sem_row_cons Σ op).
Proof. 
  intros ???????. rewrite /sem_row_cons. 
  intros ?. simpl. do 8 f_equiv. destruct a0. 
  - f_contractive. f_equiv; apply non_dep_fun_dist. by f_equiv.
  - f_equiv. apply non_dep_fun_dist. by f_equiv.
  - f_equiv. apply non_dep_fun_dist. by f_equiv.
Qed.

Global Instance sem_row_tun_ne {Σ} op : NonExpansive (@sem_row_tun Σ op).
Proof. 
  intros ??????. rewrite /sem_row_tun. 
  simpl. do 8 f_equiv. destruct a0; first f_equiv;
  f_equiv; apply non_dep_fun_dist; by f_equiv.  
  f_equiv. apply non_dep_fun_dist. by f_equiv.
Qed.
Global Instance sem_row_tun_Proper {Σ} op : Proper ((≡) ==> (≡)) (@sem_row_tun Σ op).
Proof. apply ne_proper. apply _. Qed.

Global Instance sem_row_os_ne {Σ} : NonExpansive (@sem_row_os Σ).
Proof. intros ?????. rewrite /sem_row_os. intros ?. simpl. 
       do 4 f_equiv. apply non_dep_fun_dist; by f_equiv. Qed.
Global Instance sem_row_os_Proper {Σ} : Proper ((≡) ==> (≡)) (@sem_row_os Σ).
Proof. apply ne_proper. apply _. Qed.

Global Instance sem_row_os_rec_contractive {Σ} (R : sem_row Σ -d> sem_row Σ) `{Contractive R} : 
  Contractive (λ θ, sem_row_os (R θ)).
Proof.
  intros ??????. rewrite /sem_row_os. simpl.
  do 4 f_equiv. apply non_dep_fun_dist. by apply Contractive0.
Qed. 

(* Notations. *)

Notation "⟨⟩" := (sem_row_nil) : sem_row_scope.
Notation "opσ · ρ" := (sem_row_cons opσ.1%S opσ.2%S ρ%R) (at level 80, right associativity) : sem_row_scope.
Notation "⦗ ρ | op ⦘" := (sem_row_tun op ρ%R) (at level 80, right associativity) : sem_row_scope.
Notation "¡ ρ" := (sem_row_os ρ%R) (at level 10) : sem_row_scope.
Notation "'μR:' θ , ρ " := (sem_row_rec (λ θ, ρ%R)) (at level 50) : sem_row_scope.

(* One-Shot Rows *)

Global Instance row_nil_once {Σ} : Once (⟨⟩ : sem_row Σ)%R.
Proof. constructor. rewrite /= /sem_row_nil. iIntros (v Φ Φ') "_ []". Qed.

Global Instance row_cons_once {Σ} (ρ : sem_row Σ) op (σ : sem_sig Σ) `{! Once σ, ! Once ρ } :
  Once ((op, σ) · ρ).
Proof.
  constructor. rewrite /sem_row_cons /=. 
  iIntros (v Φ Φ') "HPost (%op' & %s' & %v' & -> & H)".
  destruct (decide (op = op')) as [->|]; first destruct s' as [|s'].
  - iExists op', 0, v'; iSplit; try done. 
    rewrite decide_True; last auto. 
    inv H. iDestruct (monotonic_prot with "HPost") as "Hσ".
    by iApply "Hσ".
  - iExists op', (S s'), v'; iSplit; try done. 
    rewrite decide_True; last auto.
    inv H0. iDestruct (monotonic_prot with "HPost") as "Hρ".
    by iApply "Hρ".
  - iExists op', s', v'; iSplit; try done. 
    rewrite decide_False; last auto.
    inv H0. iDestruct (monotonic_prot with "HPost") as "Hρ".
    by iApply "Hρ".
Qed.

Global Instance row_os_once {Σ} (ρ : sem_row Σ) : Once (¡ ρ)%R.
Proof.
  constructor. rewrite /sem_row_os.
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

Global Instance row_type_sub_persistent {Σ} ρ τ :
  Persistent (@row_type_sub Σ ρ τ).
Proof.
  unfold row_type_sub. apply _.
Qed.

Notation "ρ ≼ₜ τ" := (row_type_sub ρ%R τ%T)%I (at level 80) : bi_scope.

Lemma row_type_sub_os {Σ} (ρ : sem_row Σ) (τ : sem_ty Σ) : ⊢ (¡ ρ) ≼ₜ τ.
Proof.
  iIntros (w v Φ) "!# Hρ Hτ".
  pose proof (@row_os_once Σ ρ) as H. inv H. 
  iApply (monotonic_prot v Φ (λ w', Φ w' ∗ τ w)%I with "[Hτ] Hρ").
  iIntros "% $ //".
Qed.

Definition row_env_sub {Σ} (ρ : sem_row Σ) (Γ : env Σ) : iProp Σ := 
  (∀ vs, mono_prot_on_prop ρ (⟦ Γ ⟧ vs)).

Global Instance row_env_sub_persistent {Σ} ρ Γ :
  Persistent (@row_env_sub Σ ρ Γ).
Proof.
  unfold row_env_sub. apply _.
Qed.

Notation "ρ ≼ₑ Γ" := (row_env_sub ρ%R Γ%T) (at level 80) : bi_scope.

Lemma row_env_sub_os {Σ} (ρ : sem_row Σ) (Γ : env Σ) : ⊢ (¡ ρ) ≼ₑ Γ.
Proof.
  iIntros (vs v Φ) "!# Hρ HΓ".
  pose proof (@row_os_once Σ ρ) as H. inv H. 
  by iApply (monotonic_prot _ Φ with "[HΓ]"); first iIntros "% $ //".
Qed.

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
  iIntros (??) "!# (%op' & %s' & %v' & -> & H)".
  iExists op', s', v'; iSplit; first done.
  destruct (decide (op = op')); first destruct s' as [|];
  first (by iApply "Hσσ'"); by iApply "Hρρ'".
Qed.

Lemma row_le_rec_unfold {Σ} (R : sem_row Σ → sem_row Σ) `{Contractive R} :
  ⊢ (μR: θ, R θ) ≤R R (μR: θ, R θ).
Proof. rewrite {1} sem_row_rec_unfold //. iApply row_le_refl. Qed.

Lemma row_le_rec_fold {Σ} (R : sem_row Σ → sem_row Σ) `{ Contractive R }:
  ⊢ R (μR: θ, R θ) ≤R (μR: θ, R θ).
Proof. rewrite - {1} sem_row_rec_unfold. iApply row_le_refl. Qed.

Lemma row_le_os_cons {Σ} op σ (ρ : sem_row Σ) :
  ⊢ ¡ ((op, σ) · ρ) ≤R (op, ¡ σ)%S · (¡ ρ).
Proof. 
  rewrite /sem_row_os. 
  iIntros (??) "!# (%Φ' & (%op' & %s & %v' & -> & H) & Hpost)". simpl.
  iExists op', s, v'. iSplit; first done.
  destruct (decide (op = op')); first destruct s as [|];
  first iNext; iExists Φ'; iFrame. 
Qed.

Lemma row_le_os_comp {Σ} (ρ ρ' : sem_row Σ) :
  ρ ≤R ρ' -∗
  ¡ ρ ≤R ¡ ρ'. 
Proof. 
  iIntros "#Hle". rewrite /sem_row_os. 
  iIntros (??) "!# (%Φ' & Hρ & Hpost)". simpl.
  iExists Φ'. iFrame. by iApply "Hle".
Qed.

Lemma row_le_os_intro {Σ} (ρ : sem_row Σ) :
  ⊢ ρ ≤R ¡ ρ. 
Proof. 
  rewrite /sem_row_os. iIntros (??) "!# Hρ". simpl.
  iExists Φ. iFrame. iIntros (?) "$ //".
Qed.

Lemma row_le_os_elim {Σ} (ρ : sem_row Σ) `{! Once ρ}:
  ⊢ ¡ ρ ≤R ρ. 
Proof. 
  rewrite /sem_row_os. iIntros (??) "!# (%Φ' & Hρ & Hpost)". simpl.
  inv H. by iApply (monotonic_prot with "Hpost").
Qed.

Corollary row_le_nil_os {Σ} :
   ⊢ ¡ ⟨⟩%R ≤R (⟨⟩%R : sem_row Σ).
Proof. apply row_le_os_elim. apply _. Qed.

Corollary row_le_os_idemp {Σ} (ρ : sem_row Σ) :
   ⊢ ¡ (¡ ρ) ≤R ¡ ρ.
Proof. apply row_le_os_elim. apply _. Qed.

Corollary row_le_rec_os {Σ} (R : sem_row Σ → sem_row Σ) `{ Contractive R }: 
  (∀ θ, ¡ (R θ) ≤R (R θ)) -∗ ¡ (μR: θ, R θ) ≤R (μR: θ, R θ).
Proof. 
  iIntros "#Hle". iApply row_le_trans.
  { iApply row_le_os_comp. iApply row_le_rec_unfold. }
  iApply row_le_trans; first iApply "Hle". 
  iApply row_le_rec_fold.
Qed.

Lemma row_le_swap_second {Σ} (op op' : operation) (σ σ' : sem_sig Σ) (ρ : sem_row Σ) : 
  op ≠ op' →
  ⊢ (op, σ) · (op', σ') · ρ ≤R (op', σ') · (op, σ) · ρ. 
Proof. 
  iIntros (Hneq). rewrite /sem_row_cons /=.
  iIntros (??) "!# (%op'' & %s'' & %v'' & %Heq & H)". simpl.
  destruct (decide (op = op'')) as [->|]; first destruct s'' as [|s''].
  - iExists op'', 0, v''. iSplit; first done.
    rewrite decide_False; last done.
    iExists op'', 0, v''; iSplit; first done.
    rewrite decide_True //.
  - iDestruct "H" as "(%op''' & %s''' & %v''' & %Heq' & H)".
    simplify_eq. rewrite decide_False; last done.
    iExists op''', (S s'''), v'''; iSplit; first done.
    rewrite decide_False; last done.
    iExists op''', (S s'''), v'''; iSplit; first done.
    rewrite decide_True //.
  - iDestruct "H" as "(%op''' & %s''' & %v''' & %Heq' & H)".
    destruct (decide (op' = op''')) as [->|]; first destruct s'''.
    + iExists op'', s'', v''; iSplit; first done.
      simplify_eq. rewrite decide_True //.
    + iExists op'', s'', v''; iSplit; first done.
      simplify_eq. rewrite decide_True //.
      iExists op''', s''', v'''; iSplit; first done.
      rewrite decide_False //.
    + iExists op''', s'', v''; iSplit; first by simplify_eq.
      simplify_eq. rewrite decide_False //.
      iExists op''', s''', v'''. iSplit; first done.
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
