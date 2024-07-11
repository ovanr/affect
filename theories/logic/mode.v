
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

Definition mode_glb m m' : mode :=
  match m with
    OS => OS 
  | MS => m'
  end.

Definition mode_lub m m' : mode :=
  match m with
    MS => MS
  | OS => m'
  end.

Lemma mode_glb_idemp m :
  mode_glb m m = m.
Proof. by destruct m. Qed.

Lemma mode_glb_assoc m₁ m₂ m₃ :
  mode_glb m₁ (mode_glb m₂ m₃) = (mode_glb (mode_glb m₁ m₂) m₃).
Proof. by destruct m₁. Qed.

Lemma mode_glb_comm m₁ m₂ :
  mode_glb m₁ m₂ = mode_glb m₂ m₁.
Proof. by destruct m₁, m₂. Qed.

Lemma mode_glb_os m :
  mode_glb OS m = OS.
Proof. destruct m; eauto. Qed.

Lemma mode_lub_idemp m :
  mode_lub m m = m.
Proof. by destruct m. Qed.

Lemma mode_lub_assoc m₁ m₂ m₃ :
  mode_lub m₁ (mode_lub m₂ m₃) = (mode_lub (mode_lub m₁ m₂) m₃).
Proof. by destruct m₁. Qed.

Lemma mode_lub_comm m₁ m₂ :
  mode_lub m₁ m₂ = mode_lub m₂ m₁.
Proof. by destruct m₁, m₂. Qed.

Lemma mode_lub_ms m :
  mode_lub MS m = MS.
Proof. destruct m; eauto. Qed.


(* Sub-Typing on Mode *)

Lemma mode_le_refl {Σ} (m : mode) : ⊢ (m ≤M m : iProp Σ).
Proof. by iLeft. Qed.

Lemma mode_le_trans {Σ} (m1 m2 m3 : mode) : 
  m1 ≤M m2 -∗
  m2 ≤M m3 -∗
  (m1 ≤M m3 : iProp Σ).
Proof. iIntros "#H12 H23". destruct m1,m2,m3; eauto. Qed.

Lemma mode_le_MS {Σ} (m : mode) : 
  ⊢ (m ≤M MS : iProp Σ).
Proof. by iRight. Qed.

Lemma mode_lub_le {Σ} (m₁ m₁' m₂ m₂' : mode) :
  m₁ ≤M m₁' -∗ m₂ ≤M m₂' -∗
  mode_lub m₁ m₂ ≤M@{ Σ } mode_lub m₁' m₂'.
Proof. iIntros "Hm₁₁' Hm₂₂'". destruct m₁,m₂,m₁',m₂'; eauto. Qed.

Lemma mode_le_OS {Σ} (m : mode) : 
  ⊢ (OS ≤M m : iProp Σ).
Proof. destruct m; eauto. Qed.

Lemma mode_le_OS_inv {Σ} (m : mode) : 
  (m ≤M OS : iProp Σ) -∗ m ≡ OS.
Proof.
  iIntros "H". destruct m; first done.
  iDestruct "H" as "%H". inv H.
Qed.

Notation "m ⊓ₘ m'" := (mode_glb m m') (at level 80) : bi_scope.
Notation "m ⊔ₘ m'" := (mode_lub m m') (at level 80) : bi_scope.

Definition mode_type_sub {Σ} (m : mode) (τ : sem_ty Σ) : iProp Σ :=
  □ (∀ v, τ v -∗ □? m (τ v)).

Notation "m ₘ≼ₜ τ" := (mode_type_sub m τ%T) (at level 80) : bi_scope.

Lemma mode_type_sub_os {Σ} (τ : sem_ty Σ) : ⊢ OS ₘ≼ₜ τ.
Proof. rewrite /mode_type_sub /=. iIntros "!# % $ //". Qed.

Lemma mode_type_sub_ms {Σ} m (τ : sem_ty Σ) : copy_ty τ ⊢ m ₘ≼ₜ τ.
Proof. 
  rewrite /mode_type_sub /=. iIntros "#Hcpy !# % Hτ". 
  iApply bi.intuitionistically_intuitionistically_if.
  iApply ("Hcpy" with "Hτ"). 
Qed.

Definition mode_env_sub {Σ} (m : mode) (Γ : env Σ) : iProp Σ :=
  □ (∀ γ, ⟦ Γ ⟧ γ -∗ □? m (⟦ Γ ⟧ γ)).

Notation "m ₘ≼ₑ Γ" := (mode_env_sub m Γ%T) (at level 80) : bi_scope.

Lemma mode_env_sub_os {Σ} (Γ : env Σ) : ⊢ OS ₘ≼ₑ Γ.
Proof. rewrite /mode_env_sub /=. iIntros "!# % $ //". Qed.

Lemma mode_env_sub_ms {Σ} m (Γ : env Σ) : copy_env Γ -∗ m ₘ≼ₑ Γ.
Proof. 
  rewrite /mode_env_sub /=. iIntros "#Hcpy !# % HΓ ". 
  iApply bi.intuitionistically_intuitionistically_if.
  iApply ("Hcpy" with "HΓ"). 
Qed.

Lemma mode_env_sub_nil {Σ} m : ⊢ m ₘ≼ₑ ([] : env Σ).
Proof. iApply mode_env_sub_ms. iIntros "!# % _ //". Qed.

Lemma mode_env_sub_cons {Σ} m x τ (Γ : env Σ) : 
  m ₘ≼ₑ Γ -∗ m ₘ≼ₜ τ -∗ m ₘ≼ₑ ((x, τ) :: Γ).
Proof.
  iIntros "#HmΓ #Hmτ %γ !# (%w & %Heq & Hτ & HΓ)".
  iSpecialize ("HmΓ" $! γ with "HΓ").
  iSpecialize ("Hmτ" $! w with "Hτ").
  iDestruct (bi.intuitionistically_if_sep_2 m (⟦ Γ ⟧ γ) (τ w) with "[HmΓ Hmτ]") as "HmΓτ".
  { iFrame. }
  iApply (intuitionistically_if_mono_iprop with "[] HmΓτ").
  iIntros "!# [HΓ Hτ]". 
  iExists w. by iFrame.
Qed.
