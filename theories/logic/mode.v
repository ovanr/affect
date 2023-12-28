
From iris.proofmode Require Import base tactics.
From iris.algebra Require Import ofe gmap.
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

Definition mode_mult m m' : mode :=
  match m with
    MS => MS
  | OS => m'
  end.

Lemma mode_mult_idemp m :
  mode_mult m m = m.
Proof. by destruct m. Qed.

Lemma mode_mult_assoc m₁ m₂ m₃ :
  mode_mult m₁ (mode_mult m₂ m₃) = (mode_mult (mode_mult m₁ m₂) m₃).
Proof. by destruct m₁. Qed.

Lemma mode_mult_comm m₁ m₂ :
  mode_mult m₁ m₂ = mode_mult m₂ m₁.
Proof. by destruct m₁, m₂. Qed.

Lemma mode_mult_ms m :
  mode_mult MS m = MS.
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
  ⊢ (MS ≤M m : iProp Σ).
Proof. by iRight. Qed.

Lemma mode_mult_le {Σ} (m₁ m₁' m₂ m₂' : mode) :
  m₁ ≤M m₁' -∗ m₂ ≤M m₂' -∗
  mode_mult m₁ m₂ ≤M@{ Σ } mode_mult m₁' m₂'.
Proof. iIntros "Hm₁₁' Hm₂₂'". destruct m₁,m₂,m₁',m₂'; eauto. Qed.

Lemma mode_le_OS {Σ} (m : mode) : 
  ⊢ (m ≤M OS : iProp Σ).
Proof. destruct m; eauto. Qed.
