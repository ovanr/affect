
(* adequacy.v *)

(* This file contains the proofs of adequacy. *)
(* This file is based from the adequacy proof in TES:
   https://gitlab.inria.fr/cambium/tes/-/blob/main/theories/logic/adequacy.v *)

From iris.proofmode     Require Import base tactics classes.
From iris.program_logic Require Import weakestpre adequacy.
From stdpp Require Export gmap.

(* Local imports *)
From affect.lang Require Import affect.
From affect.logic Require Import sem_def.
From affect.logic Require Import sem_types.
From affect.logic Require Import sem_row.
From affect.logic Require Import sem_judgement.
From affect.logic Require Import ewpw.


Section adequacy.

Context `{!heapGS Σ}.

Lemma ewp_imp_wp `{!irisGS eff_lang Σ} e Φ :
 EWP e {{ v, Φ v }} ⊢ WP e @ NotStuck; ⊤ {{ Φ }}.
Proof. 
  iLöb as "IH" forall (e).
  destruct (to_val e) as [ v    |] eqn:?; [|
  destruct (to_eff e) as [((m,v), k)|] eqn:?  ].
  - rewrite ewp_unfold /ewp_pre wp_unfold /wp_pre /= Heqo. by auto.
  - rewrite -(of_to_eff _ _ _ _ Heqo0).
    iIntros "Hewp".
    rewrite ewp_unfold. unfold ewp_pre.
    destruct (to_val (Eff m v k)) eqn:H; first done.
    simpl. destruct m; iDestruct "Hewp" as (?) "[[] _]".
  - rewrite ewp_unfold /ewp_pre wp_unfold /wp_pre /= Heqo Heqo0.
    iIntros "Hewp" (σ ns k ks nt) "Hs".
    iMod ("Hewp" $! σ ns k ks nt with "Hs") as "[$ H]". iModIntro.
    iIntros (e2 σ2 efs Hstep) "Hcred".
    case k   as [|??]; [|done].
    case efs as [|??]; [|done].
    simpl in Hstep.
    iMod ("H" with "[//]") as "H". iIntros "!> !>".
    simpl. iMod "H". iModIntro.
    iApply (step_fupdN_wand with "[H]"); first by iApply "H".
    iIntros "H". iMod "H" as "[$ Hewp]". iModIntro.
    by iSplit; [iApply "IH"|].
Qed.

Lemma eff_heap_adequacy `{!heapGpreS Σ} s e σ φ :
  (∀ `{!heapGS Σ}, ⊢ WP e @ s; ⊤ {{ v, ⌜φ v⌝ }}) →
  adequate s e σ (λ v _, φ v).
Proof.
  intros Hwp; eapply (@wp_adequacy Σ _ _). 
  intros ??. simpl.
  iMod (gen_heap_init σ.(heap)) as (?) "[Hh _]".
  iMod (inv_heap_init loc val) as (?) ">Hi".
  iExists
      (λ σ κs, gen_heap_interp σ.(heap)),
      (λ _, True%I).
    iFrame. iApply (Hwp (HeapGS _ _ _ _)).
  Qed.

Lemma eff_adequacy `{!heapGpreS Σ} e σ φ :
  (∀ `{!heapGS Σ}, ⊢ EWP e {{ v, ⌜φ v⌝ }}) →
  adequate NotStuck e σ (λ v _, φ v).
Proof.
  intros Hwp.
  apply eff_heap_adequacy.
  intros.
  iApply ewp_imp_wp. iApply Hwp.
Qed.

Lemma eff_adequate_not_stuck `{!heapGpreS Σ} e σ Φ :
  (∀ `{!heapGS Σ}, ⊢ EWP e {{ Φ }}) →
  ∀ e' σ', rtc erased_step ([e], σ) ([e'], σ') → 
           not_stuck e' σ'.
Proof.
  intros Hewp ?? Hstep.
  assert (adequate NotStuck e σ (λ _ _, True)) as Hadequate.
  { apply eff_adequacy.
    intros.
    iApply ewp_mono.
    { iApply Hewp. }
    by iIntros (?) "_". }
  eapply adequate_alt in Hadequate as [_ Hnot_stuck]; eauto.
  apply Hnot_stuck; auto.
  set_solver.
Qed.

Lemma sem_typed_ewpw e τ ρ:
  (∀ `{heapGS Σ}, ⊨ e : ρ : τ -∗ EWPW e <| ρ |> {{ τ }}). 
Proof.
  iIntros (?) "He". unfold sem_typed. simpl.
  iAssert (emp)%I as "Hemp"; first done.
  iAssert (∀ v, τ v ∗ emp -∗ τ v)%I as "Himp".
  { iIntros (?) "[H _] {$H}". }
  pose (@empty (@gmap string String.eq_dec String.countable val)
          (@gmap_empty string String.eq_dec String.countable val)) as Hempty. 
  iSpecialize ("He" $! ∅ with "[]"); first done. 
  rewrite (subst_map_empty e). 
  iApply (ewpw_mono with "[He]"); [iApply "He"|iIntros "!# % [$ _] //="].
Qed.

Lemma sem_typed_ewp_nil e τ :
  (∀ `{heapGS Σ}, ⊨ e : ⟨⟩ : τ -∗ EWP e {{ τ }}). 
Proof.
  iIntros (?) "He". unfold sem_typed. simpl.
  iAssert (emp)%I as "Hemp"; first done.
  iAssert (∀ v, τ v ∗ emp -∗ τ v)%I as "Himp".
  { iIntros (?) "[H _] {$H}". }
  pose (@empty (@gmap string String.eq_dec String.countable val)
          (@gmap_empty string String.eq_dec String.countable val)) as Hempty. 
  iSpecialize ("He" $! ∅ with "[]"); first done. 
  rewrite (subst_map_empty e). iApply (ewpw_bot_inv with "[He]").
  iApply (ewpw_mono with "[He]"); [iApply "He"|iIntros "!# % [$ _] //="].
Qed.

Lemma sem_typed_adequacy `{!heapGpreS Σ} e τ σ :
  (∀ `{!heapGS Σ}, ⊢ ⊨ e : ⟨⟩ : τ) →
  ∀ e' σ', rtc erased_step ([e], σ) ([e'], σ') → 
           not_stuck e' σ'.
Proof.
  intros He. 
  apply (eff_adequate_not_stuck _ _ τ).
  iIntros (?). 
  iApply (sem_typed_ewp_nil). iApply He.
Qed.

End adequacy.
