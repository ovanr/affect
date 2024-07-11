From iris.bi Require Import fixpoint big_op.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Export total_weakestpre weakestpre.
From iris.prelude Require Import options.
Import uPred.

(** The definition of total weakest preconditions is very similar to the
definition of normal (i.e. partial) weakest precondition, with the exception
that there is no later modality. Hence, instead of taking a Banach's fixpoint,
we take a least fixpoint. *)
Definition pwp_pre `{!irisGS_gen hlc Λ Σ} (s : stuckness) (Φ : val Λ → iProp Σ)
    (wp : expr Λ -d> iProp Σ) : expr Λ -d> iProp Σ := λ e1,
  match to_val e1 with
  | Some v => Φ v
  | None => ∀ σ1,
     ⌜if s is NotStuck then reducible_no_obs e1 σ1 else True⌝ ∗
     ∀ κ e2 σ2 efs, ⌜prim_step e1 σ1 κ e2 σ2 efs⌝ -∗
       ⌜κ = []⌝ ∗
       ⌜σ2 = σ1⌝ ∗
       ⌜efs = []⌝ ∗
       wp e2
  end%I.

(** This is some uninteresting bookkeeping to prove that [pwp_pre_mono] is
monotone. The actual least fixpoint [pwp_def] can be found below. *)
Local Lemma pwp_pre_mono `{!irisGS_gen hlc Λ Σ} s (wp1 wp2 : expr Λ → iProp Σ) Φ :
  ⊢ (□ ∀ e, wp1 e -∗ wp2 e) →
    ∀ e, pwp_pre s Φ wp1 e -∗ pwp_pre s Φ wp2 e.
Proof.
  iIntros "#H"; iIntros (e1) "Hwp". rewrite /pwp_pre.
  destruct (to_val e1) as [v|]; first done.
  iIntros (σ1). iDestruct ("Hwp" $! σ1) as "($ & Hwp)".
  iIntros (κ e2 σ2 efs) "Hstep".
  iDestruct ("Hwp" with "Hstep") as "($ & $ & $ & Hwp)". by iApply "H".
Qed.

Local Instance pwp_pre_mono_pred `{!irisGS_gen hlc Λ Σ} s Φ :
  BiMonoPred (pwp_pre s Φ).
Proof.
  constructor; last solve_proper.
  iIntros (wp1 wp2 ??) "#H". by iApply pwp_pre_mono.
Qed.

Local Definition pwp_def `{!irisGS_gen hlc Λ Σ} (s : stuckness)
    (e : expr Λ) (Φ : val Λ → iProp Σ) : iProp Σ :=
  bi_least_fixpoint (pwp_pre s Φ) e. 
Local Definition pwp_aux : seal (@pwp_def). Proof. by eexists. Qed.
Definition pwp := pwp_aux.(unseal).
Global Arguments pwp {hlc Λ Σ _}.
Local Lemma pwp_unseal `{!irisGS_gen hlc Λ Σ} : pwp = @pwp_def hlc Λ Σ _.
Proof. rewrite -pwp_aux.(seal_eq) //. Qed.

(** Notations without binder -- only parsing because they overlap with the
notations with binder. *)
Notation "'PWP' e @ s [{ Φ } ]" := (pwp s e%E Φ)
  (at level 20, e, Φ at level 200, only parsing) : bi_scope.
Notation "'PWP' e [{ Φ } ]" := (pwp NotStuck e%E Φ)
  (at level 20, e, Φ at level 200, only parsing) : bi_scope.
Notation "'PWP' e ? [{ Φ } ]" := (pwp MaybeStuck e%E Φ)
  (at level 20, e, Φ at level 200, only parsing) : bi_scope.

(** Notations with binder. *)
Notation "'PWP' e @ s [{ v , Q } ]" := (pwp s e%E (λ v, Q))
  (at level 20, e, Q at level 200,
   format "'[hv' 'PWP'  e  '/' @ '['  s  ']' '/' [{  '[' v ,  '/' Q  ']' } ] ']'") : bi_scope.
Notation "'PWP' e [{ v , Q } ]" := (pwp NotStuck e%E (λ v, Q))
  (at level 20, e, Q at level 200,
   format "'[hv' 'PWP'  e  '/' [{  '[' v ,  '/' Q  ']' } ] ']'") : bi_scope.
Notation "'PWP' e ? [{ v , Q } ]" := (pwp MaybeStuck e%E (λ v, Q))
  (at level 20, e, Q at level 200,
   format "'[hv' 'PWP'  e  '/' ? [{  '[' v ,  '/' Q  ']' } ] ']'") : bi_scope.

Section pwp.
Context `{!irisGS_gen hlc Λ Σ}.
Implicit Types s : stuckness.
Implicit Types P : iProp Σ.
Implicit Types Φ : val Λ → iProp Σ.
Implicit Types v : val Λ.
Implicit Types e : expr Λ.

(* Weakest pre *)
Lemma pwp_unfold s e Φ : PWP e @ s [{ Φ }] ⊣⊢ pwp_pre s Φ (flip (pwp s) Φ) e.
Proof. by rewrite pwp_unseal /pwp_def least_fixpoint_unfold. Qed.
Lemma pwp_ind s Φ Ψ :
  □ (∀ e, pwp_pre s Φ (λ e, Ψ e ∧ PWP e @ s [{ Φ }]) e -∗ Ψ e) -∗
  ∀ e, PWP e @ s [{ Φ }] -∗ Ψ e. 
Proof.
  iIntros "#IH" (e) "H". rewrite pwp_unseal.
  iApply (least_fixpoint_ind _ Ψ with "IH H").
Qed.

Global Instance pwp_ne s e n :
  Proper (pointwise_relation _ (dist n) ==> dist n) (pwp (Σ:=Σ) s e).
Proof.
  intros Φ1 Φ2 HΦ. rewrite !pwp_unseal.
  apply (least_fixpoint_ne _); last done. solve_proper.
Qed.
Global Instance pwp_proper s e :
  Proper (pointwise_relation _ (≡) ==> (≡)) (pwp (Σ:=Σ) s e).
Proof.
  by intros Φ Φ' ?; apply equiv_dist=> n; apply pwp_ne=> v; apply equiv_dist.
Qed.

Global Instance pwp_persistent s Φ e :
  (∀ v, Persistent (Φ v)) → Persistent (PWP e @ s [{ Φ }]).
Proof.
  intros. rewrite pwp_unseal.
  apply (least_fixpoint_persistent_absorbing _); simpl; apply _.
Qed.

Lemma pwp_value' s Φ v : PWP of_val v @ s [{ Φ }] ⊣⊢ Φ v.
Proof. rewrite pwp_unfold /pwp_pre to_of_val. auto. Qed.

Lemma pwp_strong_mono s1 s2 e Φ Ψ :
  s1 ⊑ s2 →
  PWP e @ s1 [{ Φ }] -∗ (∀ v, Φ v -∗ Ψ v) -∗ PWP e @ s2 [{ Ψ }].
Proof.
  iIntros (?) "H HΦ". iRevert (Ψ) "HΦ"; iRevert (e) "H". iApply pwp_ind.
  iIntros "!>" (e) "IH"; iIntros (Ψ) "HΦ".
  rewrite !pwp_unfold /pwp_pre. destruct (to_val e) as [v|] eqn:?.
  { by iApply "HΦ". }
  iIntros (σ1). iDestruct ("IH" $! σ1) as "[% IH]".
  iSplit; [by destruct s1, s2|]. iIntros (κ e2 σ2 efs Hstep).
  iDestruct ("IH" with "[//]") as "($ & $ & $ & IH)". by iApply "IH".
Qed.

Lemma pwp_bind K `{!LanguageCtx K} s e Φ :
  PWP e @ s [{ v, PWP K (of_val v) @ s [{ Φ }] }] ⊢ PWP K e @ s [{ Φ }].
Proof.
  revert Φ. cut (∀ Φ', PWP e @ s [{ Φ' }] -∗ ∀ Φ,
    (∀ v, Φ' v -∗ PWP K (of_val v) @ s [{ Φ }]) -∗ PWP K e @ s [{ Φ }]).
  { iIntros (help Φ) "H". iApply (help with "H"); auto. }
  iIntros (Φ') "H". iRevert (e) "H". iApply pwp_ind.
  iIntros "!>" (e) "IH". iIntros (Φ) "HΦ".
  rewrite /pwp_pre. destruct (to_val e) as [v|] eqn:He.
  { apply of_to_val in He as <-. by iApply "HΦ". }
  rewrite pwp_unfold /pwp_pre fill_not_val //.
  iIntros (σ1). iDestruct ("IH" $! σ1) as "[% IH]".
  iSplit.
  { iPureIntro. unfold reducible_no_obs in *.
    destruct s; naive_solver eauto using fill_step. }
  iIntros (κ e2 σ2 efs Hstep).
  destruct (fill_step_inv e σ1 κ e2 σ2 efs) as (e2'&->&?); auto.
  iDestruct ("IH" $! κ e2' σ2 efs with "[//]") as "($ & $ & $ & IH)".
  by iApply "IH".
Qed.

Lemma pwp_bind_inv K `{!LanguageCtx K} s e Φ :
  PWP K e @ s [{ Φ }] -∗ PWP e @ s [{ v, PWP K (of_val v) @ s [{ Φ }] }].
Proof.
  iIntros "H". remember (K e) as e' eqn:He'.
  iRevert (e He'). iRevert (e') "H". iApply pwp_ind.
  iIntros "!>" (e') "IH". iIntros (e ->).
  rewrite !pwp_unfold {2}/pwp_pre. destruct (to_val e) as [v|] eqn:He.
  { apply of_to_val in He as <-. rewrite !pwp_unfold.
    iApply (pwp_pre_mono with "[] IH"). by iIntros "!>" (e) "[_ ?]". }
  rewrite /pwp_pre fill_not_val //.
  iIntros (σ1). iDestruct ("IH" $! σ1) as "[% IH]".
  iSplit.
  { destruct s; eauto using reducible_no_obs_fill_inv. }
  iIntros (κ e2 σ2 efs Hstep).
  iDestruct ("IH" $! κ (K e2) σ2 efs with "[]")
    as "($ & $ & $ & IH)"; eauto using fill_step.
  by iApply "IH".
Qed.

Lemma pwp_twp E s e Φ : PWP e @ s [{ Φ }] -∗ WP e @ s; E [{ Φ }].
Proof.
  iIntros "H". iApply (twp_mask_mono _ ∅); first set_solver.
  clear E. iRevert (e) "H". iApply pwp_ind.
  iIntros "!>" (e) "IH". rewrite !twp_unfold /twp_pre /pwp_pre.
  destruct (to_val e) as [v|] eqn:?; [done|].
  iIntros (σ1 ns κs nt) "Hs". iDestruct ("IH" $! σ1) as "[% IH]".
  iModIntro. iSplit; [by destruct s|]. iIntros (κ e2 σ2 efs Hstep).
  iDestruct ("IH" with "[//]") as (-> -> ->) "[$ _] /=". iSplitR; [done|].
  by iSplitL "Hs"; first by iApply state_interp_mono.
Qed.

Lemma pwp_forall `{!Inhabited A} s e (Φ : A → val Λ → iProp Σ) :
  (∀ x, PWP e @ s [{ Φ x }]) -∗ PWP e @ s [{ v, ∀ x, Φ x v }].
Proof.
  iIntros "H". iAssert (PWP e @ s [{ _, True }])%I with "[#]" as "Hwp".
  { set (x := @inhabitant A _).
    iSpecialize ("H" $! x). iApply (pwp_strong_mono with "H"); auto. }
  iRevert "Hwp H". rewrite bi.intuitionistically_elim. iRevert (e).
  iApply pwp_ind. iIntros "!> %e IH H".
  rewrite !pwp_unfold /pwp_pre. destruct (to_val e) as [v|] eqn:He.
  { iIntros (x). apply of_to_val in He as <-. iApply pwp_value'. iApply "H". }
  iIntros (σ1). iDestruct ("IH" $! σ1) as "[$ IH]".
  iIntros (κ e2 σ2 efs Hstep).
  iDestruct ("IH" with "[//]") as "($ & $ & $ & IH) /=". iApply "IH".
  iIntros (x). iSpecialize ("H" $! x). rewrite {1}pwp_unfold /pwp_pre He.
  iDestruct ("H" $! σ1) as "[_ H]".
  iDestruct ("H" with "[//]") as "(_ & _ & _ & $)".
Qed.

Lemma pwp_intuitionistically_2 s e Φ :
  □ PWP e @ s [{ Φ }] -∗ PWP e @ s [{ v, □ Φ v }].
Proof.
  iIntros "#H". iAssert (PWP e @ s [{ v, Φ v }])%I as "H'"; first done.
  iRevert "H H'". rewrite {1}bi.intuitionistically_elim. iRevert (e).
  iApply pwp_ind. iIntros "!> %e IH #H".
  rewrite !pwp_unfold /pwp_pre. destruct (to_val e) as [v|] eqn:He; first done.
  iIntros (σ1). iDestruct ("IH" $! σ1) as "[$ IH]".
  iIntros (κ e2 σ2 efs Hstep).
  iDestruct ("IH" with "[//]") as "($ & $ & $ & IH) /=". iApply "IH".
  iIntros "!>". iDestruct ("H" $! σ1) as "[_ H']".
  iDestruct ("H'" with "[//]") as "(_ & _ & _ & $)".
Qed.

Lemma pwp_pure_step `{!Inhabited (state Λ)} s e1 e2 φ n Φ :
  PureExec φ n e1 e2 →
  φ →
  PWP e2 @ s [{ Φ }] ⊢ PWP e1 @ s [{ Φ }].
Proof.
  iIntros (Hexec Hφ) "Hwp". specialize (Hexec Hφ).
  iInduction Hexec as [e|n e1 e2 e3 [Hsafe Hstep]] "IH"; simpl; first done.
  iDestruct ("IH" with "Hwp") as "Hwp {IH}".
  iEval (rewrite pwp_unfold /pwp_pre). destruct (to_val e1) as [v|] eqn:He.
  { specialize (Hsafe inhabitant). apply reducible_no_obs_reducible in Hsafe.
    apply reducible_not_val in Hsafe. congruence. }
  iIntros (σ1). iSplit; [by destruct s|].
  iIntros (κ e2' σ2 efs Hstep').
  destruct (Hstep _ _ _ _ _ Hstep') as (-> & -> & -> & ->). auto.
Qed.

(** * Derived rules *)
Lemma pwp_mono s e Φ Ψ :
  (∀ v, Φ v ⊢ Ψ v) → PWP e @ s [{ Φ }] ⊢ PWP e @ s [{ Ψ }]. 
Proof.
  iIntros (HΦ) "H"; iApply (pwp_strong_mono with "H"); auto.
  iIntros (v) "?". by iApply HΦ.
Qed.
Lemma pwp_stuck_mono s1 s2 e Φ :
  s1 ⊑ s2 → PWP e @ s1 [{ Φ }] ⊢ PWP e @ s2 [{ Φ }].
Proof. iIntros (?) "H". iApply (pwp_strong_mono with "H"); auto. Qed.
Lemma pwp_stuck_weaken s e Φ :
  PWP e @ s [{ Φ }] ⊢ PWP e ?[{ Φ }].
Proof. apply pwp_stuck_mono. by destruct s. Qed.
Global Instance pwp_mono' s e :
  Proper (pointwise_relation _ (⊢) ==> (⊢)) (pwp (Σ:=Σ) s e).
Proof. by intros Φ Φ' ?; apply pwp_mono. Qed.

Lemma pwp_value s Φ e v : IntoVal e v → PWP e @ s [{ Φ }] ⊣⊢ Φ v.
Proof. intros <-. apply pwp_value'. Qed.

Lemma pwp_frame_l s e Φ R : R ∗ PWP e @ s [{ Φ }] ⊢ PWP e @ s [{ v, R ∗ Φ v }].
Proof. iIntros "[? H]". iApply (pwp_strong_mono with "H"); auto with iFrame. Qed.
Lemma pwp_frame_r s e Φ R : PWP e @ s [{ Φ }] ∗ R ⊢ PWP e @ s [{ v, Φ v ∗ R }].
Proof. iIntros "[H ?]". iApply (pwp_strong_mono with "H"); auto with iFrame. Qed.

Lemma pwp_wand s e Φ Ψ :
  PWP e @ s [{ Φ }] -∗ (∀ v, Φ v -∗ Ψ v) -∗ PWP e @ s [{ Ψ }].
Proof. by apply pwp_strong_mono. Qed.
Lemma pwp_wand_l s e Φ Ψ :
  (∀ v, Φ v -∗ Ψ v) ∗ PWP e @ s [{ Φ }] -∗ PWP e @ s [{ Ψ }].
Proof. iIntros "[H Hwp]". iApply (pwp_wand with "Hwp H"). Qed.
Lemma pwp_wand_r s e Φ Ψ :
  PWP e @ s [{ Φ }] ∗ (∀ v, Φ v -∗ Ψ v) -∗ PWP e @ s [{ Ψ }].
Proof. iIntros "[Hwp H]". iApply (pwp_wand with "Hwp H"). Qed.
Lemma pwp_frame_wand s e Φ R :
  R -∗ PWP e @ s [{ v, R -∗ Φ v }] -∗ PWP e @ s [{ Φ }].
Proof.
  iIntros "HR HPWP". iApply (pwp_wand with "HPWP").
  iIntros (v) "HΦ". by iApply "HΦ".
Qed.

Lemma pwp_intuitionistically s Φ e :
  PWP e @ s [{ v, □ Φ v }] ⊣⊢ □ PWP e @ s [{ Φ }].
Proof.
  iSplit.
  - iIntros "#H !>". iApply (pwp_wand with "H"); auto.
  - iApply pwp_intuitionistically_2.
Qed.

Lemma pwp_wp E s e Φ : PWP e @ s [{ Φ }] -∗ WP e @ s; E {{ Φ }}.
Proof. iIntros "H". iApply twp_wp. by iApply pwp_twp. Qed.
End pwp.

(** Proofmode class instances *)
Section proofmode_classes.
  Context `{!irisGS_gen hlc Λ Σ}.
  Implicit Types P Q : iProp Σ.
  Implicit Types Φ : val Λ → iProp Σ.
  Implicit Types v : val Λ.
  Implicit Types e : expr Λ.

  Global Instance frame_pwp p s e R Φ Ψ :
    (∀ v, Frame p R (Φ v) (Ψ v)) →
    Frame p R (PWP e @ s [{ Φ }]) (PWP e @ s [{ Ψ }]) | 2.
  Proof.
    rewrite /Frame=> HR. rewrite pwp_frame_l. apply pwp_mono, HR.
  Qed.
End proofmode_classes.
