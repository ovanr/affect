
From iris.proofmode Require Import base tactics classes.
From iris.program_logic Require Import weakestpre.

From stdpp Require Import base gmap.

(* Hazel Reasoning *)
From program_logic Require Import weakest_precondition 
                                  state_reasoning.

(* Local imports *)
From affine_tes.lib Require Import base.
From affine_tes.lang Require Import hazel.
From affine_tes.lang Require Import subst_map.
From affine_tes.logic Require Import iEff.
From affine_tes.logic Require Import sem_def.
From affine_tes.logic Require Import sem_types.

Lemma env_dom_nil {Σ} :
  env_dom (Σ:= Σ) [] = [].
Proof. done. Qed.

Lemma env_dom_cons {Σ} x τ (Γ : env Σ) :
  env_dom ((x, τ) :: Γ) = x :: env_dom Γ.
Proof. done. Qed.

Lemma env_dom_app {Σ} (Γ₁ Γ₂ : env Σ) :
  env_dom (Γ₁ ++ Γ₂) = env_dom Γ₁ ++ env_dom Γ₂.
Proof. by rewrite -map_app. Qed.

Lemma env_sem_typed_empty `{irisGS eff_lang Σ} vs : ⟦ [] ⟧ vs = True%I.
Proof. done. Qed.

Lemma env_sem_typed_cons `{irisGS eff_lang Σ} x τ Γ' vs : 
    ⟦ (x, τ) :: Γ' ⟧ vs = ((∃ v, ⌜ vs !! x = Some v ⌝ ∗ τ v) ∗ ⟦ Γ' ⟧ vs)%I.
Proof. done. Qed.

Lemma env_sem_typed_insert `{irisGS eff_lang Σ} Γ vs (x : string) v :
  x ∉ (env_dom Γ) →
  ⟦ Γ ⟧ vs ⊣⊢ ⟦ Γ ⟧ (binder_insert x v vs).
Proof.
  intros Helem. 
  iInduction Γ as [|[y τ] Γ'] "IH";
    first (iSplit; iIntros; by rewrite env_sem_typed_empty). 
  rewrite !env_sem_typed_cons; iSplit; iIntros "Henv";
  iDestruct ("Henv") as "((%w & %Hvs & Hw) & HΓ')".
  assert (x ≠ y).
  { rewrite env_dom_cons in Helem.
    destruct (not_elem_of_cons (env_dom Γ') x y) as [[ ] _]; done. }
  - iSplitL "Hw".
    + iExists _. iIntros "{$Hw} !%". 
      destruct (decide (y = x)) as [->|]. 
      { destruct Helem. rewrite env_dom_cons. apply elem_of_list_here. }
      by rewrite lookup_insert_ne.
    + iApply "IH"; last done. iPureIntro. 
      destruct (not_elem_of_cons (env_dom Γ') x y) as [[ ] _]; done.
  - iSplitL "Hw".
    + iExists w.  iIntros "{$Hw} !%". 
      destruct (decide (y = x)) as [->|]. 
      { destruct Helem. rewrite env_dom_cons. apply elem_of_list_here. }
      by rewrite lookup_insert_ne in Hvs.
    + iApply "IH"; last done. iPureIntro. 
      destruct (not_elem_of_cons (env_dom Γ') x y) as [[ ] _]; done.
Qed.

Ltac solve_sem_typed_insert :=
  rewrite env_sem_typed_insert; try (simplify_eq; done); progress iFrame "%#∗".

Ltac solve_sem_typed_insert_inv :=
  rewrite -env_sem_typed_insert; try (simplify_eq; done); progress iFrame "%#∗".

Ltac solve_env := 
  repeat (
    done ||
    iIntros || 
    iExists _ || 
    iPureIntro ||
    iSplit || 
    (progress iFrame "%#∗") ||
    (progress simpl) ||
    apply lookup_insert || 
    rewrite lookup_insert_ne || 
    apply lookup_delete ||
    rewrite env_sem_typed_empty ||
    rewrite env_sem_typed_cons ||
    solve_sem_typed_insert ||
    solve_sem_typed_insert_inv
  ).

Lemma env_sem_typed_union `{irisGS eff_lang Σ} Γ ws vs :
  ⟦ Γ ⟧ vs ⊢ ⟦ Γ ⟧ (vs ∪ ws).
Proof. 
  iIntros "HΓ". iInduction Γ as [|[x τ] Γ'] "IH"; first done.
  rewrite !env_sem_typed_cons.
  iDestruct "HΓ" as "[(%m & %Hrw & Hx) HΓ']".
  rewrite -/env_sem_typed. 
  iSplitL "Hx"; [|by iApply "IH"].
  iExists m; iFrame; iPureIntro.
  by rewrite lookup_union_l.
Qed.

Lemma env_sem_typed_delete_union `{irisGS eff_lang Σ} Γ (Δ : env Σ) ws vs :
  env_dom Γ ⊆ env_dom Δ →
  ⟦ Γ ⟧ vs ⊣⊢ ⟦ Γ ⟧ (delete (env_dom Δ) ws ∪ vs).
Proof.
  intros ?. iSplit.
  - iInduction Γ as [|[x τ] Γ'] "IH"; first solve_env. 
    rewrite !env_sem_typed_cons.
    iIntros "/= [(%w & %Hrw & Hw) HΓ']".
    assert (Hseq' : env_dom Γ' ⊆ env_dom Δ). 
    { eapply subset_cons. by erewrite <- env_dom_cons. }
    assert (x ∈ (env_dom Δ)).
    { eapply subset_cons_elem. by erewrite <- env_dom_cons. }
    iSplitL "Hw";[| iApply ("IH" with "[] HΓ'"); by iPureIntro].
    iExists w. iFrame. iPureIntro. 
    rewrite (delete_list_elem_of _ x); last done.
    rewrite lookup_union_r; first done. apply lookup_delete.
  - iInduction Γ as [|[x τ] Γ'] "IH"; first solve_env.
    rewrite !env_sem_typed_cons.
    iIntros "[(%v & %Hrw & Hτ) HΓ']".
    iSplitL "Hτ".
    + iExists v. iIntros "{$Hτ} !%".
      rewrite -(lookup_union_r (delete (env_dom Δ) ws)); first done.
      rewrite (delete_list_elem_of _ x); first (apply lookup_delete).
      eapply subset_cons_elem. by erewrite <- env_dom_cons.
    + iApply "IH"; last done.
      iPureIntro. eapply subset_cons. by erewrite <- env_dom_cons.
Qed.

Lemma env_sem_typed_difference_delete `{irisGS eff_lang Σ} Γ (Δ : env Σ) vs ws :
  env_dom Γ ⊆ env_dom Δ → ⟦ Γ ⟧ vs ⊣⊢ ⟦ Γ ⟧ (vs ∖ delete (env_dom Δ) ws).
Proof.
  intros ?.
  iInduction Γ as [|[x τ] Γ'] "IH"; first (iSplit; solve_env).
  rewrite !env_sem_typed_cons; iSplit;
  iIntros "/= [(%v & %Hrw & Hτ) HΓ']".
  assert (Hseq' : env_dom Γ' ⊆ env_dom Δ).
  { eapply subset_cons. by erewrite <- env_dom_cons. }
  assert (x ∈ (env_dom Δ)).
  { eapply subset_cons_elem. by erewrite <- env_dom_cons. }
  - iSplitL "Hτ".
    + iExists _. iFrame. iPureIntro. 
      rewrite (delete_list_elem_of _ x); last done. 
      by rewrite lookup_difference_delete. 
    + iApply ("IH" with "[] HΓ'"); eauto. 
  - iSplitL "Hτ".
    + iExists _. iFrame. iPureIntro. 
      rewrite (delete_list_elem_of _ x) in Hrw; 
        [|eapply subset_cons_elem; by erewrite <- env_dom_cons].
      by rewrite lookup_difference_delete in Hrw.
    + iApply ("IH" with "[] HΓ'"); eauto. 
      iPureIntro. eapply subset_cons. by erewrite <- env_dom_cons.
Qed.

Lemma env_sem_typed_delete_disjoint `{irisGS eff_lang Σ} Γ (Δ : env Σ) vs  :
  env_dom Γ ## env_dom Δ → ⟦ Γ ⟧ vs ⊣⊢ ⟦ Γ ⟧ (delete (env_dom Δ) vs).
Proof. 
  iIntros (?).
  iInduction Γ as [|[x τ] Γ'] "IH"; first (iSplit; solve_env). 
  rewrite !env_sem_typed_cons; iSplit;
  iIntros "/= [(%v & %Hrw & Hτ) HΓ']";
  assert (Hseq' : env_dom Γ' ## env_dom Δ)
    by (eapply disjoint_cons; by erewrite <- env_dom_cons);
  assert (x ∉ (env_dom Δ)) by 
    (eapply disjoint_cons_not_elem; by erewrite <- env_dom_cons).
  - iSplitL "Hτ".
    + iExists v. iIntros "{$Hτ} !%".
      by rewrite lookup_delete_not_elem.
    + by iApply "IH".
  - iSplitL "Hτ".
    + iExists v. iIntros "{$Hτ} !%".
      by rewrite lookup_delete_not_elem in Hrw.
    + by iApply "IH".
Qed. 

Lemma env_sem_typed_union_difference_delete `{irisGS eff_lang Σ} Γ (Δ : env Σ) vs ws :
  env_dom Γ ## env_dom Δ → ⟦ Γ ⟧ (vs ∪ ws ∖ (delete (env_dom Δ) ws)) ⊢ ⟦ Γ ⟧ vs.
Proof. 
  intros ?.
  iInduction Γ as [|[x τ] Γ'] "IH"; first solve_env.
  rewrite !env_sem_typed_cons.
  iIntros "/= [(%v & %Hrw & Hτ) HΓ']".
  assert (Hseq' : env_dom Γ' ## env_dom Δ)
    by (eapply disjoint_cons; by erewrite <- env_dom_cons).
  assert (x ∉ (env_dom Δ)) by 
    (eapply disjoint_cons_not_elem; by erewrite <- env_dom_cons).
  iSplitL "Hτ".
  + iExists v. iIntros "{$Hτ} !%".
    by rewrite lookup_union_delete_disjoint in Hrw.
  + by iApply "IH".
Qed.

Lemma env_sem_typed_app `{irisGS eff_lang Σ} Γ₁ Γ₂ vs :
  ⟦ Γ₁ ++ Γ₂ ⟧ vs ⊣⊢ ⟦ Γ₁ ⟧ vs ∗ ⟦ Γ₂ ⟧ vs.
Proof. 
  iInduction Γ₁ as [|[y τ] Γ₁'] "IH". 
  { iSplit; [iIntros; by iFrame|iIntros "[_ H] {$H}"]. }
  iSplit; rewrite !env_sem_typed_cons; iIntros "HΓ₁₂". 
  - iDestruct "HΓ₁₂" as "($ & HΓ₁'₂)". by iApply "IH".
  - iDestruct ("HΓ₁₂") as "[[Hτ HΓ₁'] HΓ₂]".
    rewrite -/app. iFrame. iApply ("IH" with "[HΓ₁' HΓ₂]").
    iFrame.
Qed.

Lemma env_sem_typed_mk_moved `{irisGS eff_lang Σ} vs Γ :
  ⟦ Γ ⟧ vs -∗
  □ ⟦ map (prod_map id (const Moved)) Γ ⟧ vs ∗ ⟦ Γ ⟧ vs.
Proof.
  iIntros "HΓ". iInduction Γ as [|x Γ'] "IH"; first done. simpl.
  destruct x. simpl. rewrite !env_sem_typed_cons.
  iDestruct "HΓ" as "[(%w & -> & Hw) HΓ']". 
  iSpecialize ("IH" with "HΓ'"). 
  rewrite bi.intuitionistically_sep.
  rewrite -bi.sep_assoc. iSplitR.
  { by iExists w. }
  iDestruct "IH" as "[HΓ'T HΓ']". iFrame.
  { iExists w. by iFrame. }
Qed.
