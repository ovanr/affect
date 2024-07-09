
From iris.proofmode Require Import base tactics classes.
From iris.program_logic Require Import weakestpre.

From stdpp Require Import base gmap.

(* Hazel Reasoning *)
From hazel.program_logic Require Import weakest_precondition 
                                        state_reasoning.

(* Local imports *)
From affect.lib Require Import base.
From affect.lang Require Import affect.
From affect.logic Require Import sem_def.
From affect.logic Require Import sem_row.

Section env_lemmas_base.
  
  Context {Σ : gFunctors}.

  Implicit Types Γ Γ₁ Γ₂ Γ₃ Δ : env Σ.
  Implicit Types τ τ₁ τ₂ : sem_ty Σ.

  Lemma env_dom_nil :
    env_dom (Σ:= Σ) [] = [].
  Proof. done. Qed.
  
  Lemma env_dom_cons x τ Γ :
    env_dom ((x, τ) :: Γ) = x :: env_dom Γ.
  Proof. done. Qed.
  
  Lemma env_dom_app Γ₁ Γ₂ :
    env_dom (Γ₁ ++ Γ₂) = env_dom Γ₁ ++ env_dom Γ₂.
  Proof. by rewrite -map_app. Qed.
  
  Lemma env_sem_typed_empty vs : ⟦ ([] : env Σ) ⟧ vs = True%I.
  Proof. done. Qed.
  
  Lemma env_sem_typed_cons  x τ Γ' vs : 
      ⟦ (x, τ) :: Γ' ⟧ vs = ((∃ v, ⌜ vs !! x = Some v ⌝ ∗ τ v) ∗ ⟦ Γ' ⟧ vs)%I.
  Proof. done. Qed.
  
  Lemma env_sem_typed_insert Γ vs (x : string) v :
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
  
  Lemma env_sem_typed_delete Γ vs (x : string) :
    x ∉ (env_dom Γ) →
    ⟦ Γ ⟧ vs ⊣⊢ ⟦ Γ ⟧ (binder_delete x vs).
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
      + iExists _. iIntros "{$Hw} !% /=". 
        by rewrite lookup_delete_ne.
      + iApply "IH"; last done. iPureIntro. 
        destruct (not_elem_of_cons (env_dom Γ') x y) as [[ ] _]; done.
    - iSplitL "Hw".
      + iExists w.  iIntros "{$Hw} !%". 
        destruct (decide (y = x)) as [->|]. 
        { destruct Helem. rewrite env_dom_cons. apply elem_of_list_here. }
        simpl in Hvs.
        by rewrite lookup_delete_ne in Hvs.
      + iApply "IH"; last done. iPureIntro. 
        destruct (not_elem_of_cons (env_dom Γ') x y) as [[ ] _]; done.
  Qed.
  
  Lemma env_sem_typed_app Γ₁ Γ₂ vs :
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

End env_lemmas_base.

Global Ltac solve_sem_typed_insert :=
  rewrite env_sem_typed_insert; try (simplify_eq; done); progress iFrame "%#∗".

Global Ltac solve_sem_typed_insert_inv :=
  rewrite -env_sem_typed_insert; try (simplify_eq; done); progress iFrame "%#∗".

Global Ltac solve_env := 
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
  
Section env_lemmas_set_operations.

  Context {Σ : gFunctors}.

  Implicit Types Γ Γ₁ Γ₂ Γ₃ Δ : env Σ.
  Implicit Types τ τ₁ τ₂ : sem_ty Σ.

  Lemma env_sem_typed_union Γ ws vs :
    ⟦ Γ ⟧ vs ⊢ ⟦ Γ ⟧ (vs ∪ ws).
  Proof. 
    iIntros "HΓ". iInduction Γ as [|[x τ] Γ'] "IH"; first done.
    rewrite !env_sem_typed_cons.
    iDestruct "HΓ" as "[(%m & %Hrw & Hx) HΓ']".
    rewrite -/env_sem_typed. 
    iSplitL "Hx"; [|by iApply "IH"].
    iExists m; iFrame; iPureIntro.
    by apply lookup_union_Some_l.
  Qed.
  
  Lemma env_sem_typed_delete_union Γ Δ ws vs :
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
  
  Lemma env_sem_typed_difference_delete Γ Δ vs ws :
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
  
  Lemma env_sem_typed_delete_disjoint Γ Δ vs  :
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
  
  Lemma env_sem_typed_union_difference_delete Γ Δ vs ws :
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
  
End env_lemmas_set_operations.

Section env_row_sub_typing.

  Lemma row_env_sub_copy {Σ} (ρ : sem_row Σ) (Γ : env Σ) : 
    copy_env Γ -∗ ρ ≼ₑ Γ.
  Proof.
    iIntros "#HΓcpy %vs %v %Φ !# Hρ HΓ.".
    iDestruct ("HΓcpy" with "HΓ.") as "#HΓ".
    iApply (pmono_prot_prop Σ ρ); last iApply "Hρ".  
    iIntros "!# % $ //".
  Qed.

End env_row_sub_typing.

Section env_sub_typing.

  Context {Σ : gFunctors}.

  Implicit Types Γ Γ₁ Γ₂ Γ₃ : env Σ.
  Implicit Types τ τ₁ τ₂ : sem_ty Σ.

  Lemma env_le_refl Γ : ⊢ Γ ≤E Γ.
  Proof. iIntros "!# % $". Qed.
  
  Lemma env_le_trans Γ₁ Γ₂ Γ₃ : 
    Γ₁ ≤E Γ₂ -∗
    Γ₂ ≤E Γ₃ -∗
    Γ₁ ≤E Γ₃.
  Proof.
    iIntros "#HΓ₁₂ #HΓ₂₃ !# %vs HΓ₁ //=".  
    iApply "HΓ₂₃". by iApply "HΓ₁₂".
  Qed.
  
  Lemma env_le_cons Γ₁ Γ₂ τ₁ τ₂ x :
    Γ₁ ≤E Γ₂ -∗
    τ₁ ≤T τ₂ -∗
    (x, τ₁) :: Γ₁ ≤E (x, τ₂) :: Γ₂.
  Proof.
    iIntros "#HΓ₁₂ #Hτ₁₂ !# %vs [%v (Hlookup & Hv & HΓ₁)]".
    iExists v. iFrame. iSplitR "HΓ₁"; last (by iApply "HΓ₁₂").
    by iApply "Hτ₁₂".
  Qed.
  
  Lemma env_le_copy_contraction Γ x τ :
    copy_ty τ -∗
    (x, τ) :: Γ ≤E (x, τ) :: (x, τ) :: Γ.
  Proof.
    iIntros "#Hcpy !# %vs".
    iIntros "//= [%w (%Hrw & Hτ & HΓ)]". 
    iDestruct ("Hcpy" with "Hτ") as "#Hτ'".
    by do 2 (iExists w; iFrame "%#").
  Qed.
  
  Lemma env_le_bring_forth Γ n x τ :
    nth_error Γ n = Some (x, τ) →
    ⊢ Γ ≤E (x, τ) :: (list_delete n Γ) .
  Proof.
    iInduction n as [|] "IH" forall (Γ); iIntros (Hnth vs);
    iIntros "!# HΓ"; simpl in Hnth; destruct Γ; first done; simplify_eq; first done.
    destruct p; simpl. rewrite !env_sem_typed_cons.
    iDestruct "HΓ" as "[$ HΓ]". rewrite -env_sem_typed_cons.
    by iApply "IH". 
  Qed.
  
  Lemma env_le_bring_forth_rev Γ n x τ :
    nth_error Γ n = Some (x, τ) →
    ⊢ (x, τ) :: (list_delete n Γ) ≤E Γ.
  Proof.
    iInduction n as [|] "IH" forall (Γ); iIntros (Hnth vs);
    simpl in Hnth; 
    destruct Γ as [|[y κ] Γ']; first done; 
    simplify_eq; simpl; first (iIntros "!# $").
    iIntros "!# [%v (? & ? & [%w (? & ? & ?)])]". 
    iExists w. iFrame. iApply "IH"; first done.
    iExists v. iFrame.
  Qed.
  
  Lemma env_le_swap_second Γ x y τ₁ τ₂ : 
    ⊢ (y, τ₂) :: (x, τ₁) :: Γ ≤E (x, τ₁) :: (y, τ₂) :: Γ.
  Proof.
    pose proof (env_le_bring_forth_rev ((x, τ₁) :: (y, τ₂) :: Γ) 1 y τ₂).
    by apply H.
  Qed.
  
  Lemma env_le_swap_third Γ x y z τ₁ τ₂ τ₃: 
    ⊢ (z, τ₃) :: (x, τ₁) :: (y, τ₂) :: Γ ≤E (x, τ₁) :: (y, τ₂) :: (z, τ₃) :: Γ.
  Proof.
    pose proof (env_le_bring_forth_rev ((x, τ₁) :: (y, τ₂) :: (z, τ₃) :: Γ) 2 z τ₃).
    by apply H.
  Qed.
  
  Lemma env_le_swap_fourth Γ x y z z' τ₁ τ₂ τ₃ τ₄: 
    ⊢ (z', τ₄) :: (x, τ₁) :: (y, τ₂) :: (z, τ₃) :: Γ ≤E (x, τ₁) :: (y, τ₂) :: (z, τ₃) :: (z', τ₄) :: Γ.
  Proof.
    pose proof (env_le_bring_forth_rev ((x, τ₁) :: (y, τ₂) :: (z, τ₃) :: (z', τ₄) :: Γ) 3 z' τ₄).
    by apply H.
  Qed.
  
  Lemma env_le_swap_env_singl Γ x τ : 
    ⊢ (x, τ) :: Γ ≤E Γ ++ [(x, τ)].
  Proof.
    induction Γ as [|[y κ] Γ'].
    { simpl. iIntros "!# % $". }
    rewrite -app_comm_cons.
    iApply env_le_trans; [iApply env_le_swap_second|].
    iApply env_le_cons; last (iIntros "!# % $").
    iApply IHΓ'.
  Qed.
  
  Lemma env_le_weaken Γ x τ :
    ⊢ (x, τ) :: Γ ≤E Γ.
  Proof. iIntros "!# % [% (? & ? & $)]". Qed.

End env_sub_typing.
