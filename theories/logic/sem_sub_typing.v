
(* sem_sub_typing.v *)

(* This file contains the definition sub-typing relations and 
   Copyable (persistent) types
*)

From iris.algebra Require Import ofe.
From iris.proofmode Require Import base tactics classes.
From iris.base_logic.lib Require Import iprop invariants.

(* Hazel Reasoning *)
From hazel.program_logic Require Import weakest_precondition 
                                        tactics 
                                        state_reasoning.

(* Local imports *)
From haffel.lang Require Import hazel.
From haffel.lang Require Import subst_map.
From haffel.logic Require Import sem_def.
From haffel.logic Require Import sem_types.
From haffel.logic Require Import sem_env.


Section sub_typing.

  Context `{!heapGS Σ}.

  Lemma sig_le_refl (σ : sem_sig Σ) : ⊢ σ ≤S σ.
  Proof. iApply iEff_le_refl. Qed.
  
  Lemma sig_le_trans (σ₁ σ₂ σ₃: sem_sig Σ) : 
      σ₁ ≤S σ₂ -∗
      σ₂ ≤S σ₃ -∗
      σ₁ ≤S σ₃. 
  Proof. 
    iIntros "#Hσ₁₂ #Hσ₂₃". rewrite /sig_le /tc_opaque. 
    iApply iEff_le_trans; [iApply "Hσ₁₂"|iApply "Hσ₂₃"]. 
  Qed.
  
  Lemma sig_le_nil (σ : sem_sig Σ) :
    ⊢ ⊥ ≤S σ.
  Proof. iApply iEff_le_bottom. Qed.

  Lemma sig_le_eff_rec m₁ m₂ (ι₁ ι₂ κ₁ κ₂ : sem_sig Σ → sem_ty Σ → sem_ty Σ)
    `{NonExpansive2 ι₁, NonExpansive2 ι₂, NonExpansive2 κ₁, NonExpansive2 κ₂ } :
    mode_le m₁ m₂ →
    □ (∀ α σ σ', σ ≤S σ' -∗ (ι₁ σ α) ≤T (ι₂ σ' α)) -∗
    □ (∀ α σ σ', σ ≤S σ' -∗ (κ₂ σ' α) ≤T (κ₁ σ α)) -∗
    (μ∀TS: θ , α , ι₁ θ α ⇒ κ₁ θ α | m₁) ≤S (μ∀TS: θ , α , ι₂ θ α ⇒ κ₂ θ α | m₂).
  Proof.
    iIntros (mle) "#Hι₁₂ #Hκ₂₁". iLöb as "IH".
    iIntros (v Φ) "!#".
    rewrite !sem_sig_eff_rec_eq.
    iIntros "(%α & %w & <- & Hι₁ & HκΦ₁)".
    iExists α, w; iSplitR; first done.
    iSplitL "Hι₁".
    { iNext. iApply ("Hι₁₂" with "IH Hι₁"). }
    simpl. destruct m₁, m₂; rewrite /mode_le in mle; try tauto; simpl.
    - iIntros (b) "Hκ₂". iApply "HκΦ₁".
      iNext. iApply ("Hκ₂₁" with "IH Hκ₂").
    - iIntros (b) "Hκ₂". iApply "HκΦ₁".
      iNext. iApply ("Hκ₂₁" with "IH Hκ₂").
    - iDestruct "HκΦ₁" as "#HκΦ₁".
      iIntros "!# %b Hκ₂". iApply "HκΦ₁".
      iNext. iApply ("Hκ₂₁" with "IH Hκ₂").
  Qed.

  Lemma ty_le_refl (τ : sem_ty Σ) : ⊢ τ ≤T τ.
  Proof. iIntros "!# % $". Qed.
  
  Lemma ty_le_trans (τ₁ τ₂ τ₃ : sem_ty Σ) :
    τ₁ ≤T τ₂ -∗
    τ₂ ≤T τ₃ -∗
    τ₁ ≤T τ₃.
  Proof. 
    iIntros "#Hτ₁₂ #Hτ₂₃ !# %v Hτ₁". 
    iApply "Hτ₂₃". by iApply "Hτ₁₂".
  Qed.
  
  Lemma ty_le_void (τ : sem_ty Σ) :
    ⊢ Void ≤T τ.
  Proof. iIntros "% !# []". Qed.

  Lemma ty_le_cpy (τ : sem_ty Σ) :
    copy_ty τ -∗
    τ ≤T '! τ.
  Proof. 
    iIntros "#Hcpy !# %v Hτ". 
    iDestruct ("Hcpy" with "Hτ") as "#Hτ'".
    iIntros "!# {$#Hτ'}". 
  Qed.
        
  Lemma ty_le_cpy_inv (τ : sem_ty Σ) :
    ⊢ ('! τ) ≤T τ.
  Proof. iIntros "!# %v #$". Qed.

  Lemma ty_le_u2aarr (τ κ : sem_ty Σ) (σ : sem_sig Σ) :
    ⊢ (τ -{ σ }-> κ) ≤T (τ -{ σ }-∘ κ).
  Proof.
    iIntros "!# %v #Hτκ". iIntros (w) "Hτ /=".
    
    iApply (ewp_pers_mono with "[Hτ Hτκ]"); [by iApply "Hτκ"|].
    iIntros "!# % $ //=".
  Qed.

  Lemma ty_le_aarr (τ₁ κ₁ τ₂ κ₂ : sem_ty Σ) (σ σ' : sem_sig Σ) :
    σ ≤S σ' -∗
    τ₂ ≤T τ₁ -∗
    κ₁ ≤T κ₂ -∗
    (τ₁ -{ σ }-∘ κ₁) ≤T (τ₂ -{ σ' }-∘ κ₂).
  Proof.
    iIntros "#Hσ  #Hτ₂₁ #Hκ₁₂ !# %v Hτκ₁ %w Hτ".
    iApply ewp_ms_prot_mono; [iApply "Hσ"|].
    iApply (ewp_pers_mono with "[Hτκ₁ Hτ]").
    { iApply ("Hτκ₁" with "[Hτ]"); by iApply "Hτ₂₁". }
    iIntros "!# % Hκ !>". by iApply "Hκ₁₂".
  Qed.
  
  Lemma ty_le_uarr (τ₁ κ₁ τ₂ κ₂ : sem_ty Σ) (σ σ' : sem_sig Σ) :
    σ ≤S σ' -∗
    τ₂ ≤T τ₁ -∗
    κ₁ ≤T κ₂ -∗
    (τ₁ -{ σ }-> κ₁) ≤T (τ₂ -{ σ' }-> κ₂).
  Proof.
    iIntros "#Hσ #Hτ₂₁ #Hκ₁₂ !# %v #Hτκ₁ %w !# Hτ₂".
    iApply ewp_ms_prot_mono; [iApply "Hσ"|].
    iApply (ewp_pers_mono with "[Hτκ₁ Hτ₂]").
    { iApply ("Hτκ₁" with "[Hτ₂]"); by iApply "Hτ₂₁". }
    iIntros "!# % Hκ !>". by iApply "Hκ₁₂".
  Qed.
  
  Lemma ty_le_ref (τ₁ τ₂ : sem_ty Σ) :
    τ₁ ≤T τ₂ -∗
    (Ref τ₁) ≤T (Ref τ₂).
  Proof.
    iIntros "#Hτ₁₂ !# %v (%l & -> & (%w & Hl & Hτw))".
    iExists l. iSplit; first done.
    iExists w. iFrame. by iApply "Hτ₁₂".
  Qed.

  Lemma ty_le_prod (τ₁ τ₂ κ₁ κ₂ : sem_ty Σ) :
    τ₁ ≤T τ₂ -∗
    κ₁ ≤T κ₂ -∗
    (τ₁ × κ₁) ≤T (τ₂ × κ₂).
  Proof.
    iIntros "#Hτ₁₂ #Hκ₁₂ !# %v (%w₁ & %w₂ & -> &Hw₁ & Hw₂)".
    iExists w₁, w₂. iSplit; first done. iSplitL "Hw₁".
    { by iApply "Hτ₁₂". }
    by iApply "Hκ₁₂".
  Qed.
  
  Lemma ty_le_sum (τ₁ τ₂ κ₁ κ₂ : sem_ty Σ) :
    τ₁ ≤T τ₂ -∗
    κ₁ ≤T κ₂ -∗
    (τ₁ + κ₁) ≤T (τ₂ + κ₂).
  Proof.
    iIntros "#Hτ₁₂ #Hκ₁₂ !# %v (%v' & [(-> & Hτ₁)|(-> & Hκ₁)])"; iExists v'. 
    - iLeft. iSplit; first done. by iApply "Hτ₁₂".
    - iRight. iSplit; first done. by iApply "Hκ₁₂". 
  Qed.

  Lemma ty_le_option (τ₁ τ₂ : sem_ty Σ) :
    τ₁ ≤T τ₂ -∗
    (Option τ₁) ≤T (Option τ₂).
  Proof. iIntros "#?". iApply ty_le_sum; last done. iIntros "!# % $". Qed.

  Lemma ty_le_forall (τ₁ τ₂ : sem_ty Σ → sem_ty Σ) :
    (∀ α, τ₁ α ≤T τ₂ α) -∗
    (∀T: α, τ₁ α)%T ≤T (∀T: α, τ₂ α).
  Proof.
    iIntros "#Hτ₁₂ !# %v #Hτ₁ %τ !#". unfold sem_ty_forall.
    iApply (ewp_pers_mono with "[Hτ₁]"); [iApply "Hτ₁"|].
    iIntros "!# % Hτ !>". by iApply "Hτ₁₂".
  Qed.

  Lemma ty_le_sig_forall (τ₁ τ₂ : sem_sig Σ → sem_ty Σ) :
    (∀ θ, τ₁ θ ≤T τ₂ θ) -∗
    (∀S: θ, τ₁ θ) ≤T (∀S: θ, τ₂ θ).
  Proof.
    iIntros "#Hτ₁₂ !# %v #Hτ₁ %σ !#".
    iApply (ewp_pers_mono with "[Hτ₁]"); [iApply "Hτ₁"|].
    iIntros "!# % Hτ₁σ !>".
    iApply ("Hτ₁₂" $! σ with "Hτ₁σ").
  Qed.

  Lemma ty_le_exists (τ₁ τ₂ : sem_ty Σ → sem_ty Σ) :
    (∀ α, τ₁ α ≤T τ₂ α) -∗
    (∃: α, τ₁ α) ≤T (∃: α, τ₂ α).
  Proof.
    iIntros "#Hτ₁₂ !# %v (%α & Hα) //=".
    iExists α. by iApply "Hτ₁₂".
  Qed.

  Lemma ty_le_rec (τ₁ τ₂ : sem_ty Σ -> sem_ty Σ) `{NonExpansive τ₁, NonExpansive τ₂} :
    □ (∀ α α', (α ≤T α') -∗ τ₁ α ≤T τ₂ α') -∗
    (μT: α, τ₁ α) ≤T (μT: α, τ₂ α).
  Proof.
    iIntros "#Hτ₁₂ !#". iLöb as "IH". iIntros "%v Hτ₁".
    iApply sem_ty_rec_unfold.
    rewrite sem_ty_rec_unfold. iNext.
    iApply ("Hτ₁₂" with "[] Hτ₁").
    rewrite /ty_le /tc_opaque. iApply "IH".
  Qed.

  Lemma ty_le_list (τ₁ τ₂ : sem_ty Σ) :
    τ₁ ≤T τ₂ -∗
    List τ₁ ≤T List τ₂.
  Proof.
    iIntros "#Hτ₁₂ !# %v HLτ₁". unfold sem_ty_list.
    iLöb as "IH" forall (v).
    iApply sem_ty_rec_unfold.
    rewrite sem_ty_rec_unfold. iNext.
    iDestruct "HLτ₁" as "(%v' & [(-> & Hunit)|(-> & (%w₁ & %w₂ & -> & Hτ₁ & Hμ))])".
    { iExists v'; iLeft. by iFrame. }
    iExists (w₁, w₂)%V. iRight. iSplit; first done.
    iExists w₁, w₂; iSplit; first done.
    iSplitL "Hτ₁"; [by iApply "Hτ₁₂"|by iApply "IH"].
  Qed.
  
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

End sub_typing.

Section copyable_types.
  
  Context `{!heapGS Σ}.

  (* Copyable types *)
  
  Open Scope sem_ty_scope.

  Lemma copy_ty_void : ⊢ copy_ty Void.
  Proof. iIntros "!# %v $!". Qed.

  Lemma copy_ty_unit : ⊢ copy_ty ().
  Proof. iIntros "!# %v $!". Qed.
  
  Lemma copy_ty_bool : ⊢ copy_ty 𝔹.
  Proof. iIntros "!# %v #$". Qed.
  
  Lemma copy_ty_nat : ⊢ copy_ty ℤ.
  Proof. iIntros "!# %v #$". Qed.
  
  Lemma copy_ty_moved : ⊢ copy_ty Moved.
  Proof. iIntros "!# %v #$". Qed.

  Lemma copy_ty_cpy τ : ⊢ copy_ty ('! τ).
  Proof. iIntros "!# %v #$". Qed.

  Lemma copy_ty_uarr τ σ κ : ⊢ copy_ty (τ -{ σ }-> κ).
  Proof. iIntros "!# %v #$". Qed.
  
  Lemma copy_ty_prod τ κ : copy_ty τ -∗ copy_ty κ -∗ copy_ty (τ × κ).
  Proof. 
    iIntros "#Hcpyτ #Hcpyκ !# %v (% & % & -> & Hτ & Hκ)". 
    iDestruct ("Hcpyτ" with "Hτ") as "#Hτ'".
    iDestruct ("Hcpyκ" with "Hκ") as "#Hκ'". 
    iIntros "!#". iExists v₁, v₂. by iFrame "#".
  Qed.

  Lemma copy_ty_sum τ κ : copy_ty τ -∗ copy_ty κ -∗ copy_ty (τ + κ).
  Proof.
    iIntros "#Hcpyτ #Hcpyκ !# %v (% & [(-> & Hτ)|(-> & Hκ)])". 
    - iDestruct ("Hcpyτ" with "Hτ") as "#Hτ'". iIntros "!#". 
      iExists v'. iLeft. by iFrame "#".
    - iDestruct ("Hcpyκ" with "Hκ") as "#Hκ'". iIntros "!#". 
      iExists v'. iRight. by iFrame "#".
  Qed.

  Lemma copy_ty_forallT C : ⊢ copy_ty (∀T: α, C α).
  Proof. iIntros "!# % #$". Qed.

  Lemma copy_ty_forallS C : ⊢ copy_ty (∀S: θ, C θ).
  Proof. iIntros "!# % #$". Qed.

  Lemma copy_ty_ref τ : ⊢ copy_ty (Refᶜ τ).
  Proof. iIntros "!# % #$". Qed.

  Lemma copy_ty_exists τ : (∀ α, copy_ty (τ α)) -∗ copy_ty (∃: α, τ α).
  Proof. 
    iIntros "#H !# % [%α Hτ']". 
    iDestruct ("H" with "Hτ'") as "#Hτ".
    iIntros "!#". by iExists α.
  Qed.

  Lemma copy_ty_rec τ `{NonExpansive τ}: 
    □ (∀ α, (copy_ty α) -∗ copy_ty (τ α)) -∗ 
    copy_ty (μT: α, τ α).
  Proof. 
    iIntros "#H !# %". iLöb as "IH" forall (v). 
    rewrite {1 2} sem_ty_rec_unfold.
    iIntros "Hτ". iApply bi.later_intuitionistically.
    iNext. iApply ("H" with "[] Hτ"). 
    rewrite /copy_ty /tc_opaque. iApply "IH".
  Qed.

  Lemma copy_ty_option τ : copy_ty τ -∗ copy_ty (Option τ).
  Proof. 
    iIntros "#H". 
    iApply copy_ty_sum; [iApply copy_ty_unit|done]. 
  Qed.

  Lemma copy_ty_list τ : copy_ty τ -∗ copy_ty (List τ).
  Proof.
    iIntros "#Hτ". iApply copy_ty_rec.
    iIntros "!# % #Hα". 
    iApply copy_ty_sum; [iApply copy_ty_unit|].
    by iApply copy_ty_prod.
  Qed.

  Lemma copy_env_nil : ⊢ copy_env [].
  Proof. iIntros "!# % #$". Qed.
  
  Lemma copy_env_cons Γ x τ : 
    copy_env Γ -∗
    copy_ty τ -∗
    copy_env ((x, τ) :: Γ).
  Proof. 
    iIntros "#HΓcpy #Hτcpy !# % (% & %Hrw & Hτ & HΓ)".
    iDestruct ("Hτcpy" with "Hτ") as "#Hτ'".
    iDestruct ("HΓcpy" with "HΓ") as "#HΓ'".
    iIntros "!#". iExists v. by iFrame "#".
  Qed.

End copyable_types.
