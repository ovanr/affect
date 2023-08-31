
(* sem_sub_typing.v *)

(* This file contains the definition sub-typing relations and 
   Copyable (persistent) types
*)


From iris.proofmode Require Import base tactics.
From iris.base_logic.lib Require Import iprop invariants.

(* Hazel Reasoning *)
From program_logic Require Import weakest_precondition 
                                  tactics 
                                  state_reasoning.

(* Local imports *)
From affine_tes.logic Require Import sem_types.
From affine_tes.logic Require Import sem_typed.


(* Copyable types *)
Definition copy_ty `{!heapGS Σ} (τ : sem_ty Σ) := 
  ∀ v, Persistent (τ%T v).

(* Copyable environment *)
Definition copy_env `{!heapGS Σ} Γ :=
  ∀ vs, Persistent (env_sem_typed Γ vs).

(* Sub-typing and relations *)

Definition ty_le {Σ} (A B : sem_ty Σ) := ∀ v, A v ⊢ B v.
Definition sig_le {Σ} (ρ ρ' : sem_sig Σ) := ⊢ iEff_le ρ ρ'.
Definition env_le `{!heapGS Σ} Γ₁ Γ₂ :=
  ∀ vs, env_sem_typed Γ₁ vs ⊢ env_sem_typed Γ₂ vs.

Notation "Γ₁ '≤E' Γ₂" := (env_le Γ₁ Γ₂) (at level 98).
Notation "τ '≤T' κ" := (ty_le τ%T κ%T) (at level 98).

Notation "ρ '≤R' ρ'" := (sig_le ρ%R ρ'%R) (at level 98).

Section sub_typing.

  Context `{!heapGS Σ}.

  Lemma sig_le_refl (ρ : sem_sig Σ) : ρ ≤R ρ.
  Proof. iApply iEff_le_refl. Qed.
  
  Lemma sig_le_trans (ρ₁ ρ₂ ρ₃: sem_sig Σ) : 
      ρ₁ ≤R ρ₂ →
      ρ₂ ≤R ρ₃ →
      ρ₁ ≤R ρ₃. 
  Proof. 
    intros Hρ₁₂ Hρ₂₃. 
    iApply iEff_le_trans; [iApply Hρ₁₂|iApply Hρ₂₃]. 
  Qed.
  
  Lemma sig_le_nil (ρ : sem_sig Σ) :
    ⟨⟩ ≤R ρ.
  Proof. iApply iEff_le_bottom. Qed.
  
  Lemma sig_le_eff (ι₁ ι₂ κ₁ κ₂ : sem_ty Σ) :
    ι₁ ≤T ι₂ →
    κ₂ ≤T κ₁ →
    ((ι₁ ⇒ κ₁) ≤R (ι₂ ⇒ κ₂)).
  Proof.
    iIntros (Hι₁₂ Hκ₂₁ v) "%Φ !#".
    rewrite !sem_sig_eff_eq.
    iIntros "(%a & -> & Hι₁ & HκΦ₁)".
    iExists v. iSplit; first done. iSplitL "Hι₁".
    { by iApply Hι₁₂. }
    iIntros (b) "Hκ₂". iApply "HκΦ₁".
    by iApply Hκ₂₁.
  Qed.
  
  Lemma ty_le_refl (τ : sem_ty Σ) : τ ≤T τ.
  Proof. done. Qed.
  
  Lemma ty_le_trans (τ₁ τ₂ τ₃ : sem_ty Σ) :
    τ₁ ≤T τ₂ →
    τ₂ ≤T τ₃ →
    τ₁ ≤T τ₃.
  Proof. 
    iIntros (Hτ₁₂ Hτ₂₃ v) "Hτ₁". 
    iApply Hτ₂₃. by iApply Hτ₁₂.
  Qed.
  
  Lemma ty_le_u2aarr (τ κ : sem_ty Σ) (ρ : sem_sig Σ) :
    (τ -{ ρ }-> κ) ≤T (τ -{ ρ }-∘ κ).
  Proof.
    iIntros (v) "#Hτκ %w Hw".
    iApply ("Hτκ" with "Hw").
  Qed.

  Lemma ty_le_u2suarr (τ κ : sem_ty Σ) (ρ : sem_sig Σ) :
    (τ -{ ρ }-> κ) ≤T (τ ∘-{ ρ }-> κ).
  Proof.
    iIntros (v) "#Hτκ".
    iLöb as "IH".
    rewrite {2}sem_ty_equiv; [|apply sem_ty_suarr_unfold].
    iIntros (w) "Hτ".
  Admitted.


  Lemma ty_le_suarr2arr (τ κ : sem_ty Σ) (ρ : sem_sig Σ) :
    (τ ∘-{ ρ }-> κ) ≤T (τ -{ ρ }-∘ κ).
  Proof.
    iIntros (v) "Hτκ %w Hτ".
    rewrite sem_ty_equiv; [|apply sem_ty_suarr_unfold].
    iApply (ewp_mono with "[Hτκ Hτ]").
    { by iApply "Hτκ". }
    iIntros "%u /= [Hκ _] !> {$Hκ}".
  Qed.
  
  Lemma ty_le_aarr (τ₁ κ₁ τ₂ κ₂ : sem_ty Σ) (ρ ρ' : sem_sig Σ) :
    ρ ≤R ρ' →
    τ₂ ≤T τ₁ →
    κ₁ ≤T κ₂ →
    (τ₁ -{ ρ }-∘ κ₁) ≤T (τ₂ -{ ρ' }-∘ κ₂).
  Proof.
    iIntros (Hρ Hτ₂₁ Hκ₁₂ v) "Hτκ₁ %w Hw".
    iApply ewp_os_prot_mono.
    { iApply Hρ. }
    iApply (ewp_mono with "[Hτκ₁ Hw]").
    { iApply ("Hτκ₁" with "[Hw]"); by iApply Hτ₂₁. }
    iIntros (u) "Hu !>". by iApply Hκ₁₂.
  Qed.
  
  Lemma ty_le_uarr (τ₁ κ₁ τ₂ κ₂ : sem_ty Σ) (ρ ρ' : sem_sig Σ) :
    ρ ≤R ρ' →
    τ₂ ≤T τ₁ →
    κ₁ ≤T κ₂ →
    (τ₁ -{ ρ }-> κ₁) ≤T (τ₂ -{ ρ' }-> κ₂).
  Proof.
    iIntros (Hρ Hτ₂₁ Hκ₁₂ v) "#Hτκ₁ %w !# Hw".
    iApply ewp_os_prot_mono.
    { iApply Hρ. }
    iApply (ewp_mono with "[Hw]").
    { iApply ("Hτκ₁" with "[Hw]"); by iApply Hτ₂₁. }
    iIntros (u) "Hu". by iApply Hκ₁₂. 
  Qed.
  
  Lemma ty_le_suarr (τ₁ κ₁ τ₂ κ₂ : sem_ty Σ) (ρ ρ' : sem_sig Σ) :
    ρ ≤R ρ' →
    τ₂ ≤T τ₁ →
    κ₁ ≤T κ₂ →
    (τ₁ ∘-{ ρ }-> κ₁) ≤T (τ₂ ∘-{ ρ' }-> κ₂).
  Proof.
    iIntros (Hρ Hτ₂₁ Hκ₁₂ v) "Hτκ₁". 
    iLöb as "IH".
    rewrite sem_ty_equiv; [iApply sem_ty_suarr_unfold|apply sem_ty_suarr_unfold].
    simpl. iIntros (w) "Hτ₂". 
    iApply (ewp_mono with "[Hτκ₁ Hτ₂]").
    { iApply ewp_os_prot_mono. iApply Hρ. iApply "Hτκ₁". by iApply Hτ₂₁. }
    iIntros (u) "[Hκ₁ Hτκ₁] !>". iSplitL "Hκ₁".
    { by iApply Hκ₁₂. }
  Admitted.

  Lemma ty_le_ref (τ₁ τ₂ : sem_ty Σ) :
    τ₁ ≤T τ₂ →
    (Ref τ₁) ≤T (Ref τ₂).
  Proof.
    iIntros (Hτ₁₂ v) "(%l & -> & (%w & Hl & Hτw))".
    iExists l. iSplit; first done.
    iExists w. iFrame. by iApply Hτ₁₂.
  Qed.

  Lemma ty_le_prod (τ₁ τ₂ κ₁ κ₂ : sem_ty Σ) :
    τ₁ ≤T τ₂ →
    κ₁ ≤T κ₂ →
    (τ₁ × κ₁) ≤T (τ₂ × κ₂).
  Proof.
    iIntros (Hτ₁₂ Hκ₁₂ v) "(%w₁ & %w₂ & -> &Hw₁ & Hw₂)".
    iExists w₁, w₂. iSplit; first done. iSplitL "Hw₁".
    { by iApply Hτ₁₂. }
    by iApply Hκ₁₂.
  Qed.
  
  Lemma ty_le_sum (τ₁ τ₂ κ₁ κ₂ : sem_ty Σ) :
    τ₁ ≤T τ₂ →
    κ₁ ≤T κ₂ →
    (τ₁ + κ₁) ≤T (τ₂ + κ₂).
  Proof.
    iIntros (Hτ₁₂ Hκ₁₂ v) "(%v' & [(-> & Hτ₁)|(-> & Hκ₁)])"; iExists v'. 
    - iLeft. iSplit; first done. by iApply Hτ₁₂.
    - iRight. iSplit; first done. by iApply Hκ₁₂. 
  Qed.

  Lemma ty_le_option (τ₁ τ₂ : sem_ty Σ) :
    τ₁ ≤T τ₂ →
    (Option τ₁) ≤T (Option τ₂).
  Proof. intros ?. by apply ty_le_sum. Qed.

  Lemma ty_le_forall ρ₁ ρ₂ (τ₁ τ₂ : sem_ty Σ → sem_sig Σ → sem_ty Σ) :
    ρ₁ ≤R ρ₂ →
    (∀ α, τ₁ α ρ₁ ≤T τ₂ α ρ₂) →
    (∀T: α, { ρ₁ }, τ₁ α ρ₁) ≤T (∀T: α, { ρ₂ }, τ₂ α ρ₂).
  Proof.
    iIntros (Hρ₁₂ Hτ₁₂ v) "Hτ₁ %τ". unfold sem_ty_forall.
    iApply ewp_os_prot_mono; [iApply Hρ₁₂|].
    iApply (ewp_mono with "[Hτ₁]").
    { iApply "Hτ₁". }
    iIntros (w) "Hw !>". by iApply Hτ₁₂.
  Qed.

  Lemma ty_le_sig_forall (τ₁ τ₂ : sem_sig Σ → sem_ty Σ) :
    (∀ θ, τ₁ θ ≤T τ₂ θ) →
    (∀S: θ, τ₁ θ) ≤T (∀S: θ, τ₂ θ).
  Proof.
    iIntros (Hτ₁₂ v) "Hτ₁ %ρ".
    iApply (ewp_mono with "[Hτ₁]"); [iApply "Hτ₁"|].
    iIntros (u) "Hτ₁ !>".
    iApply (Hτ₁₂ ρ with "Hτ₁").
  Qed.

  Lemma ty_le_exists (τ₁ τ₂ : sem_ty Σ → sem_ty Σ) :
    (∀ α, τ₁ α ≤T τ₂ α) →
    (∃: α, τ₁ α) ≤T (∃: α, τ₂ α).
  Proof.
    iIntros (Hτ₁₂ v) "(%α & Hα) //=".
    iExists α. by iApply Hτ₁₂.
  Qed.

  Lemma ty_le_list (τ₁ τ₂ : sem_ty Σ) :
    τ₁ ≤T τ₂ →
    List τ₁ ≤T List τ₂.
  Proof.
    iIntros (Hτ₁₂ v) "HLτ₁". unfold sem_ty_list.
    iLöb as "IH" forall (v).
    iApply sem_ty_rec_unfold.
    rewrite sem_ty_rec_unfold. iNext.
    iDestruct "HLτ₁" as "(%v' & [(-> & Hunit)|(-> & (%w₁ & %w₂ & -> & Hτ₁ & Hμ))])".
    { iExists v'; iLeft. by iFrame. }
    iExists (w₁, w₂)%V. iRight. iSplit; first done.
    iExists w₁, w₂; iSplit; first done.
    iSplitL "Hτ₁"; [by iApply Hτ₁₂|by iApply "IH"].
  Qed.
  
  Lemma env_le_refl Γ : Γ ≤E Γ.
  Proof. done. Qed.
  
  Lemma env_le_trans Γ₁ Γ₂ Γ₃ : 
    Γ₁ ≤E Γ₂ →
    Γ₂ ≤E Γ₃ →
    Γ₁ ≤E Γ₃.
  Proof.
    iIntros (HΓ₁₂ HΓ₂₃ vs) "HΓ₁ //=".  
    iApply HΓ₂₃. by iApply HΓ₁₂.
  Qed.
  
  Lemma env_le_cons Γ₁ Γ₂ τ₁ τ₂ x :
    Γ₁ ≤E Γ₂ →
    τ₁ ≤T τ₂ →
    (x, τ₁) :: Γ₁ ≤E (x, τ₂) :: Γ₂.
  Proof.
    iIntros (HΓ₁₂ Hτ₁₂ vs) "//= ((%v & Hlookup & Hv) & HΓ₁)".
    iSplitR "HΓ₁"; last (by iApply HΓ₁₂).
    iExists v. iFrame. by iApply Hτ₁₂.
  Qed.
  
  Lemma env_le_copy_contraction Γ x τ :
    copy_ty τ →
    (x, τ) :: Γ ≤E (x, τ) :: (x, τ) :: Γ.
  Proof.
    iIntros (Hcpyτ vs) "//= [(%w & -> & Hτ) $]". 
    rewrite Hcpyτ. iDestruct "Hτ" as "#Hτ".
    iSplitL; iExists w; by iSplit.
  Qed.
  
  Lemma env_le_bring_forth Γ n x τ :
    nth_error Γ n = Some (x, τ) →
    Γ ≤E (x, τ) :: (list_delete n Γ) .
  Proof.
    iInduction n as [|] "IH" forall (Γ); iIntros (Hnth vs).
    { iIntros "HΓ". simpl in Hnth. destruct Γ; first done. simplify_eq. iFrame. }
    iIntros "/= HΓ". simpl in Hnth. destruct Γ; first done; simpl. destruct p.
    iDestruct "HΓ" as "[Hp HΓ]". iFrame. iApply "IH".
    { by iPureIntro. }
    iFrame.
  Qed.

  Lemma env_le_bring_forth_rev Γ n x τ :
    nth_error Γ n = Some (x, τ) →
    (x, τ) :: (list_delete n Γ) ≤E Γ.
  Proof.
    iInduction n as [|] "IH" forall (Γ); iIntros (Hnth vs).
    { iIntros "[Hτ HΓ']". simpl in Hnth. destruct Γ; first done. simplify_eq. iFrame. }
    iIntros "/= [Hτ HΓ]". simpl in Hnth. destruct Γ; first done; simpl. destruct p.
    iDestruct "HΓ" as "[Hp HΓ]". iFrame. iApply "IH".
    { by iPureIntro. }
    iFrame.
  Qed.

  Lemma env_le_swap_second Γ x y τ₁ τ₂ : 
    (y, τ₂) :: (x, τ₁) :: Γ ≤E (x, τ₁) :: (y, τ₂) :: Γ.
  Proof.
    pose proof (env_le_bring_forth_rev ((x, τ₁) :: (y, τ₂) :: Γ) 1 y τ₂).
    by apply H.
  Qed.

  Lemma env_le_swap_third Γ x y z τ₁ τ₂ τ₃: 
    (z, τ₃) :: (x, τ₁) :: (y, τ₂) :: Γ ≤E (x, τ₁) :: (y, τ₂) :: (z, τ₃) :: Γ.
  Proof.
    pose proof (env_le_bring_forth_rev ((x, τ₁) :: (y, τ₂) :: (z, τ₃) :: Γ) 2 z τ₃).
    by apply H.
  Qed.

  Lemma env_le_weaken Γ x τ :
    (x, τ) :: Γ ≤E Γ.
  Proof. iIntros (vs) "(_ & $) /=". Qed.

End sub_typing.

Ltac solve_copy :=
  repeat (intros ? ||
          apply bi.emp_persistent ||
          apply bi.sep_persistent ||
          apply bi.and_persistent ||
          apply bi.or_persistent ||
          apply bi.forall_persistent ||
          apply bi.exist_persistent ||
          apply bi.pure_persistent ||
          apply plainly_persistent ||
          apply bi.later_persistent ||
          apply bi.persistently_persistent ||
          apply bi.intuitionistically_persistent ||
          apply inv_persistent).

Section copyable_types.
  
  Context `{!heapGS Σ}.

  (* Copyable types *)
  
  Open Scope sem_ty_scope.

  Lemma copy_ty_unit : copy_ty ().
  Proof. solve_copy. Qed.
  
  Lemma copy_ty_bool : copy_ty 𝔹.
  Proof. solve_copy. Qed.
  
  Lemma copy_ty_nat : copy_ty ℤ.
  Proof. solve_copy. Qed.
  
  Lemma copy_ty_moved : copy_ty Moved.
  Proof. solve_copy. Qed.

  Lemma copy_ty_uarr τ ρ κ : copy_ty (τ -{ ρ }-> κ).
  Proof. solve_copy. Qed.
  
  Lemma copy_ty_prod τ κ : copy_ty τ → copy_ty κ → copy_ty (τ × κ).
  Proof. by solve_copy. Qed.
  
  Lemma copy_ty_sum τ κ : copy_ty τ → copy_ty κ → copy_ty (τ + κ).
  Proof. by solve_copy. Qed.

  Lemma copy_ty_option τ : copy_ty τ → copy_ty (Option τ).
  Proof. by solve_copy. Qed.

  Lemma copy_ty_exists τ : (∀ α, copy_ty (τ α)) → copy_ty (∃: α, τ α).
  Proof. solve_copy. apply H. Qed.

  Lemma copy_ty_rec τ `{NonExpansive τ}: 
    (∀ α, copy_ty (τ α)) → copy_ty (μ: α, τ α).
  Proof. iIntros (H v). rewrite sem_ty_rec_unfold.
         solve_copy. apply H. 
  Qed.

  Lemma copy_ty_list τ : copy_ty τ → copy_ty (List τ).
  Proof.
    iIntros (Hcpyτ). unfold sem_ty_list. unfold copy_ty.
    iIntros (v). unfold Persistent. iIntros "Hμ".
    iLöb as "IH" forall (v).
    rewrite sem_ty_rec_unfold. rewrite -bi.later_persistently_1.
    iNext. unfold ListF.
    rewrite bi.persistently_exist. 
    iDestruct "Hμ" as "(%w & [(-> & #Hunit)|(-> & (%w₁ & %w₂ & -> & Hτ & Hμ))])".
    { iExists w; rewrite bi.persistently_or;
      iLeft. iIntros "!# {$Hunit} //=". }
    iExists (w₁, w₂)%V. rewrite bi.persistently_or.
    iRight. unfold copy_ty in Hcpyτ. rewrite Hcpyτ.
    iDestruct "Hτ" as "#Hτ".
    iDestruct ("IH" with "Hμ") as "#Hμ₂".
    iIntros "!#". iSplit; first done.
    iExists w₁, w₂; iSplit; first done. by iSplit.
  Qed.

  Lemma copy_env_nil : copy_env [].
  Proof. solve_copy. Qed.
  
  Lemma copy_env_cons Γ x τ : 
    copy_env Γ →
    copy_ty τ →
    copy_env ((x, τ) :: Γ).
  Proof. by solve_copy. Qed.

  Lemma copy_pers τ :
    ⌜ copy_ty τ ⌝ -∗ □ (∀ v, τ v -∗ □ (τ v)).
  Proof.
    iIntros "%Hcpy !# %v Hτ".
    unfold copy_ty, Persistent in Hcpy. 
    by iDestruct (Hcpy v with "Hτ") as "#Hτv".
  Qed.

End copyable_types.
