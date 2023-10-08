
(* sem_sub_typing.v *)

(* This file contains the definition sub-typing relations and 
   Copyable (persistent) types
*)


From iris.algebra Require Import ofe.
From iris.proofmode Require Import base tactics classes.
From iris.base_logic.lib Require Import iprop invariants.

(* Hazel Reasoning *)
From program_logic Require Import weakest_precondition 
                                  tactics 
                                  state_reasoning.

(* Local imports *)
From affine_tes.lang Require Import hazel.
From affine_tes.lang Require Import subst_map.
From affine_tes.logic Require Import sem_def.
From affine_tes.logic Require Import tactics.
From affine_tes.logic Require Import sem_types.
From affine_tes.logic Require Import sem_env.


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
  
  Lemma sig_le_eff_non_rec (ι₁ ι₂ κ₁ κ₂ : sem_ty Σ -n> sem_ty Σ) :
    (∀ α, ι₁ α ≤T ι₂ α) →
    (∀ α, κ₂ α ≤T κ₁ α) →
    (∀μTS: _ , α , ι₁ α ⇒ κ₁ α) ≤R (∀μTS: _ , α , ι₂ α ⇒ κ₂ α).
  Proof.
    iIntros (Hι₁₂ Hκ₂₁ v Φ) "!#".
    iPoseProof (sem_sig_eff_rec_eq (λ α _, ι₂ α) (λ α _, κ₂ α) v Φ) as "[_ Hrw]".
    iIntros "Hμ₁". iApply "Hrw".
    iPoseProof (sem_sig_eff_rec_eq (λ α _, ι₁ α) (λ α _, κ₁ α) v Φ) as "[Hrw' _]".
    iDestruct ("Hrw'" with "Hμ₁") as "(%α & %w & -> & Hι₁ & HκΦ₁)".
    iExists α, v; iSplitR; first done.
    iSplitL "Hι₁".
    { iNext. by iApply Hι₁₂. }
    iIntros (b) "Hκ₂". iApply "HκΦ₁".
    iNext. by iApply Hκ₂₁.
  Qed.

  (* Lemma sig_le_eff_rec (ι₁ ι₂ κ₁ κ₂ : sem_sig Σ -d> sem_ty Σ) *) 
  (*   `{ NonExpansive ι₁, NonExpansive ι₂, NonExpansive κ₁, NonExpansive κ₂ } : *)
  (*   (∀ ρ ρ', ρ ≤R ρ' → ι₁ ρ ≤T ι₂ ρ') → *)
  (*   (∀ ρ ρ', ρ ≤R ρ' → κ₂ ρ' ≤T κ₁ ρ) → *)
  (*   (μS: α, ι₁ α ⇒ κ₁ α) ≤R (μS: α, ι₂ α ⇒ κ₂ α). *)
  (* Proof. *)
  (*   iIntros (Hι₁₂ Hκ₂₁). iLöb as "IH". *)
  (*   iIntros (v Φ) "!#". *) 
  (*   rewrite !sem_sig_eff_rec_eq. *)
  (*   iIntros "(%w & -> & Hι₁ & HκΦ₁)". *)
  (*   iExists v; iSplitR; first done. *)
  (*   iSplitL "Hι₁". *)
  (*   { iNext. admit. iApply Hι₁₂. } *)
  (*   iIntros (b) "Hκ₂". iApply "HκΦ₁". *)
  (*   iNext. by iApply Hκ₂₁. *)
  (* Qed. *)

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
  
  Lemma ty_le_cpy (τ : sem_ty Σ) :
    copy_ty τ →
    τ ≤T '! τ.
  Proof. iIntros (? v). rewrite H. iIntros "#$". Qed.

  Lemma ty_le_cpy_inv (τ : sem_ty Σ) :
    ('! τ) ≤T τ.
  Proof. iIntros (v) "#$". Qed.

  Lemma ty_le_u2suarr (τ κ : sem_ty Σ) (ρ : sem_sig Σ) (Γ₁ Γ₂ : env Σ) :
    (τ -{ ρ ; Γ₁ ; Γ₂ }-> κ) ≤T (τ >-{ ρ ; Γ₁ ; Γ₂ }-∘ κ).
  Proof.
    iIntros (v) "#Hτκ".
    iLöb as "IH".
    rewrite {2}sem_ty_suarr_unfold.
    iIntros (w vs) "HΓ₁ Hτ /=".
    iApply (ewp_mono _ _ (λ v0, (κ v0 ∗ ⟦ Γ₂ ⟧ vs) ∗ (τ >-{ ρ; Γ₁; Γ₂ }-∘ κ)%T v)%I  with "[HΓ₁ Hτ]");
      last (iIntros (?) "[[$ $] $] !> //").
    iApply (ewp_frame_later_r with "[Hτ HΓ₁ Hτκ]").
    { iApply ("Hτκ" with "HΓ₁ Hτ"). }
    iIntros "!> {$IH}". 
  Qed.

  Lemma ty_le_su2aarr (τ κ : sem_ty Σ) (ρ : sem_sig Σ) (Γ₁ Γ₂ : env Σ) :
    (τ >-{ ρ; Γ₁; Γ₂ }-∘ κ) ≤T (τ -{ ρ; Γ₁; Γ₂ }-∘ κ).
  Proof.
    iIntros "%v Hτκ %w %vs HΓ₁ Hτ". 
    rewrite sem_ty_suarr_unfold.
    iApply (ewp_mono with "[Hτκ HΓ₁ Hτ]").
    { iApply ("Hτκ" $! w vs with "HΓ₁ Hτ"). }
    iIntros "%u /= [$ [$ _]] !> //".
  Qed.
  
  Lemma ty_le_u2aarr (τ κ : sem_ty Σ) (ρ : sem_sig Σ) (Γ₁ Γ₂ : env Σ) :
    (τ -{ ρ ; Γ₁; Γ₂ }-> κ) ≤T (τ -{ ρ ; Γ₁; Γ₂ }-∘ κ).
  Proof.
    eapply ty_le_trans; [apply ty_le_u2suarr|apply ty_le_su2aarr].
  Qed.

  Lemma ty_le_aarr (τ₁ κ₁ τ₂ κ₂ : sem_ty Σ) (ρ ρ' : sem_sig Σ) (Γ₁ Γ₂ Γ₁' Γ₂' : env Σ) :
    ρ ≤R ρ' →
    τ₂ ≤T τ₁ →
    κ₁ ≤T κ₂ →
    Γ₁' ≤E Γ₁ →
    Γ₂ ≤E Γ₂' →
    env_dom Γ₁ = env_dom Γ₁' →
    (τ₁ -{ ρ ; Γ₁ ; Γ₂ }-∘ κ₁) ≤T (τ₂ -{ ρ' ; Γ₁' ; Γ₂' }-∘ κ₂).
  Proof.
    iIntros (Hρ Hτ₂₁ Hκ₁₂ HΓ₁'Γ₁ HΓ₂Γ₂' Heq v) "Hτκ₁ %w %vs HΓ₁' Hτ".
    iApply ewp_os_prot_mono; [iApply Hρ|].
    rewrite -Heq HΓ₁'Γ₁ Hτ₂₁.
    iApply (ewp_mono with "[Hτκ₁ Hτ HΓ₁']").
    { iApply ("Hτκ₁" $! w vs with "HΓ₁' Hτ"). }
    iIntros (u) "Hu !>". by rewrite Hκ₁₂ HΓ₂Γ₂'.
  Qed.
  
  Lemma ty_le_uarr (τ₁ κ₁ τ₂ κ₂ : sem_ty Σ) (ρ ρ' : sem_sig Σ) (Γ₁ Γ₂ Γ₁' Γ₂' : env Σ) :
    ρ ≤R ρ' →
    τ₂ ≤T τ₁ →
    κ₁ ≤T κ₂ →
    Γ₁' ≤E Γ₁ → 
    Γ₂ ≤E Γ₂' →
    env_dom Γ₁ = env_dom Γ₁' →
    (τ₁ -{ ρ ; Γ₁ ; Γ₂ }-> κ₁) ≤T (τ₂ -{ ρ' ; Γ₁' ; Γ₂' }-> κ₂).
  Proof.
    iIntros (Hρ Hτ₂₁ Hκ₁₂ HΓ₁'Γ₁ HΓ₂Γ₂' Heq v) "#Hτκ₁ %w !# %ws HΓ₁' Hτ₂".
    iApply ewp_os_prot_mono; [iApply Hρ|].
    rewrite -!Heq !HΓ₁'Γ₁ Hτ₂₁.
    iApply (ewp_mono with "[Hτκ₁ HΓ₁' Hτ₂]").
    { iApply ("Hτκ₁" with "HΓ₁' Hτ₂"). }
    iIntros (u) "[Hκ₁ HΓ₂] !>". rewrite HΓ₂Γ₂' -Hκ₁₂. iFrame.
  Qed.
  
  Lemma ty_le_suarr (τ₁ κ₁ τ₂ κ₂ : sem_ty Σ) (ρ ρ' : sem_sig Σ) (Γ₁ Γ₂ Γ₁' Γ₂' : env Σ) :
    ρ ≤R ρ' →
    τ₂ ≤T τ₁ →
    κ₁ ≤T κ₂ →
    Γ₁' ≤E Γ₁ → 
    Γ₂ ≤E Γ₂' →
    env_dom Γ₁ = env_dom Γ₁' →
    (τ₁ >-{ ρ ; Γ₁ ; Γ₂  }-∘ κ₁) ≤T (τ₂ >-{ ρ' ; Γ₁' ; Γ₂' }-∘ κ₂).
  Proof.
    iIntros (Hρ Hτ₂₁ Hκ₁₂ HΓ₁'Γ₁ HΓ₂Γ₂' ? v) "Hτκ₁". 
    iLöb as "IH".
    iApply sem_ty_suarr_unfold.
    simpl. iIntros (w vs) "HΓ₁' Hτ₂ /=". 
    iApply ewp_os_prot_mono; [iApply Hρ|]. 
    rewrite HΓ₁'Γ₁ Hτ₂₁. rewrite -H.
    iApply (ewp_mono with "[Hτκ₁ HΓ₁' Hτ₂]").
    - rewrite {2}sem_ty_suarr_unfold /=.
      iSpecialize ("Hτκ₁" $! w vs with "HΓ₁' Hτ₂").
      iApply (ewp_frame_later_r with "Hτκ₁ IH").
    - iIntros (u) "[(Hκ₁ & HΓ₂ & Hτκ₁) Hτκ₂] !>".
      rewrite Hκ₁₂ HΓ₂Γ₂'. iFrame. by iApply "Hτκ₂".
  Qed.

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
    (∀T: α, { ρ₁ }, τ₁ α ρ₁)%T ≤T (∀T: α, { ρ₂ }, τ₂ α ρ₂).
  Proof.
    iIntros (Hρ₁₂ Hτ₁₂ v) "#Hτ₁ %τ !#". unfold sem_ty_forall.
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
    iIntros (HΓ₁₂ Hτ₁₂ vs) "[%v (Hlookup & Hv & HΓ₁)]".
    iExists v. iFrame. iSplitR "HΓ₁"; last (by iApply HΓ₁₂).
    by iApply Hτ₁₂.
  Qed.
  
  Lemma env_le_copy_contraction Γ x τ :
    copy_ty τ →
    (x, τ) :: Γ ≤E (x, τ) :: (x, τ) :: Γ.
  Proof.
    move =>Hcpyτ vs.
    iIntros "//= [%w (%Hrw & Hτ & HΓ)]". 
    rewrite Hcpyτ. iDestruct "Hτ" as "#Hτ".
    by do 2 (iExists w; iFrame "%#").
  Qed.
  
  Lemma env_le_bring_forth Γ n x τ :
    nth_error Γ n = Some (x, τ) →
    Γ ≤E (x, τ) :: (list_delete n Γ) .
  Proof.
    iInduction n as [|] "IH" forall (Γ); iIntros (Hnth vs);
    iIntros "HΓ"; simpl in Hnth; destruct Γ; first done; simplify_eq; first done.
    destruct p; simpl. rewrite !env_sem_typed_cons.
    iDestruct "HΓ" as "[$ HΓ]". rewrite -env_sem_typed_cons.
    by iApply "IH". 
  Qed.

  Lemma env_le_bring_forth_rev Γ n x τ :
    nth_error Γ n = Some (x, τ) →
    (x, τ) :: (list_delete n Γ) ≤E Γ.
  Proof.
    iInduction n as [|] "IH" forall (Γ); iIntros (Hnth vs);
    simpl in Hnth; 
    destruct Γ as [|[y κ] Γ']; first done; 
    simplify_eq; simpl; first (iIntros "$").
    iIntros "[%v (? & ? & [%w (? & ? & ?)])]". 
    iExists w. iFrame. iApply "IH"; first done.
    iExists v. iFrame.
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

  Lemma env_le_swap_fourth Γ x y z z' τ₁ τ₂ τ₃ τ₄: 
    (z', τ₄) :: (x, τ₁) :: (y, τ₂) :: (z, τ₃) :: Γ ≤E (x, τ₁) :: (y, τ₂) :: (z, τ₃) :: (z', τ₄) :: Γ.
  Proof.
    pose proof (env_le_bring_forth_rev ((x, τ₁) :: (y, τ₂) :: (z, τ₃) :: (z', τ₄) :: Γ) 3 z' τ₄).
    by apply H.
  Qed.

  Lemma env_le_weaken Γ x τ :
    (x, τ) :: Γ ≤E Γ.
  Proof. iIntros (?) "[% (? & ? & $)]". Qed.

End sub_typing.

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

  Lemma copy_ty_cpy τ : copy_ty ('! τ).
  Proof. solve_copy. Qed.

  Lemma copy_ty_uarr τ ρ κ Γ₁ Γ₂ : copy_ty (τ -{ ρ ; Γ₁ ; Γ₂ }-> κ).
  Proof. solve_copy. Qed.
  
  Lemma copy_ty_prod τ κ : copy_ty τ → copy_ty κ → copy_ty (τ × κ).
  Proof. by solve_copy. Qed.
  
  Lemma copy_ty_sum τ κ : copy_ty τ → copy_ty κ → copy_ty (τ + κ).
  Proof. by solve_copy. Qed.

  Lemma copy_ty_forall C ρ : copy_ty (∀T: α, {ρ}, C α).
  Proof. by solve_copy. Qed.

  Lemma copy_ty_ref τ : copy_ty (Refᶜ τ).
  Proof. by solve_copy. Qed.

  Lemma copy_ty_option τ : copy_ty τ → copy_ty (Option τ).
  Proof. by solve_copy. Qed.

  Lemma copy_ty_exists τ : (∀ α, copy_ty (τ α)) → copy_ty (∃: α, τ α).
  Proof. solve_copy. apply H. Qed.

  Lemma copy_ty_rec τ `{NonExpansive τ}: 
    (∀ α, copy_ty (τ α)) → copy_ty (μT: α, τ α).
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
  Proof. 
    intros ???. rewrite env_sem_typed_cons.
    by solve_copy. Qed.

  Lemma copy_pers τ :
    ⌜ copy_ty τ ⌝ -∗ □ (∀ v, τ v -∗ □ (τ v)).
  Proof.
    iIntros "%Hcpy !# %v Hτ".
    unfold copy_ty, Persistent in Hcpy. 
    by iDestruct (Hcpy v with "Hτ") as "#Hτv".
  Qed.

End copyable_types.
