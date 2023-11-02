
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
From affine_tes.lang Require Import hazel.
From affine_tes.lang Require Import subst_map.
From affine_tes.logic Require Import sem_def.
From affine_tes.logic Require Import tactics.
From affine_tes.logic Require Import sem_types.
From affine_tes.logic Require Import sem_env.


Section sub_typing.

  Context `{!heapGS Σ}.

  Lemma sig_le_refl (ρ : sem_sig Σ) : ρ ≤R ρ.
  Proof. iIntros "%% !# $ !> //=". Qed.
  
  Lemma sig_le_trans (ρ₁ ρ₂ ρ₃: sem_sig Σ) : 
      ρ₁ ≤R ρ₂ →
      ρ₂ ≤R ρ₃ →
      ρ₁ ≤R ρ₃. 
  Proof. 
    intros Hρ₁₂ Hρ₂₃. 
    iIntros "%% !# Hρ₁".
    iDestruct Hρ₁₂ as "#Hρ₁₂".
    iSpecialize ("Hρ₁₂" $! v Φ with "Hρ₁").
    iMod "Hρ₁₂" as "Hρ₁₂". 
    iDestruct Hρ₂₃ as "#Hρ₂₃".
    iSpecialize ("Hρ₂₃" $! v Φ with "Hρ₁₂"). done.
  Qed.
  
  Lemma sigs_le_refl (ρs : sem_sigs Σ) :
    ρs ≤Rs ρs.
  Proof. destruct ρs. split; apply sig_le_refl. Qed.

  Lemma sigs_le_trans (ρs₁ ρs₂ ρs₃ : sem_sigs Σ) :
      ρs₁ ≤Rs ρs₂ →
      ρs₂ ≤Rs ρs₃ →
      ρs₁ ≤Rs ρs₃. 
  Proof. 
    intros Hρs₁₂ Hρs₂₃.
    destruct ρs₁, ρs₂, ρs₃, Hρs₁₂, Hρs₂₃. split; by eapply sig_le_trans.
  Qed.

  Lemma sig_eff_bot_iEff_bot `{!irisGS eff_lang Σ}:
    (μ∀TS: _ , _ , ⊥ ⇒ ⊥) ≤R iEff_bottom.
  Proof.
    iIntros "!# %v %Φ".
    rewrite sem_sig_eff_rec_eq.
    iIntros "H". iMod "H" as "(% & % & ? & HPre & HPost) /=".
    rewrite /sem_ty_void. iMod "HPre" as "HPre".
    iDestruct "HPre" as ">HPre". iIntros "!> //=".
  Qed.

  Lemma sig_le_nil (ρ : sem_sig Σ) :
    sem_sig_nil ≤R ρ.
  Proof. iIntros "%% !# H". iMod "H" as "[]". Qed.

  Lemma sigs_le_nil (ρs : sem_sigs Σ) :
    (⟨⟩ : sem_sigs Σ) ≤Rs ρs.
  Proof. split; apply sig_le_nil. Qed.
  
  Lemma sigs_le_comp (ρ₁ ρ₂ ρ₁' ρ₂' : sem_sig Σ) :
    ρ₁ ≤R ρ₁' →
    ρ₂ ≤R ρ₂' →
    ⟨ ρ₁, ρ₂ ⟩ ≤Rs ⟨ ρ₁', ρ₂' ⟩.
  Proof. intros ??. auto. Qed.

  Lemma sigs_le_os (ρ ρ' : sem_sig Σ) :
    ρ ≤R ρ' →
    (⟨ ρ , ⟩ : sem_sigs Σ) ≤Rs (⟨ ρ', ⟩ : sem_sigs Σ).
  Proof. intros ?. split; first auto. apply sig_le_nil. Qed.

  Lemma sigs_le_ms (ρ ρ' : sem_sig Σ) :
    ρ ≤R ρ' →
    (⟨ , ρ ⟩ : sem_sigs Σ) ≤Rs (⟨ , ρ' ⟩ : sem_sigs Σ).
  Proof. intros ?. split; last auto. apply sig_le_nil. Qed.

  Lemma sig_le_eff_non_rec (ι₁ ι₂ κ₁ κ₂ : sem_ty Σ -n> sem_ty Σ) :
    (∀ α, ι₁ α ≤T ι₂ α) →
    (∀ α, κ₂ α ≤T κ₁ α) →
    (μ∀TS: _ , α , ι₁ α ⇒ κ₁ α) ≤R (μ∀TS: _ , α , ι₂ α ⇒ κ₂ α).
  Proof.
    iIntros (Hι₁₂ Hκ₂₁ v Φ) "!#".
    iPoseProof (sem_sig_eff_rec_eq OS (λ α _, ι₂ α) (λ α _, κ₂ α) v Φ) as "[_ Hrw]".
    iIntros "Hμ₁". iApply "Hrw".
    iPoseProof (sem_sig_eff_rec_eq OS (λ α _, ι₁ α) (λ α _, κ₁ α) v Φ) as "[Hrw' _]".
    iMod "Hμ₁" as "Hμ₁".
    iDestruct ("Hrw'" with "Hμ₁") as "(%α & %w & <- & Hι₁ & HκΦ₁)".
    iExists α, w; iSplitR; first done.
    iSplitL "Hι₁".
    { iMod "Hι₁" as "Hι₁". iIntros "!>!>". by iApply Hι₁₂. }
    simpl. iIntros "!>". iIntros (b) "Hκ₂". iApply "HκΦ₁".
    iNext. by iApply Hκ₂₁.
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
  
  Lemma ty_le_bot (τ : sem_ty Σ) :
    ⊥ ≤T τ.
  Proof. iIntros (?) "[]". Qed.

  Lemma ty_le_cpy (τ : sem_ty Σ) :
    copy_ty τ →
    τ ≤T '! τ.
  Proof. iIntros (? v). rewrite H. iIntros "#$". Qed.

  Lemma ty_le_cpy_inv (τ : sem_ty Σ) :
    ('! τ) ≤T τ.
  Proof. iIntros (v) "#$". Qed.

  Lemma ty_le_u2aarr (τ κ : sem_ty Σ) (ρs : sem_sigs Σ) :
    (τ -{ ρs }-> κ) ≤T (τ -{ ρs }-∘ κ).
  Proof.
    iIntros (v) "#Hτκ". iIntros (w) "Hτ /=".
    iApply (ewp_pers_mono with "[Hτ Hτκ]"); [by iApply "Hτκ"|].
    iIntros "!# % $ //=".
  Qed.

  Lemma sig_le_upcl m ρ₁ ρ₂ : (ρ₁ ≤R ρ₂ → (upcl m ρ₁) ≤R (upcl m ρ₂))%ieff.
  Proof.
    iIntros (Hρ₁₂ v Φ) "!# H". iMod "H" as "[%Φ' [HΨ1 HΦ']]".
    iExists Φ'. iDestruct Hρ₁₂ as "#Hρ₁₂".
    iSpecialize ("Hρ₁₂" $! v Φ').
    iSplitL "HΨ1"; [by iApply "Hρ₁₂"|].
    by iApply (bi.intuitionistically_if_mono with "HΦ'").
  Qed.

  Lemma ewp_pers_smono_r ρs₁ ρs₂ Φ Φ' e :
      (ρs₁ ≤Rs ρs₂)%R →
      (|={⊤}=> EWP e <| ρs₁.1 |> {| ρs₁.2 |} {{ Φ }}) -∗
                   □ (∀ v, Φ v ={⊤}=∗ Φ' v) -∗
      |={⊤}=> EWP e <| ρs₂.1 |> {| ρs₂.2 |} {{ Φ' }}.
  Proof. 
      iIntros ([Hρ₁ Hρ₂]) "He #HΦ".
      iLöb as "IH" forall (e).
      destruct (to_val e) as [ v         |] eqn:?;
    [|destruct (to_eff e) as [((m, v), k)|] eqn:?].
    - rewrite !ewp_unfold /ewp_pre Heqo.
      iApply ("HΦ" with "[> -]"). iMod "He". done. 
    - rewrite -(of_to_eff _ _ _ _ Heqo0).
      destruct m; [rewrite -!ewp_eff_os_eq|rewrite -!ewp_eff_ms_eq]; 
      [iApply sig_le_upcl; first (apply Hρ₁)|iApply sig_le_upcl; first (apply Hρ₂)].
      { iApply (monotonic_prot with "[HΦ] He").
      [iApply (monotonic_prot with "[HΦ] He")| iApply (pers_monotonic_prot with "[] He"); iModIntro];
      iIntros (w) "Hk"; iNext. 
      { iApply 

      iApply ("IH" with "[Hk]").
    - rewrite !ewp_unfold /ewp_pre Heqo Heqo0.
      iIntros (σ₁ ns k ks nt) "Hσ".
      iMod (fupd_mask_subseteq E) as "Hclose"; first done.
      iMod ("He" with "[$]") as "[$ H]".
      iModIntro. iIntros (e₂ σ₂ Hstep) "Hcred".
      iMod ("H" with "[//] Hcred") as "H". iIntros "!> !>".
      iMod "H". iModIntro.
      iApply (step_fupdN_wand with "[H]"); first by iApply "H".
      iIntros ">($ & H)". iMod "Hclose" as "_". iModIntro.
      iApply ("IH" with "H").
  Qed.

  Lemma ty_le_aarr (τ₁ κ₁ τ₂ κ₂ : sem_ty Σ) (ρs ρs' : sem_sigs Σ) :
    ρs ≤Rs ρs' →
    τ₂ ≤T τ₁ →
    κ₁ ≤T κ₂ →
    (τ₁ -{ ρs }-∘ κ₁) ≤T (τ₂ -{ ρs' }-∘ κ₂).
  Proof.
    iIntros (Hρsle Hτ₂₁ Hκ₁₂ v) "Hτκ₁ %w Hτ".
    iApply fupd_ewp. 
    iApply (ewp_pers_smono_r with "[Hτκ₁ Hτ]"); [apply Hρsle| |iIntros "!# % H //= $H"].
    iApply (ewp_pers_mono with "[Hτκ₁ Hτ]").
    { iApply ("Hτκ₁" with "[Hτ]"); by rewrite Hτ₂₁. }
    iIntros "!# % Hκ !>". by rewrite Hκ₁₂.
  Qed.
  
  Lemma ty_le_uarr (τ₁ κ₁ τ₂ κ₂ : sem_ty Σ) (ρs ρs' : sem_sigs Σ) :
    ρs ≤Rs ρs' →
    τ₂ ≤T τ₁ →
    κ₁ ≤T κ₂ →
    (τ₁ -{ ρs }-> κ₁) ≤T (τ₂ -{ ρs' }-> κ₂).
  Proof.
    iIntros (Hρsle Hτ₂₁ Hκ₁₂ v) "#Hτκ₁ %w !# Hτ₂".
    iApply fupd_ewp. 
    iApply (ewp_pers_smono_r with "[Hτκ₁ Hτ₂]"); [apply Hρsle| |iIntros "!# % H //= $H"].
    iApply (ewp_pers_mono with "[Hτκ₁ Hτ₂]").
    { iApply ("Hτκ₁" with "[Hτ₂]"); by rewrite Hτ₂₁. }
    iIntros "!# % Hκ !>". by rewrite Hκ₁₂.
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

  Lemma ty_le_forall ρs₁ ρs₂ (τ₁ τ₂ : sem_ty Σ → sem_sigs Σ → sem_ty Σ) :
    ρs₁ ≤Rs ρs₂ →
    (∀ α, τ₁ α ρs₁ ≤T τ₂ α ρs₂) →
    (∀T: α, ρs₁ , τ₁ α ρs₁)%T ≤T (∀T: α, ρs₂ , τ₂ α ρs₂).
  Proof.
    iIntros (Hρsle Hτ₁₂ v) "#Hτ₁ %τ !#". unfold sem_ty_forall.
    iApply fupd_ewp. 
    iApply (ewp_pers_smono_r with "[Hτ₁]"); [apply Hρsle| |iIntros "!# % H //= $H"].
    iApply (ewp_pers_mono with "[Hτ₁]"); [iApply "Hτ₁"|].
    iIntros "!# % Hτ !>". by iApply Hτ₁₂.
  Qed.

  Lemma ty_le_sig_forall (τ₁ τ₂ : sem_sigs Σ → sem_ty Σ) :
    (∀ θ, τ₁ θ ≤T τ₂ θ) →
    (∀S: θ, τ₁ θ) ≤T (∀S: θ, τ₂ θ).
  Proof.
    iIntros (Hτ₁₂ v) "Hτ₁ %ρ".
    iApply (ewp_pers_mono with "[Hτ₁]"); [iApply "Hτ₁"|].
    iIntros "!# % Hτ₁ !>".
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

  Lemma env_le_swap_env_singl Γ x τ : 
    (x, τ) :: Γ ≤E Γ ++ [(x, τ)].
  Proof.
    induction Γ as [|[y κ] Γ'].
    { solve_env. }
    rewrite -app_comm_cons.
    eapply env_le_trans; [apply env_le_swap_second|].
    apply env_le_cons; last done.
    apply IHΓ'.
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

  Lemma copy_ty_uarr τ ρ κ : copy_ty (τ -{ ρ }-> κ).
  Proof. solve_copy. Qed.
  
  Lemma copy_ty_prod τ κ : copy_ty τ → copy_ty κ → copy_ty (τ × κ).
  Proof. by solve_copy. Qed.
  
  Lemma copy_ty_sum τ κ : copy_ty τ → copy_ty κ → copy_ty (τ + κ).
  Proof. by solve_copy. Qed.

  Lemma copy_ty_forall C ρs : copy_ty (∀T: α, ρs , C α).
  Proof. by solve_copy. Qed.

  Lemma copy_ty_ref τ : copy_ty (Refᶜ τ).
  Proof. by solve_copy. Qed.

  Lemma copy_ty_option τ : copy_ty τ → copy_ty (Option τ).
  Proof. by solve_copy. Qed.

  Lemma copy_ty_exists τ : (∀ α, copy_ty (τ α)) → copy_ty (∃: α, τ α).
  Proof. solve_copy. apply H. Qed.

  Lemma copy_ty_rec τ `{NonExpansive τ}: 
    (∀ α, copy_ty (τ α)) → copy_ty (μT: α, τ α).
  Proof. 
    iIntros (H v). rewrite sem_ty_rec_unfold.
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
