
(* reasoning_os.v *)

From iris.proofmode Require Import base tactics.
From iris.base_logic.lib Require Import iprop invariants.

(* Hazel Reasoning *)
From hazel.program_logic Require Import weakest_precondition 
                                        tactics 
                                        shallow_handler_reasoning 
                                        deep_handler_reasoning 
                                        state_reasoning.

(* Local imports *)
From haffel.lib Require Import base.
From haffel.lang Require Import hazel.
From haffel.lang Require Import subst_map.
From haffel.logic Require Import iEff.
From haffel.logic Require Import sem_def.
From haffel.logic Require Import sem_types.
From haffel.logic Require Import sem_env.
From haffel.logic Require Import sem_sub_typing.


Section reasoning_os.

  Context `{!heapGS Σ}.

  Definition is_os (σ : sem_sig Σ) : iProp Σ := 
    ((σ ≤S ⊥) ∨ (∃ τ κ, ⌜ NonExpansive2 τ ⌝ ∗ ⌜ NonExpansive2 κ ⌝ ∗
                        (σ ≤S (μ∀TS: θ, α, τ θ α ⇒ κ θ α | OS)%S) ∧
                        ((μ∀TS: θ, α, τ θ α ⇒ κ θ α | OS)%S ≤S σ)))%I.

  Lemma bot_is_os : ⊢ is_os ⊥.
  Proof. iLeft. iApply sig_le_refl. Qed.

  Lemma os_is_os A B `{ NonExpansive2 A, NonExpansive2 B} : 
    ⊢ is_os (μ∀TS: θ, α, A θ α ⇒ B θ α | OS)%S.
  Proof. 
    iRight. iExists A, B. 
    do 2 (iSplit; first done).
    iSplit; iApply sig_le_refl. 
  Qed.

  Lemma ewp_mono_os σ e Φ Φ' :
    is_os σ -∗
    EWP e <| ⊥ |> {| σ |} {{ v, Φ v }} -∗
    (∀ v : val, Φ v ={⊤}=∗ Φ' v) -∗ EWP e <| ⊥ |> {| σ |} {{ v, Φ' v }}.
  Proof.
    iIntros "#HOS Hewp Himp". 
    iDestruct "HOS" as "[Hbot|(%τ & %κ & (%Hn₁ & %Hn₂ & Hσ₁ & Hσ₂))]".
    { iApply ewp_ms_prot_mono; [iApply sig_le_nil|].
      iDestruct (ewp_ms_prot_mono with "Hbot Hewp") as "Hewp'".
      iApply (ewp_mono with "Hewp' Himp").  }
    iApply ewp_ms_prot_mono; [iApply "Hσ₂"|].
    iDestruct (ewp_ms_prot_mono with "Hσ₁ Hewp") as "Hewp".
    iLöb as "IH" forall (e).
    rewrite !ewp_unfold /ewp_pre.
    destruct (to_val e) eqn:?.
    { iMod "Hewp" as "Hewp". by iApply "Himp". }
    destruct (to_eff e) eqn:?.
    - simpl. destruct p eqn:?, p0 eqn:?, m.
      { iDestruct "Hewp" as "(%Φ'' & [] & ?)". }
      iDestruct "Hewp" as "(%Φ'' & HΨ & Hps)". 
      iExists (λ w, Φ'' w ∗ (∀ v, Φ v ={⊤}=∗ Φ' v)%I)%I.
      iSplitL "HΨ Himp".
      + rewrite !sem_sig_eff_rec_eq.
        iDestruct "HΨ" as "(%α & %u & Hrw & HA & HPost)".
        iExists α, u. iFrame. simpl.
        iIntros (b) "HB". iFrame. by iApply "HPost".
      + iDestruct "Hps" as "#Hps".
        iIntros "!# % (HΦ'' & Himp)". 
        iSpecialize ("Hps" with "HΦ''"). iNext.
        iApply ("IH" with "Himp Hps"). 
    - iIntros (σ₁ ns κ' κs nt) "Hstate".
      iSpecialize ("Hewp" $! σ₁ ns κ' κs nt with "Hstate"). 
      iMod "Hewp" as "Hewp". iModIntro.
      iDestruct "Hewp" as "(Hred & Hpost)".
      iFrame. iIntros (e₂ σ₂) "Hprim Hcred".
      iSpecialize ("Hpost" $! e₂ σ₂ with "Hprim Hcred").
      iInduction (num_laters_per_step) as [|] "IH'"; simpl.
      { iMod "Hpost" as "Hpost". iModIntro. iNext.
        do 2 (iMod "Hpost" as "Hpost"; iModIntro).
        iDestruct "Hpost" as "[$ He₂]".
        iApply ("IH" with "Himp He₂"). }
      iMod "Hpost" as "Hpost". iModIntro. iNext.
      iMod "Hpost" as "Hpost". 
      iSpecialize ("IH'" with "Himp Hpost").
      iMod "IH'" as "IH'". do 2 iModIntro. iNext.
      iApply "IH'".
  Qed.

End reasoning_os.
