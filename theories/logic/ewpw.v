(* ewpw.v *)

From iris.proofmode Require Import base tactics.
From iris.algebra Require Import ofe gmap.
From iris.base_logic Require Export iprop upred invariants.

(* Hazel Reasoning *)
From hazel.program_logic Require Import weakest_precondition 
                                        basic_reasoning_rules
                                        state_reasoning
                                        shallow_handler_reasoning
                                        deep_handler_reasoning
                                        tactics
                                        protocols.

(* Local imports *)
From haffel.lib Require Import logic.
From haffel.lang Require Import haffel.
From haffel.logic Require Import sem_def.
From haffel.logic Require Import mode.
From haffel.logic Require Import sem_sig.
From haffel.logic Require Import sem_row.

(* EWP wrapper *)
Definition ewpw `{!heapGS Σ} (E : coPset) (e : expr) (ρ : sem_row Σ) (Φ : val -d> iPropO Σ) : iPropO Σ := 
    (EWP e @ E <| ⟦ filter_os ρ%R ⟧ |> {| ⟦ ρ%R ⟧ |} {{ Φ }})%R%I.

Global Opaque env_dom.

Notation "'EWPW' e @ E {{ Φ } }" :=
  (ewpw E e%E ⊥ Φ)
  (at level 20, e, Φ at level 200,
   format "'[' 'EWPW'  e  '/' '[          ' @  E  {{  Φ  } } ']' ']'") : bi_scope.

(* Postcondition includes binder. *)
Notation "'EWPW' e @ E {{ v , Φ } }" :=
  (ewpw E e%E ⊥ (λ v, Φ)%I)
  (at level 20, e, Φ at level 200,
   format "'[' 'EWPW'  e  '/' '[          ' @  E  {{  v ,  Φ  } } ']' ']'") : bi_scope.

(* Mask is implicitly specified by ⊤. *)
Notation "'EWPW' e {{ v , Φ } }" :=
  (ewpw ⊤ e%E ⊥ (λ v, Φ)%I)
  (at level 20, e, Φ at level 200,
   format "'[' 'EWPW'  e  '/' '[          ' {{  v ,  Φ  } } ']' ']'") : bi_scope.

(* No binder and no mask. *)
Notation "'EWPW' e {{ Φ } }" :=
  (ewp_def ⊤ e%E ⊥ Φ%I)
  (at level 20, e, Φ at level 200,
   format "'[' 'EWPW'  e  '/' '[          ' {{  Φ  } } ']' ']'") : bi_scope.

Notation "'EWPW' e @ E '<|' ρ '|' '>' {{ Φ } }" :=
  (ewpw E e%E ρ%R Φ)
  (at level 20, e, ρ, Φ at level 200,
   format "'[' 'EWPW'  e  '/' '[          ' @  E '<|' ρ '|' '>' {{  Φ  } } ']' ']'") : bi_scope.

(* Postcondition includes binder. *)
Notation "'EWPW' e @ E '<|' ρ '|' '>' {{ v , Φ } }" :=
  (ewpw E e%E ρ%R (λ v, Φ)%I)
  (at level 20, e, ρ, Φ at level 200,
   format "'[' 'EWPW'  e  '/' '[          ' @  E '<|' ρ '|' '>'  {{  v ,  Φ  } } ']' ']'") : bi_scope.

(* Mask is implicitly specified by ⊤. *)
Notation "'EWPW' e '<|' ρ '|' '>' {{ v , Φ } }" :=
  (ewpw ⊤ e%E ρ%R (λ v, Φ)%I)
  (at level 20, e, ρ, Φ at level 200,
   format "'[' 'EWPW'  e  '/' '[          ' '<|' ρ '|' '>' {{  v ,  Φ  } } ']' ']'") : bi_scope.

(* No binder and no mask. *)
Notation "'EWPW' e '<|' ρ '|' '>' {{ Φ } }" :=
  (ewpw ⊤ e%E ρ%R Φ%I)
  (at level 20, e, ρ, Φ at level 200,
   format "'[' 'EWPW'  e  '/' '[          ' '<|' ρ '|' '>' {{  Φ  } } ']' ']'") : bi_scope.

Global Instance ewpw_ne `{!heapGS Σ} E e : 
  NonExpansive2 (ewpw E e).
Proof.
  rewrite /ewpw. intros ???????. by repeat f_equiv.
Qed.

Global Instance ewpw_proper `{!heapGS Σ} E e: 
  Proper ((≡) ==> (≡) ==> (≡)) (ewpw E e).
Proof. apply ne_proper_2. apply ewpw_ne. Qed.

Global Instance ewpw_contractive `{!heapGS Σ} E e ρ : 
  TCEq (to_val e) None →
  TCEq (to_eff e) None →
  Contractive (ewpw E e ρ).
Proof.
  rewrite /ewpw. intros ??????. 
  by f_contractive.
Qed.

Section reasoning.

Context `{!heapGS Σ}. 

Lemma ewpw_value (E : coPset) ρ Φ (v : val) :
  Φ v -∗ EWPW v @E <| ρ |> {{ Φ }}.
Proof.
  iIntros "HΦ". rewrite /ewpw. by iApply ewp_value. 
Qed.

Lemma ewpw_bot E e Φ :
  EWP e @ E {{ v, Φ v }} -∗
  EWPW e @ E {{ Φ }}.
Proof. 
  iIntros "Hewp". rewrite /ewpw /=.
  iApply ewp_ms_prot_mono.
  { iApply iEff_le_bottom. }
  rewrite filter_os_nil.
  iApply ewp_os_prot_mono.
  { iApply iEff_le_bottom. }
  iApply "Hewp".
Qed.

Lemma ewpw_bot_inv e E Φ :
  EWPW e @ E {{ Φ }} -∗
  EWP e @ E {{ v, Φ v }}.
Proof. 
  iIntros "Hewp".
  rewrite /ewpw /=.
  rewrite filter_os_nil.
  iApply ewp_ms_prot_mono.
  { iApply row_nil_iEff_bot. }
  iApply ewp_os_prot_mono.
  { iApply row_nil_iEff_bot. }
  iApply "Hewp".
Qed.

Lemma ewpw_sub E e ρ ρ' Φ :
  ρ ≤R ρ' -∗ 
  EWPW e @E <| ρ |> {{ Φ }} -∗ EWPW e @E <| ρ' |> {{ Φ }}. 
Proof.
  iIntros "#Hρρ' Hewp".
  rewrite /ewpw.
  iApply ewp_ms_prot_mono; first (iApply (row_le_iEff with "Hρρ'")). 
  iApply ewp_os_prot_mono; last done. 
  { iApply row_le_iEff. by iApply row_le_filter_os_mono. }
Qed.

Lemma ewp_mono_os E (Ψ Ψ' : iEff Σ) e Φ Φ' `{! MonoProt Ψ' } :
  EWP e @ E <| Ψ |> {| Ψ' |} {{ v, Φ v }} -∗
  (∀ v : val, Φ v ={E}=∗ Φ' v) -∗ EWP e @ E <| Ψ |> {| Ψ' |} {{ v, Φ' v }}.
Proof.
  iIntros "Hewp Himp". 
  iLöb as "IH" forall (e).
  rewrite !ewp_unfold /ewp_pre.
  destruct (to_val e) eqn:?.
  { iMod "Hewp" as "Hewp". by iApply "Himp". }
  destruct (to_eff e) eqn:?.
  - simpl. destruct p eqn:?, p0 eqn:?, m;
    iDestruct "Hewp" as "(%Φ'' & HΨ & Hps)".
    + iExists Φ''. iFrame.
      iIntros (?) "HΦ''". iSpecialize ("Hps" $! w with "HΦ''").
      iNext. iApply ("IH" with "Hps Himp").
    + iExists (λ w, Φ'' w ∗ (∀ v, Φ v ={E}=∗ Φ' v)%I)%I;
      iSplitL "HΨ Himp".
      { destruct MonoProt0 as [].
        iApply (monotonic_prot with "[Himp] HΨ"); iIntros "% $ {$Himp}". }
      try (iDestruct "Hps" as "#Hps"; iModIntro).
      iIntros "% (HΦ'' & Himp)". 
      iSpecialize ("Hps" with "HΦ''"); iNext;
      iApply ("IH" with "Hps Himp").
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
      iApply ("IH" with "He₂ Himp" ). }
    iMod "Hpost" as "Hpost". iModIntro. iNext.
    iMod "Hpost" as "Hpost". iClear "IH".
    iMod ("IH'" with "Hpost Himp") as "IH".
    do 2 iModIntro. iNext. iApply "IH".
Qed.

Corollary ewp_mono_os_row E (ρ ρ' : sem_row Σ) e Φ Φ' `{! OSRow ρ' } :
  EWP e @ E <| ⟦ ρ ⟧%R |> {| ⟦ ρ' ⟧%R |} {{ v, Φ v }} -∗
  (∀ v : val, Φ v ={E}=∗ Φ' v) -∗ EWP e @ E <| ⟦ ρ ⟧%R |> {| ⟦ ρ' ⟧%R |} {{ v, Φ' v }}.
Proof.
  iIntros "Hewp Himp". 
  iApply (ewp_mono_os with "Hewp Himp").
  destruct OSRow0. constructor. iApply monotonic_prot.
Qed.

Lemma ewpw_mono_os E ρ e Φ Φ' `{! OSRow ρ} :
  EWPW e @ E <| ρ |> {{ Φ }} -∗
  (∀ v : val, Φ v ={E}=∗ Φ' v) -∗ 
  EWPW e @E <| ρ |> {{ Φ' }}. 
Proof.
  iIntros "Hewp HΦ". rewrite /ewpw.
  assert (OSRow (filter_os ρ)).
  { by apply row_filter_os_os_row. }
  iApply (@ewp_mono_os_row _ (filter_os ρ) ρ e Φ Φ' _ with "Hewp HΦ").
Qed.

Lemma ewpw_mono E ρ e Φ Φ' :
  EWPW e @E <| ρ |> {{ Φ }} -∗
  □ (∀ v : val, Φ v ={E}=∗ Φ' v) -∗ 
  EWPW e @E <| ρ |> {{ Φ' }}.
Proof.
  iIntros "Hewp HΦ". rewrite /ewpw. 
  iApply (ewp_pers_mono with "Hewp HΦ").
Qed.

Lemma ewpw_pure_step' E e e' ρ Φ :
  pure_prim_step e e' → 
  ▷ EWPW e' @E <| ρ |>  {{ Φ }} -∗
  EWPW e @E <| ρ |> {{ Φ }}. 
Proof.
  iIntros "%Hprim Hewp". rewrite /ewpw. 
  by iApply ewp_pure_step'.
Qed.

Lemma ewpw_bind k `{NeutralEctx k} E ρ e e' Φ :
  e' = fill k e →
  EWPW e @E <| ρ |> {{ w, EWPW (fill k w) @E <| ρ |> {{ Φ }} }} -∗
  EWPW e' @E <| ρ |> {{ Φ }}.
Proof.
  iIntros (?) "Hewp". rewrite /ewpw.
  by iApply ewp_bind.
Qed.

Lemma ewpw_alloc E ρ Φ v :
  ▷ (∀ (l : loc), l ↦ v ={E}=∗ Φ #l) -∗
    EWPW (ref v)%E @E <| ρ |> {{ Φ }}.
Proof.
  iIntros "H". rewrite /ewpw. by iApply ewp_alloc. 
Qed.

Lemma ewpw_load E ρ Φ l q v :
  ▷ l ↦{q} v -∗
    ▷ (l ↦{q} v ={E}=∗ Φ v) -∗
      EWPW (Load #l)%E @E <| ρ |> {{ Φ }}.
Proof.
  iIntros "H". rewrite /ewpw. by iApply ewp_load. 
Qed.

Lemma ewpw_store E ρ Φ l v w :
  ▷ l ↦ v -∗
    ▷ (l ↦ w ={E}=∗ Φ #()) -∗
      EWPW (#l <- w)%E @E <| ρ |> {{ Φ }}.
Proof.
  iIntros "H". rewrite /ewpw. by iApply ewp_store. 
Qed.

Lemma ewpw_replace E ρ Φ l v w :
  ▷ l ↦ v -∗
    ▷ (l ↦ w ={E}=∗ Φ v) -∗
      EWPW (#l <!- w)%E @E <| ρ |> {{ Φ }}.
Proof.
  iIntros "H". rewrite /ewpw. by iApply ewp_replace. 
Qed.

Lemma ewpw_free E ρ Φ l v :
  ▷ l ↦ v -∗
    ▷ (|={E}=> Φ v) -∗
      EWPW (Free #l)%E @E <| ρ |> {{ Φ }}.
Proof.
  iIntros "H". rewrite /ewpw. by iApply ewp_free. 
Qed.

Lemma ewpw_atomic E1 E2 e ρ Φ `{!Atomic StronglyAtomic e} :
  TCEq (to_eff e) None →
    (|={E1,E2}=> EWPW e @E2 <| ρ |> {{ v, |={E2,E1}=> Φ v }}) -∗
      EWPW e @E1 <| ρ |> {{ Φ }}.
Proof.
  iIntros (?) "H". rewrite /ewpw. by iApply ewp_atomic. 
Qed.

Lemma ewpw_eff_os E ρ Φ v k :
  iEff_car (upcl OS ⟦ filter_os ρ ⟧%R) v (λ w, ▷ EWPW (fill k (Val w)) @ E <| ρ |> {{ Φ }}) -∗
  EWPW (of_eff OS v k) @ E <| ρ |> {{ Φ }}.
Proof. 
  iIntros "H". rewrite /ewpw /=.
  by iApply ewp_eff_os.
Qed.

Lemma ewpw_do_os E l s v ρ Φ :
  iEff_car ⟦ filter_os ρ ⟧%R ((effect l, s), v)%V Φ -∗ 
  EWPW (do: ((effect l, s), v)%V) @ E <| ρ |> {{ Φ }}.
Proof.
  iIntros "Hρ".
  rewrite /ewpw /=. iApply ewp_do_os.
  simpl. iExists Φ. iFrame. iIntros (w) "$".
Qed.

Lemma ewpw_do_ms E l s v ρ Φ :
  iEff_car ⟦ ρ ⟧%R ((effect l, s), v)%V Φ -∗ 
  EWPW (doₘ: ((effect l, s), v)%V) @ E <| ρ |> {{ Φ }}.
Proof.
  iIntros "Hρ".
  rewrite /ewpw /=. 
  iApply ewp_do_ms;
  simpl; iExists Φ; iFrame; iIntros "!# % $".
Qed.

Lemma ewpw_lft E l σ ρ e Φ :
  EWPW e @E  <| ρ |> {{ Φ }} -∗
  EWPW (lft: (effect l, e)) @E <| (l, σ) ·: ρ |> {{ Φ }}.
Proof. 
  iIntros "He".
  rewrite /lft_def. rewrite /ewpw. ewp_pure_steps.
  iApply (ewp_deep_try_with_mode with "[He]").
  { ewp_pure_steps. iApply "He". }
  iLöb as "IH".
  rewrite {2} deep_handler_mode_unfold /deep_handler_mode_pre. 
  iSplit; last iSplit.
  - iIntros (v) "HΦ". by ewp_pure_steps.
  - iIntros (v k) "Hρ".
    iDestruct "Hρ" as "(%Φ' & (%w & %l' & %s' & %σ' & -> & #Hlookup' & Hσ') & HPost)". 
    ewp_pure_steps'.
    destruct (decide (l = l')) as [->|Hneg].
    + ewp_pure_steps'. iApply ewp_do_os. 
      rewrite filter_os_lookup. iExists Φ'. simpl.
      iSplitL "Hσ'".
      { iExists w, l', (S s'), σ'. rewrite /sem_row_cons. 
        rewrite filter_os_lookup /sem_row_ins lookup_insert_ne // row_tun_lookup_alt. iFrame "#∗". 
        by replace (Z.add (Z.of_nat s') (Zpos xH)) with (Z.of_nat (S s')) by lia. }
      iIntros (v') "HΦ'". iApply ("HPost" with "HΦ'"). by iNext.
    + ewp_pure_steps'. iApply ewp_do_os. 
      rewrite filter_os_lookup. iExists Φ'. simpl.
      iSplitL "Hσ'".
      { iExists w, l', s', σ'. 
        rewrite filter_os_lookup /sem_row_cons /sem_row_ins lookup_insert_ne //; last (intros H; inv H).
        rewrite row_tun_lookup_ne //. by iFrame "#∗".  }
      iIntros (v') "HΦ'". iApply ("HPost" with "HΦ'"). by iNext.
  - iIntros (v k) "Hρ". simpl.
    iDestruct "Hρ" as "(%Φ' & (%w & %l' & %s' & %σ' & -> & #Hlookup' & Hσ') & #HPost)". 
    ewp_pure_steps'.
    destruct (decide (l = l')) as [->|Hneg].
    + ewp_pure_steps'. iApply ewp_do_ms. 
      iExists Φ'. simpl.
      iSplitL "Hσ'".
      { iExists w, l', (S s'), σ'. rewrite /sem_row_cons /sem_row_ins lookup_insert_ne // row_tun_lookup_alt. iFrame "#∗". 
        by replace (Z.add (Z.of_nat s') (Zpos xH)) with (Z.of_nat (S s')) by lia. }
      iIntros "!# %v' HΦ'". iApply ("HPost" with "HΦ'"). by iNext.
    + ewp_pure_steps'. iApply ewp_do_ms. iExists Φ'. simpl.
      iSplitL "Hσ'".
      { iExists w, l', s', σ'. 
        rewrite /sem_row_cons /sem_row_ins lookup_insert_ne; last (intros H; inv H). 
        rewrite row_tun_lookup_ne //. by iFrame "#∗".  }
      iIntros "!# %v' HΦ'". iApply ("HPost" with "HΦ'"). by iNext.
Qed.

Lemma ewpw_unlft E l ρ e Φ :
  EWPW e @E <| ⦗ ρ | l ⦘ |> {{ Φ }} -∗
  EWPW (unlft: (effect l, e)) @E <| ρ |> {{ Φ }}.
Proof.
  iIntros "He".
  rewrite /unlft_def. rewrite /ewpw. ewp_pure_steps.
  iApply (ewp_deep_try_with_mode with "[He]").
  { ewp_pure_steps. iApply "He". }
  iLöb as "IH".
  rewrite {2} deep_handler_mode_unfold /deep_handler_mode_pre. 
  iSplit; last iSplit.
  - iIntros (v) "HΦ". by ewp_pure_steps.
  - iIntros (v k) "Hρ".
    iDestruct "Hρ" as "(%Φ' & (%w & %l' & %s' & %σ' & -> & #Hlookup' & Hσ') & HPost)". 
    ewp_pure_steps'.
    destruct (decide (l = l')) as [->|Hneg].
    + ewp_pure_steps'. iApply ewp_do_os. 
      rewrite filter_os_lookup row_tun_lookup. 
      iDestruct "Hlookup'" as "[(%s & -> & Hlookup) HOS]". iExists Φ'. simpl.
      iSplitL "Hσ'".
      { iExists w, l', s, σ'. rewrite filter_os_lookup. iFrame "#∗". 
        by replace (Z.sub (Z.of_nat (S s)) (Zpos xH)) with (Z.of_nat s) by lia. }
      iIntros (v') "HΦ'". iApply ("HPost" with "HΦ'"). by iNext.
    + ewp_pure_steps'. iApply ewp_do_os. 
      rewrite filter_os_lookup row_tun_lookup_ne //. iExists Φ'. simpl.
      iSplitL "Hσ'".
      { iExists w, l', s', σ'. rewrite filter_os_lookup //. by iFrame "#∗".  }
      iIntros (v') "HΦ'". iApply ("HPost" with "HΦ'"). by iNext.
  - iIntros (v k) "Hρ". simpl.
    iDestruct "Hρ" as "(%Φ' & (%w & %l' & %s' & %σ' & -> & #Hlookup' & Hσ') & #HPost)". 
    ewp_pure_steps'.
    destruct (decide (l = l')) as [->|Hneg].
    + ewp_pure_steps'. iApply ewp_do_ms. 
      rewrite row_tun_lookup. iDestruct "Hlookup'" as "(%s & -> & Hlookup)". 
      iExists Φ'. simpl.
      iSplitL "Hσ'".
      { iExists w, l', s, σ'. iFrame "#∗". 
        by replace (Z.sub (Z.of_nat (S s)) (Zpos xH)) with (Z.of_nat s) by lia. }
      iIntros "!# %v' HΦ'". iApply ("HPost" with "HΦ'"). by iNext.
    + ewp_pure_steps'. iApply ewp_do_ms. iExists Φ'. simpl.
      iSplitL "Hσ'".
      { iExists w, l', s', σ'. rewrite row_tun_lookup_ne //. by iFrame "#∗".  }
      iIntros "!# %v' HΦ'". iApply ("HPost" with "HΦ'"). by iNext.
Qed.

Lemma handler_effect_propagated_cond E l l' s' Ψ :
 ¬ (l = l' ∧ s' = 0) →
 ⊢ EWP if: (effect l')%V = (effect l)%V then #s' = #0 else #false @ E <| Ψ |> {{ v, ⌜v = #false⌝ }}.
Proof.
  intros Hneg. rewrite not_and_l in Hneg. iIntros.
  destruct (decide (l = l')) as [->|], Hneg; ewp_pure_steps'. 
  iPureIntro. rewrite bool_decide_false //. 
  intros H'. simplify_eq. assert (s' = 0) by lia. simplify_eq. 
Qed.

Definition shallow_handler_ls
  (E : coPset)
  (l : label)
  (σ : sem_sig Σ)
  (ρ : sem_row Σ)
  (m : mode)
  (Φ : val -d> iPropO Σ)
  (h r : expr)
  (ρ'  : sem_row Σ)
  (Φ' : val -d> iPropO Σ) : iProp Σ := (
  (* Subsumption on row *)
  (ρ ≤R ρ') ∗

  (* One-Shot Row *)
  (⌜ m = OS → OSRow ρ ⌝) ∗

  □?m (
  (* Correctness of the return branch. *)
  (∀ (v : val), Φ v -∗ EWPW r v @ E <| ρ' |> {{ Φ' }}) ∧

  (* Correctness of the effect branch. *)
  (∀ (v k : val),
     iEff_car (upcl σ.1 σ.2) v (λ w, EWPW k w @ E <| (l, σ) ·: ρ |> {{ Φ }}) -∗
       EWPW h v k @ E <| ρ' |> {{ Φ' }}))
  )%I.

Lemma ewpw_shallow_try_ls E (l : label) m σ ρ ρ' e (h r : val) Φ Φ' :
  EWPW e @ E <| (l, σ) ·: ρ |> {{ Φ }} -∗
  shallow_handler_ls E l σ ρ m Φ h r ρ' Φ' -∗
  EWPW (ShallowTryLSV e l h r) @E <| ρ' |> {{ Φ' }}.
Proof.
  iIntros "He H". rewrite /ShallowTryLSV /shallow_try_ls /ewpw. 
  iLöb as "IH" forall (e). ewp_pure_steps.
  iApply (ewp_try_with_mode with "He").
  rewrite /shallow_handler_ls.
  iDestruct "H" as "(#Hle & %HOS & Hbr)". 
  iSplit; last iSplit.
  - rewrite {2} bi.intuitionistically_if_elim. iDestruct "Hbr" as "[$ _]".
  - iIntros (v k) "Hρ".
    ewp_pure_steps. 
    iDestruct "Hρ" as "(%Φ'' & (%v' & %l' & %s' & %σ' & %Heq' & Hlookup' & Hσ') & HPost)".
    inv Heq'. destruct (decide (l = l' ∧ s' = 0)) as [[-> ->]|Hneg].
    + ewp_pure_steps'.
      rewrite {2} bi.intuitionistically_if_elim. iDestruct "Hbr" as "[_ H]".
      iApply "H". iExists Φ''. 
      rewrite filter_os_lookup lookup_insert.
      iDestruct "Hlookup'" as "[#Heq #HσOS]".
      rewrite option_equivI. iRewrite - "Heq" in "HσOS".
      rewrite prod_equivI_2 (iEff_equivI σ.2 σ'.2).
      iRewrite - ("Heq" $! v' Φ'') in "Hσ'". iFrame. 
      iRewrite "HσOS". simpl. iIntros (w) "Φ''". by iApply "HPost".
    + do 19 ewp_value_or_step. iApply (ewp_if_false with "[]").
      { by iApply handler_effect_propagated_cond. }
      iApply (ewp_bind [AppRCtx _]); first done.
      iApply (ewpw_sub with "Hle"). iApply ewpw_unlft. rewrite /ewpw.
      ewp_pure_steps. iApply ewp_do_os. iExists Φ''. simpl. 
      rewrite filter_os_lookup lookup_insert_ne; last (intros H'; inv H'; tauto).
      iSplitR "HPost Hbr".
      { iExists v', l', s', σ'. iFrame "#∗". iSplit; first done. 
        rewrite filter_os_lookup. iFrame. }
      iIntros (w) "HΦ''". do 5 ewp_value_or_step.
      iApply ("IH" with "[HΦ'' HPost] [Hbr]"); first by iApply "HPost".
      by iFrame "#∗".
  - iIntros (v k) "Hρ".
    ewp_pure_steps. 
    iDestruct "Hρ" as "(%Φ'' & (%v' & %l' & %s' & %σ' & %Heq' & #Hlookup' & Hσ') & #HPost)".
    inv Heq'. destruct (decide (l = l' ∧ s' = 0)) as [[-> ->]|Hneg].
    + ewp_pure_steps'.
      rewrite {2} bi.intuitionistically_if_elim. iDestruct "Hbr" as "[_ H]".
      iApply "H". iExists Φ''. 
      rewrite lookup_insert option_equivI prod_equivI_2 iEff_equivI.
      iRewrite - ("Hlookup'" $! v' Φ'') in "Hσ'". iFrame.
      destruct σ.1; simpl; last iIntros "!#"; iIntros (w) "Φ''"; by iApply "HPost".
    + do 19 ewp_value_or_step. iApply (ewp_if_false with "[]").
      { by iApply handler_effect_propagated_cond. }
      iApply (ewp_bind [AppRCtx _]); first done.
      iApply (ewpw_sub with "Hle"). iApply ewpw_unlft. rewrite /ewpw.
      ewp_pure_steps. rewrite lookup_insert_ne; last (intros H'; inv H'; tauto).
      iApply ewp_do_ms. destruct m; simpl.
      * specialize (HOS eq_refl).
        iDestruct (os_row_mono_prot _ l' s' σ' with "Hlookup'") as "Hmono".
        iAssert (shallow_handler_ls E l σ _ OS Φ h r ρ' Φ') with "[Hbr]" as "H".
        { rewrite /shallow_handler_ls. simpl. by iFrame "#∗". }
        iExists (λ v, Φ'' v ∗ shallow_handler_ls E l σ ρ OS Φ h r ρ' Φ')%I.
        iSplitL; [|iIntros "!# %w [HΦ'' H]"; do 5 ewp_value_or_step; 
                   iSpecialize ("HPost" with "HΦ''"); iApply ("IH" with "HPost H")].
        iExists v', l', s', σ'. iFrame "#∗".
        iSplit; [done|]. iApply ("Hmono" with "[H] Hσ'"). iIntros (w) "$ //".
      * iDestruct "Hbr" as "#Hbr".
        iExists Φ''. iSplitL "Hσ'".
        { iExists v', l', s', σ'. by iFrame "#∗". }
        iIntros (w) "!# HΦ''". do 5 ewp_value_or_step.
        iApply ("IH" with "[HΦ'' HPost] [Hbr]"); first by iApply "HPost".
        by iFrame "#∗".
Qed.

Notation deep_handler_ls_type Σ :=
  (coPset -d> label-d> sem_sig Σ -d> sem_row Σ -d> mode -d> (val -d> iPropO Σ) 
          -d> expr -d> expr
          -d> sem_row Σ -d> (val -d> iPropO Σ) -d> iPropO Σ) (only parsing).

Definition deep_handler_ls_pre `{irisGS eff_lang Σ} : 
  deep_handler_ls_type Σ → deep_handler_ls_type Σ := (
  λ deep_handler_ls E l σ ρ m Φ h r ρ' Φ',
  (* Subsumption on row *)
  (ρ ≤R ρ') ∗

  (* One-Shot Row *)
  (⌜ m = OS → OSRow ρ ⌝) ∗

  □?m (
  (* Correctness of the return branch. *)
  (∀ (v : val), Φ v -∗ EWPW r v @ E <| ρ' |> {{ Φ' }})
  ) ∧

  (* Correctness of the effect branch. *)
  □ (
  (∀ (v k : val),
     iEff_car (upcl σ.1 σ.2) v (λ w, 
        ∀ ρ'' Φ'', 
          ▷ deep_handler_ls E l σ ρ m Φ h r ρ'' Φ'' -∗
          EWPW k w @ E <| ρ'' |> {{ Φ'' }}
     ) -∗
       EWPW h v k @ E <| ρ' |> {{ Φ' }}))
  )%I.

(*            osrow *)
(*         | OS  | MS *)   
(*    ------------------- *)
(*    | OS | ros | rms *)
(* m  | MS | rms | rms *)

Local Instance deep_handler_ls_pre_contractive `{irisGS eff_lang Σ} : Contractive deep_handler_ls_pre.
Proof.
  rewrite /deep_handler_ls_pre => n deep deep' Hne E l σ ρ m Φ h r ρ' Φ'.
  repeat (f_contractive || f_equiv). intros ?; simpl.
  repeat (f_contractive || f_equiv); apply Hne.
Qed.
Definition deep_handler_ls `{irisGS eff_lang Σ} := fixpoint deep_handler_ls_pre.
Arguments deep_handler_ls _ _%V _%S _%R _%I _%E _%E _%R _%I.

Global Lemma deep_handler_ls_unfold `{irisGS eff_lang Σ} E l σ ρ m Φ h r ρ' Φ' :
  deep_handler_ls E l σ ρ m Φ h r ρ' Φ' ⊣⊢
    deep_handler_ls_pre deep_handler_ls E l σ ρ m Φ h r ρ' Φ'.
Proof.
  by apply (fixpoint_unfold deep_handler_ls_pre).
Qed.

Lemma ewpw_deep_try_ls E (l : label) m σ ρ ρ' e (h r : val) Φ Φ' :
  EWPW e @ E <| (l, σ) ·: ρ |> {{ Φ }} -∗
  deep_handler_ls E l σ ρ m Φ h r ρ' Φ' -∗
  EWPW (DeepTryLSV e l h r) @E <| ρ' |> {{ Φ' }}.
Proof.
  iIntros "He H". rewrite /DeepTryLSV /deep_try_ls /ewpw. 
  ewp_pure_steps.
  iApply (ewp_deep_try_with_mode with "He").
  iLöb as "IH" forall (ρ' Φ'). rewrite deep_handler_ls_unfold.
  iDestruct "H" as "(#Hle & %HOS & Hbr)". 
  rewrite deep_handler_mode_unfold /deep_handler_mode_pre.
  iSplit; last iSplit.
  - rewrite bi.intuitionistically_if_elim. iDestruct "Hbr" as "[$ _]".
  - iIntros (v k) "Hρ". ewp_pure_steps. 
    iDestruct "Hρ" as "(%Φ'' & (%v' & %l' & %s' & %σ' & %Heq' & Hlookup' & Hσ') & HPost)".
    inv Heq'. destruct (decide (l = l' ∧ s' = 0)) as [[-> ->]|Hneg].
    + ewp_pure_steps'.
      rewrite bi.intuitionistically_if_elim. iDestruct "Hbr" as "[_ H]".
      iApply "H". iExists Φ''. 
      rewrite filter_os_lookup lookup_insert.
      iDestruct "Hlookup'" as "[#Heq #HσOS]".
      rewrite option_equivI. iRewrite - "Heq" in "HσOS".
      rewrite prod_equivI_2 (iEff_equivI σ.2 σ'.2).
      iRewrite - ("Heq" $! v' Φ'') in "Hσ'". iFrame. 
      iRewrite "HσOS". simpl. iIntros (w) "HΦ''". 
      iIntros (ρ'' Φ''') "Hdeep". iApply ("HPost" with "HΦ''").
      iNext. iApply ("IH" with "Hdeep"). 
    + do 19 ewp_value_or_step.
      iApply (ewp_if_false with "[]"); first by iApply handler_effect_propagated_cond.
      iApply (ewp_bind [AppRCtx _]); first done.
      iApply (ewpw_sub with "Hle"). iApply ewpw_unlft. rewrite /ewpw.
      ewp_pure_steps. iApply ewp_do_os. iExists Φ''. simpl. 
      rewrite filter_os_lookup lookup_insert_ne //; last (intros H'; inv H'; tauto).
      iSplitR "HPost Hbr".
      { iExists v', l', s', σ'. iFrame "#∗". iSplit; first done. rewrite filter_os_lookup //. }
      iIntros (w) "HΦ''". iApply ("HPost" with "HΦ''"). iNext. iApply ("IH" with "[Hbr]").
      destruct m; rewrite deep_handler_ls_unfold /deep_handler_ls_pre; iFrame "#∗"; eauto.
  - iIntros (v k) "Hρ". ewp_pure_steps. 
    iDestruct "Hρ" as "(%Φ'' & (%v' & %l' & %s' & %σ' & %Heq' & #Hlookup' & Hσ') & #HPost)".
    inv Heq'. destruct (decide (l = l' ∧ s' = 0)) as [[-> ->]|Hneg].
    + ewp_pure_steps'.
      rewrite bi.intuitionistically_if_elim. iDestruct "Hbr" as "[_ H]".
      iApply "H". iExists Φ''. 
      rewrite lookup_insert option_equivI prod_equivI_2 iEff_equivI.
      iRewrite - ("Hlookup'" $! v' Φ'') in "Hσ'". iFrame.
      destruct σ.1; simpl; last iIntros "!#"; 
      iIntros (w) "HΦ'' % %Φ''' Hdeep"; iApply ("HPost" with "HΦ''"); iNext; by iApply "IH".
    + do 19 ewp_value_or_step.
      iApply (ewp_if_false with "[]"); first by iApply handler_effect_propagated_cond.
      iApply (ewp_bind [AppRCtx _]); first done.
      iApply (ewpw_sub with "Hle"). iApply ewpw_unlft. rewrite /ewpw.
      ewp_pure_steps. rewrite lookup_insert_ne; last (intros H'; inv H'; tauto).
      iApply ewp_do_ms. destruct m; simpl.
      * specialize (HOS eq_refl).
        iDestruct (os_row_mono_prot _ l' s' σ' with "Hlookup'") as "Hmono".
        iAssert (deep_handler_ls E l σ ρ OS Φ h r ρ' Φ') with "[Hbr]" as "H".
        { rewrite deep_handler_ls_unfold /deep_handler_ls_pre. simpl. by iFrame "#∗". }
        iExists (λ v, Φ'' v ∗ deep_handler_ls E l σ ρ OS Φ h r ρ' Φ')%I.
        iSplitL; [|iIntros "!# %w [HΦ'' Hdeep]"; iApply ("HPost" with "HΦ''"); iNext; by iApply "IH"].
        iExists v', l', s', σ'. iFrame "#∗". iSplit; [done|]. 
        iApply ("Hmono" with "[H] Hσ'"). iIntros (w) "$ //".
      * iDestruct "Hbr" as "#Hbr".
        iExists Φ''. iSplitL "Hσ'".
        { iExists v', l', s', σ'. by iFrame "#∗". }
        iIntros (w) "!# HΦ''". iApply ("HPost" with "HΦ''").
        iNext. iApply "IH".
        rewrite deep_handler_ls_unfold /deep_handler_ls_pre. simpl. by iFrame "#∗". 
Qed.

Notation deep_handler_ls_2_type Σ :=
  (coPset -d> label -d> sem_sig Σ -d> label -d> sem_sig Σ -d> sem_row Σ -d> mode -d> (val -d> iPropO Σ) 
          -d> expr  -d> expr -d> expr
          -d> sem_row Σ -d> (val -d> iPropO Σ) -d> iPropO Σ) (only parsing).

Definition deep_handler_ls_2_pre `{irisGS eff_lang Σ} : 
  deep_handler_ls_2_type Σ → deep_handler_ls_2_type Σ := (
  λ deep_handler_ls_2 E l1 σ1 l2 σ2 ρ m Φ h1 h2 r ρ' Φ',

  (* Subsumption on row *)
  (ρ ≤R ρ') ∗

  ⌜ l1 ≠ l2 ⌝ ∗

  (* One-Shot Row *)
  (⌜ m = OS → OSRow ρ ⌝) ∗

  □?m (
  (* Correctness of the return branch. *)
  (∀ (v : val), Φ v -∗ EWPW r v @ E <| ρ' |> {{ Φ' }})
  ) ∧

  (* Correctness of the effect branch 1. *)
  □ (
  (∀ (v k : val),
     iEff_car (upcl σ1.1 σ1.2) v (λ w, 
        ∀ ρ'' Φ'', 
          ▷ deep_handler_ls_2 E l1 σ1 l2 σ2 ρ m Φ h1 h2 r ρ'' Φ'' -∗
          EWPW k w @ E <| ρ'' |> {{ Φ'' }}
     ) -∗
       EWPW h1 v k @ E <| ρ' |> {{ Φ' }}) ∧

  (* Correctness of the effect branch 2. *)
  (∀ (v k : val),
     iEff_car (upcl σ2.1 σ2.2) v (λ w, 
        ∀ ρ'' Φ'', 
          ▷ deep_handler_ls_2 E l1 σ1 l2 σ2 ρ m Φ h1 h2 r ρ'' Φ'' -∗
          EWPW k w @ E <| ρ'' |> {{ Φ'' }}
     ) -∗
       EWPW h2 v k @ E <| ρ' |> {{ Φ' }})
  ))%I.

Local Instance deep_handler_ls_2_pre_contractive `{irisGS eff_lang Σ} : Contractive deep_handler_ls_2_pre.
Proof.
  rewrite /deep_handler_ls_2_pre => n deep deep' Hne E l1 σ1 l2 σ2 ρ m Φ h1 h2 r ρ' Φ'.
  repeat (f_contractive || f_equiv). intros ?; simpl.
  repeat (f_contractive || f_equiv); apply Hne.
  intros ?. repeat (f_contractive || f_equiv); apply Hne.
Qed.
Definition deep_handler_ls_2 `{irisGS eff_lang Σ} := fixpoint deep_handler_ls_2_pre.
Arguments deep_handler_ls_2 _ _%V _%S _%V _%S _%R _%I _%E _%E _%E _%R _%I.

Global Lemma deep_handler_ls_2_unfold `{irisGS eff_lang Σ} E l1 σ1 l2 σ2 ρ m Φ h1 h2 r ρ' Φ' :
  deep_handler_ls_2 E l1 σ1 l2 σ2 ρ m Φ h1 h2 r ρ' Φ' ⊣⊢
    deep_handler_ls_2_pre deep_handler_ls_2 E l1 σ1 l2 σ2 ρ m Φ h1 h2 r ρ' Φ'.
Proof.
  by apply (fixpoint_unfold deep_handler_ls_2_pre).
Qed.

Lemma ewpw_deep_try_ls_2 E (l1 l2 : label) m σ1 σ2 ρ ρ' e (h1 h2 r : val) Φ Φ' :
  EWPW e @ E <| (l1, σ1) ·: (l2, σ2) ·: ρ |> {{ Φ }} -∗
  deep_handler_ls_2 E l1 σ1 l2 σ2 ρ m Φ h1 h2 r ρ' Φ' -∗
  EWPW (DeepTryLS2V e l1 l2 h1 h2 r) @E <| ρ' |> {{ Φ' }}.
Proof.
  iIntros "He H". rewrite /DeepTryLS2V /deep_try_ls_2 /ewpw. 
  ewp_pure_steps.
  iApply (ewp_deep_try_with_mode with "He").
  iLöb as "IH" forall (ρ' Φ'). rewrite deep_handler_ls_2_unfold.
  iDestruct "H" as "(#Hle & %Hneq & %HOS & Hbr)". 
  rewrite deep_handler_mode_unfold /deep_handler_mode_pre.
  iSplit; last iSplit.
  - rewrite bi.intuitionistically_if_elim. iDestruct "Hbr" as "[$ _]".
  - iIntros (v k) "Hρ". ewp_pure_steps. 
    iDestruct "Hρ" as "(%Φ'' & (%v' & %l' & %s' & %σ' & %Heq' & Hlookup' & Hσ') & HPost)".
    inv Heq'. destruct (decide (l1 = l' ∧ s' = 0)) as [[-> ->]|Hneg].
    + ewp_pure_steps'.
      rewrite bi.intuitionistically_if_elim. iDestruct "Hbr" as "[_ H]".
      iApply "H". iExists Φ''. 
      rewrite filter_os_lookup lookup_insert.
      iDestruct "Hlookup'" as "[#Heq #HσOS]".
      rewrite option_equivI. iRewrite - "Heq" in "HσOS".
      rewrite prod_equivI_2 (iEff_equivI σ1.2 σ'.2).
      iRewrite - ("Heq" $! v' Φ'') in "Hσ'". iFrame. 
      iRewrite "HσOS". simpl. iIntros (w) "HΦ''". 
      iIntros (ρ'' Φ''') "Hdeep". iApply ("HPost" with "HΦ''").
      iNext. iApply ("IH" with "Hdeep"). 
    + destruct (decide (l2 = l' ∧ s' = 0)) as [[-> ->]|Hneg'].
      * ewp_pure_steps'.
        rewrite bi.intuitionistically_if_elim. iDestruct "Hbr" as "[_ [_ H]]".
        iApply "H". iExists Φ''. 
        rewrite filter_os_lookup lookup_insert_ne; last (intros ?; simplify_eq). 
        rewrite row_tun_lookup_ne // lookup_insert.
        iDestruct "Hlookup'" as "[#Heq #HσOS]".
        rewrite option_equivI. iRewrite - "Heq" in "HσOS".
        rewrite prod_equivI_2 (iEff_equivI σ2.2 σ'.2).
        iRewrite - ("Heq" $! v' Φ'') in "Hσ'". iFrame. 
        iRewrite "HσOS". simpl. iIntros (w) "HΦ''". 
        iIntros (ρ'' Φ''') "Hdeep". iApply ("HPost" with "HΦ''").
        iNext. iApply ("IH" with "Hdeep"). 
      * do 19 ewp_value_or_step.
        iApply (ewp_if_false with "[]"); first by iApply handler_effect_propagated_cond.
        iApply (ewp_if_false with "[]"); first by iApply handler_effect_propagated_cond.
        iApply (ewp_bind [AppRCtx _]); first done. simpl.
        iApply (ewpw_sub with "Hle"). simpl. do 2 iApply ewpw_unlft. rewrite /ewpw.
        ewp_pure_steps. iApply ewp_do_os. iExists Φ''. simpl. 
        rewrite filter_os_lookup lookup_insert_ne //; last (intros H'; inv H'; tauto).
        iSplitR "HPost Hbr".
        { iExists v', l', s', σ'. iFrame "#∗". iSplit; first done. rewrite filter_os_lookup //. 
          rewrite /sem_row_cons row_tun_ins_eq_ne // lookup_insert_ne; first iFrame.
          intros H. inv H; apply Hneg'; eauto. }
      iIntros (w) "HΦ''". iApply ("HPost" with "HΦ''"). iNext. iApply ("IH" with "[Hbr]").
      destruct m; rewrite deep_handler_ls_2_unfold /deep_handler_ls_2_pre; iFrame "#∗"; eauto.
  - iIntros (v k) "Hρ". ewp_pure_steps. 
    iDestruct "Hρ" as "(%Φ'' & (%v' & %l' & %s' & %σ' & %Heq' & #Hlookup' & Hσ') & #HPost)".
    inv Heq'. destruct (decide (l1 = l' ∧ s' = 0)) as [[-> ->]|Hneg].
    + ewp_pure_steps'.
      rewrite bi.intuitionistically_if_elim. iDestruct "Hbr" as "[_ H]".
      iApply "H". iExists Φ''. 
      rewrite lookup_insert option_equivI prod_equivI_2 iEff_equivI.
      iRewrite - ("Hlookup'" $! v' Φ'') in "Hσ'". iFrame.
      destruct σ1.1; simpl; last iIntros "!#"; 
      iIntros (w) "HΦ'' % %Φ''' Hdeep"; iApply ("HPost" with "HΦ''"); iNext; by iApply "IH".
    + destruct (decide (l2 = l' ∧ s' = 0)) as [[-> ->]|Hneg'].
      * ewp_pure_steps'.
        rewrite bi.intuitionistically_if_elim. iDestruct "Hbr" as "[_ [_ H]]". 
        iApply "H". iExists Φ''. 
        rewrite lookup_insert_ne; last (intros ?; simplify_eq).  
        rewrite row_tun_ins_eq_ne. 
        2: { intros ?. apply Hneg; eauto. }
        rewrite lookup_insert option_equivI prod_equivI_2 iEff_equivI.
        iRewrite - ("Hlookup'" $! v' Φ'') in "Hσ'". iFrame.
        destruct σ2.1; simpl; last iIntros "!#"; 
        iIntros (w) "HΦ'' % %Φ''' Hdeep"; iApply ("HPost" with "HΦ''"); iNext; by iApply "IH".
      * do 19 ewp_value_or_step.
        do 2 (iApply (ewp_if_false with "[]"); first by iApply handler_effect_propagated_cond).
        iApply (ewp_bind [AppRCtx _]); first done.
        iApply (ewpw_sub with "Hle"). do 2 iApply ewpw_unlft. rewrite /ewpw.
        ewp_pure_steps. rewrite lookup_insert_ne; last (intros H'; inv H'; tauto).
        rewrite /sem_row_cons row_tun_ins_eq_ne // lookup_insert_ne; first iFrame "#".
        2: { intros H. inv H; apply Hneg'; eauto. }
        iApply ewp_do_ms. destruct m; simpl.
        ** specialize (HOS eq_refl).
          iDestruct (os_row_mono_prot _ l' s' σ' with "Hlookup'") as "Hmono".
          iAssert (deep_handler_ls_2 E l1 σ1 l2 σ2 ρ OS Φ h1 h2 r ρ' Φ') with "[Hbr]" as "H".
          { rewrite deep_handler_ls_2_unfold /deep_handler_ls_2_pre. simpl. by iFrame "#∗". }
          iExists (λ v, Φ'' v ∗ deep_handler_ls_2 E l1 σ1 l2 σ2 ρ OS Φ h1 h2 r ρ' Φ')%I.
          iSplitL; [|iIntros "!# %w [HΦ'' Hdeep]"; iApply ("HPost" with "HΦ''"); iNext; by iApply "IH"].
          iExists v', l', s', σ'. iFrame "#∗". iSplit; [done|]. 
          iApply ("Hmono" with "[H] Hσ'"). iIntros (w) "$ //".
        ** iDestruct "Hbr" as "#Hbr".
           iExists Φ''. iSplitL "Hσ'".
           { iExists v', l', s', σ'. by iFrame "#∗". }
        iIntros (w) "!# HΦ''". iApply ("HPost" with "HΦ''").
        iNext. iApply "IH".
        rewrite deep_handler_ls_2_unfold /deep_handler_ls_2_pre. simpl. by iFrame "#∗". 
Qed.
     
End reasoning.
