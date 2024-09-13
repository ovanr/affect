(* ewpw.v *)

From iris.proofmode Require Import base tactics.
From iris.algebra Require Import ofe gmap.
From iris.base_logic Require Export iprop upred invariants.

From hazel.program_logic Require Import protocols.

(* Local imports *)
From affect.lib Require Import pure_weakestpre.
From affect.lib Require Import logic.
From affect.lang Require Import affect.
From affect.logic Require Import sem_def.
From affect.logic Require Import mode.
From affect.logic Require Import sem_sig.
From affect.logic Require Import sem_row.

(* EWP wrapper *)
Definition ewpw `{!heapGS Σ} (E : coPset) (e : expr) (ρ : sem_row Σ) (Φ : val -d> iPropO Σ) : iPropO Σ := 
    (EWP e @ E <| ⊥ |> {| ρ%R |} {{ Φ }})%R%I.

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

Lemma ewpw_mask_mono e E1 E2 Φ :
  E1 ⊆ E2 → EWPW e @ E1 {{ Φ }} -∗ EWPW e @ E2 {{ Φ }}.
Proof. apply ewp_mask_mono. Qed.

Lemma pwp_ewp e E Ψ1 Ψ2 Φ : PWP e [{ Φ }] -∗ EWP e @ E <| Ψ1 |> {| Ψ2 |} {{ Φ }}.
Proof.
  iIntros "H". iApply (ewp_mask_mono ∅); first set_solver.
  clear E. iRevert (e) "H". iApply pwp_ind.
  iIntros "!>" (e) "IH". rewrite !ewp_unfold /pwp_pre /ewp_pre /=.
  destruct (to_val e) as [v|] eqn:?; [done|].
  destruct (to_eff _) as [[[m v] k]|] eqn:?.
  - destruct e; simplify_eq/=.
    iDestruct ("IH" $! (Build_state ∅))
      as ((?&?&[]&Hstep)) "_"; simplify_eq/=; last done.
    destruct Hstep as [[|[]?] ???? Hstep]; simplify_eq/=; by inversion Hstep.
  - iIntros (σ1 _ κs _ _) "Hs". iDestruct ("IH" $! σ1) as "[% IH]".
    iModIntro. iSplit; [by auto using reducible_no_obs_reducible|].
    iIntros (e2 σ2 Hstep) "_ !> !> !> !>".
    iDestruct ("IH" with "[//]") as (???) "[$ _] /="; by simplify_eq/=.
Qed.

Lemma pwp_ewpw e E ρ Φ : PWP e [{ Φ }] -∗ EWPW e @E <| ρ |> {{ Φ }}.
Proof. apply pwp_ewp. Qed.

Lemma pwp_pure_step' e e' Φ :
  pure_prim_step e e' → 
  PWP e' [{ Φ }] -∗ PWP e [{ Φ }]. 
Proof.
  iIntros ([? Hstep]) "Hwp". iApply (pwp_pure_step _ _ _ True 1 with "Hwp"); last done.
  intros _. apply nsteps_once. split; simpl.
  - intros. eexists _, _, []; simpl; auto.
  - intros ? [] ?? [] ?; naive_solver.
Qed.

Lemma ewpw_value (E : coPset) ρ Φ (v : val) :
  Φ v -∗ EWPW v @E <| ρ |> {{ Φ }}.
Proof.
  iIntros "HΦ". rewrite /ewpw. by iApply ewp_value. 
Qed.

Lemma ewpw_bot E e Φ :
  EWP e @ E {{ v, Φ v }} -∗
  EWPW e @ E {{ Φ }}.
Proof. iIntros "$". Qed.

Lemma ewpw_bot_inv e E Φ :
  EWPW e @ E {{ Φ }} -∗
  EWP e @ E {{ v, Φ v }}.
Proof. iIntros "$". Qed.

Lemma ewpw_sub E e ρ ρ' Φ :
  ρ ≤ᵣ ρ' -∗ 
  EWPW e @E <| ρ |> {{ Φ }} -∗ EWPW e @E <| ρ' |> {{ Φ }}. 
Proof.
  iIntros "#Hρρ' Hewp". rewrite /ewpw.
  iApply (ewp_ms_prot_mono with "Hρρ' Hewp").
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

Lemma ewpw_mono_os E (ρ : sem_row Σ) e Φ Φ' `{! OnceR ρ } :
  EWPW e @ E <| ρ |> {{ Φ }} -∗
  (∀ v : val, Φ v ={E}=∗ Φ' v) -∗ 
  EWPW e @E <| ρ |> {{ Φ' }}. 
Proof.
  iIntros "Hewp HΦ". rewrite /ewpw.
  iApply (@ewp_mono_os _ ⊥ ρ e Φ Φ' _ with "Hewp HΦ").
Qed.

Lemma ewpw_mono E ρ e Φ Φ' :
  EWPW e @E <| ρ |> {{ Φ }} -∗
  □ (∀ v : val, Φ v ={E}=∗ Φ' v) -∗ 
  EWPW e @E <| ρ |> {{ Φ' }}.
Proof.
  iIntros "Hewp HΦ". rewrite /ewpw. 
  iApply (ewp_pers_mono with "Hewp HΦ").
Qed.

Lemma ewp_mono_on_prop E (Ψ Ψ' : iEff Σ) e (P : iProp Σ) Φ :
  mono_prot_on_prop Ψ' P -∗ P -∗
  EWP e @ E <| Ψ |> {| Ψ' |} {{ v, Φ v }} -∗
  EWP e @ E <| Ψ |> {| Ψ' |} {{ v, Φ v ∗ P }}.
Proof.
  iIntros "#Hmono HP Hewp".
  iLöb as "IH" forall (e).
  rewrite !ewp_unfold /ewp_pre.
  destruct (to_val e) eqn:?.
  { iMod "Hewp" as "Hewp". iModIntro. iFrame. }
  destruct (to_eff e) eqn:?.
  - simpl. destruct p eqn:?, p0 eqn:?, m;
    iDestruct "Hewp" as "(%Φ'' & HΨ & Hps)".
    + iExists Φ''. iFrame.
      iIntros (?) "HΦ''". iSpecialize ("Hps" $! w with "HΦ''").
      iNext. iApply ("IH" with "HP Hps").
    + iExists (λ w, Φ'' w ∗ P)%I; iSplitL "HΨ HP".
      { iApply ("Hmono" with "HΨ HP"). }
      try (iDestruct "Hps" as "#Hps"; iModIntro).
      iIntros "% (HΦ'' & HP)". 
      iSpecialize ("Hps" with "HΦ''"); iNext;
      iApply ("IH" with "HP Hps").
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
      iApply ("IH" with "HP He₂" ). }
    iMod "Hpost" as "Hpost". iModIntro. iNext.
    iMod "Hpost" as "Hpost". iClear "IH".
    iMod ("IH'" with "HP Hpost") as "IH".
    do 2 iModIntro. iNext. iApply "IH".
Qed.

Corollary ewp_row_type_sub E (ρ ρ' : sem_row Σ) τ e Φ w `{ ρ' ᵣ⪯ₜ τ } :
  EWP e @ E <| ρ |> {| ρ' |} {{ v, Φ v }} -∗ τ w -∗
  EWP e @ E <| ρ |> {| ρ' |} {{ v, Φ v ∗ τ w }}.
Proof.
  iIntros "Hewp Hτ". 
  iApply (ewp_mono_on_prop with "[] Hτ Hewp").
  inv H. iApply row_type_sub.
Qed.

Corollary ewp_row_env_sub E (ρ ρ' : sem_row Σ) Γ e Φ γ `{ ρ' ᵣ⪯ₑ Γ } :
  EWP e @ E <| ρ |> {| ρ' |} {{ v, Φ v }} -∗ Γ ⊨ₑ γ -∗
  EWP e @ E <| ρ |> {| ρ' |} {{ v, Φ v ∗ Γ ⊨ₑ γ }}.
Proof.
  iIntros "Hewp HΓ". 
  iApply (ewp_mono_on_prop with "[] HΓ Hewp").
  inv H. iApply row_env_sub.
Qed.

Lemma ewpw_row_type_sub E ρ τ e Φ w `{ ρ ᵣ⪯ₜ τ } :
  EWPW e @ E <| ρ |> {{ Φ }} -∗ τ w -∗
  EWPW e @E <| ρ |> {{ v, Φ v ∗ τ w }}. 
Proof.
  iIntros "Hewp Hτ". rewrite /ewpw.
  iPoseProof (@ewp_row_type_sub E ⊥ ρ τ e Φ w with "[Hewp] Hτ") as "H".
  { iApply ewp_os_prot_mono; first iApply iEff_le_bottom. iApply "Hewp". }
  iApply "H".
Qed.

Lemma ewpw_row_env_sub E ρ Γ e Φ γ `{ ρ ᵣ⪯ₑ Γ } :
  EWPW e @ E <| ρ |> {{ Φ }} -∗ Γ ⊨ₑ γ -∗
  EWPW e @E <| ρ |> {{ v, Φ v ∗ Γ ⊨ₑ γ }}. 
Proof.
  iIntros "Hewp HΓ". rewrite /ewpw.
  iPoseProof (@ewp_row_env_sub E ⊥ ρ Γ e Φ γ with "[Hewp] HΓ") as "H".
  { iApply ewp_os_prot_mono; first iApply iEff_le_bottom. iApply "Hewp". }
  iApply "H".
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

Lemma ewpw_do_ms E op v (ρ : sem_row Σ) Φ :
  iEff_car ρ (effect op, v)%V Φ -∗ 
  EWPW (doₘ: (effect op, v)%V) @ E <| ρ |> {{ Φ }}.
Proof.
  iIntros "Hρ".
  rewrite /ewpw /=. 
  iApply ewp_do_ms;
  simpl; iExists Φ; iFrame; iIntros "!# % $".
Qed.

Lemma ewp_assert E Φ:
  ▷ Φ #() -∗ EWP (assert: #true) @E {{ Φ }}.
Proof. iIntros "HΦ". rewrite /assert. by ewp_pure_steps. Qed.

Lemma ewpw_assert E Φ:
  ▷ Φ #() -∗ EWPW (assert: #true) @E {{ Φ }}.
Proof. iIntros "H". iApply ewpw_bot. by iApply ewp_assert. Qed.

Lemma handler_effect_propagated_cond E op op' s' Ψ :
 ¬ (op = op' ∧ s' = 0) →
 ⊢ EWP if: (effect op') = (effect op)%V then #s' = #0 else #false @ E <| Ψ |> {{ v, ⌜v = #false⌝ }}.
Proof.
  intros Hneg. rewrite not_and_l in Hneg. iIntros.
  destruct (decide (op = op')) as [->|], Hneg; ewp_pure_steps'. 
  iPureIntro. rewrite bool_decide_false //. 
  intros H'. simplify_eq. assert (s' = 0) by lia. simplify_eq. 
Qed.

Definition shandler_spec
  (E : coPset)
  (op : operation)
  (σ : sem_sig Σ)
  (ρ : sem_row Σ)
  (mh : mode)
  (Φ : val -d> iPropO Σ)
  (h r : expr)
  (ρ'  : sem_row Σ)
  (Φ' : val -d> iPropO Σ) : iProp Σ := (
  (* Subsumption on row *)
  (ρ ≤ᵣ ρ') ∗

  ∃ P, mono_prot_on_prop ρ P ∗ P ∗
  □  (P -∗
  (* Correctness of the return branch. *)
  (∀ (v : val), Φ v -∗ EWPW r v @ E <| ρ' |> {{ Φ' }}) ∧
  (* Correctness of the effect branch. *)
  (∀ (v k : val),
     iEff_car (upcl mh σ) v (λ w, EWPW k w @ E <| (op, σ) · ρ |> {{ Φ }}) -∗
       EWPW h v k @ E <| ρ' |> {{ Φ' }})
  ))%I.

Lemma ewpw_shandler E (op : operation) mh σ ρ ρ' e (h r : val) Φ Φ' :
  EWPW e @ E <| (op, σ) · ρ |> {{ Φ }} -∗
  shandler_spec E op σ ρ mh Φ h r ρ' Φ' -∗
  EWPW (SHandlerV mh e op h r) @E <| ρ' |> {{ Φ' }}.
Proof.
  iIntros "He [#Hle (%P & #Hmono & HP & #Hbr)]". rewrite /SHandlerV /ewpw. 
  iLöb as "IH" forall (e). rewrite {2} /shandler. ewp_pure_steps.
  iApply (ewp_try_with with "[He]").
  { ewp_pure_steps. iApply "He". }
  iSplit; last iSplit.
  - iDestruct ("Hbr" with "HP") as "[$ _]".
  - iIntros (??) "_ (% & [] & _)".
  - iIntros (v k) "(% & ->) Hρ".
    ewp_pure_steps. 
    iDestruct "Hρ" as "(%Φ'' & (%op' & %v' & -> & H) & #HPost)".
    destruct (decide (op = op')) as [<-|].
    + ewp_pure_steps'. iSpecialize ("Hbr" with "HP").
      destruct mh; simpl.
      ++ iApply (ewp_bind [AppRCtx _; AppRCtx _]); first done. 
         iApply ewp_alloc. iIntros "!> %l Hl !> /=". ewp_pure_steps.
         iApply "Hbr". iExists Φ''. iFrame.
         iIntros (w) "Φ''". rewrite /ewpw. ewp_pure_steps. 
         iApply (ewp_bind [AppRCtx _; AppRCtx _]); first done.
         iApply (ewp_load with "Hl"). iIntros "!> Hl !> /=".
         iApply (ewp_bind [AppRCtx _]); first done.
         iApply ewp_ms_prot_mono; first iApply iEff_le_bottom.
         iApply ewp_assert. iIntros "!> /=". ewp_pure_steps.
         iApply (ewp_bind [AppRCtx _]); first done.
         iApply (ewp_store with "Hl"). iIntros "!> _ !> /=".
         do 3 ewp_value_or_step. by iApply "HPost".
      ++ iApply "Hbr". iExists Φ''. iFrame.
         iIntros "!# %w Φ''". rewrite /ewpw. by iApply "HPost".
    + do 11 ewp_value_or_step; first done. rewrite bool_decide_false; last (intros ?; simplify_eq).
      ewp_pure_steps. iApply (ewpw_sub with "Hle"). 
      iApply ewp_do_ms. 
      iExists (λ v, Φ'' v ∗ P)%I. 
      iSplitL; first (iApply ("Hmono" with "H HP")).
      simpl. iIntros "!# %w [HΦ'' H]"; do 5 ewp_value_or_step. 
      iSpecialize ("HPost" with "HΦ''"); iApply ("IH" with "HPost H").
Qed.

Notation handler_spec_type Σ :=
  (coPset -d> sem_sig Σ -d> sem_row Σ -d> mode -d> (val -d> iPropO Σ) 
          -d> expr -d> expr
          -d> sem_row Σ -d> (val -d> iPropO Σ) -d> iPropO Σ) (only parsing).

Definition handler_spec `{irisGS eff_lang Σ} : handler_spec_type Σ := (
  λ E σ ρ mh Φ h r ρ' Φ',
  (* Subsumption on row *)
  (ρ ≤ᵣ ρ') ∗

  □ (
  (* Correctness of the return branch. *)
    (∀ (v : val), Φ v -∗ EWPW r v @ E <| ρ' |> {{ Φ' }}) ∧

  (* Correctness of the effect branch. *)
    (∀ (v k : val),
       iEff_car (upcl mh σ) v (λ w, EWPW k w @ E <| ρ' |> {{ Φ' }}) -∗
         EWPW h v k @ E <| ρ' |> {{ Φ' }}))
  )%I.

Lemma ewpw_handler E (op : operation) mh σ ρ ρ' e (h r : val) Φ Φ' :
  EWPW e @ E <| (op, σ) · ρ |> {{ Φ }} -∗
  handler_spec E σ ρ mh Φ h r ρ' Φ' -∗
  EWPW (HandlerV mh e op h r) @E <| ρ' |> {{ Φ' }}.
Proof.
  iIntros "He H". rewrite /HandlerV /handler /ewpw. 
  ewp_pure_steps.
  iApply (ewp_deep_try_with with "[He]"). 
  { ewp_pure_steps. iApply "He". }
  iLöb as "IH" forall (ρ' Φ'). 
  iDestruct "H" as "(#Hle & #Hbr)". 
  rewrite deep_handler_unfold /deep_handler_pre.
  iSplit; last iSplit.
  - iDestruct "Hbr" as "[$ _]".
  - iIntros (??) "(% & [] & _)".
  - iIntros (v k) "Hρ". ewp_pure_steps. 
    iDestruct "Hρ" as "(%Φ'' & (%op' & %v' & -> & H) & #HPost)".
    destruct (decide (op = op')) as [->|Hneg].
    + ewp_pure_steps'. destruct mh; simpl.
      ++ iApply (ewp_bind [AppRCtx _; AppRCtx _]); first done. 
         iApply ewp_alloc. iIntros "!> %l Hl !> /=". ewp_pure_steps.
         iApply "Hbr". iExists Φ''. iFrame.
         iIntros (w) "HΦ''". rewrite /ewpw. ewp_pure_steps. 
         iApply (ewp_bind [AppRCtx _; AppRCtx _]); first done.
         iApply (ewp_load with "Hl"). iIntros "!> Hl !> /=".
         iApply (ewp_bind [AppRCtx _]); first done.
         iApply ewp_ms_prot_mono; first iApply iEff_le_bottom.
         iApply ewp_assert. iIntros "!> /=". ewp_pure_steps.
         iApply (ewp_bind [AppRCtx _]); first done.
         iApply (ewp_store with "Hl"). iIntros "!> _ !> /=".
         do 3 ewp_value_or_step. iApply ("HPost" with "HΦ''").
         iNext. iApply "IH". iFrame "#∗". iApply "Hbr".
      ++ iApply "Hbr". iExists Φ''. iFrame.
         iIntros "!# %w HΦ''". rewrite /ewpw. 
         iApply ("HPost" with "HΦ''").
         iNext. iApply "IH". iFrame "#∗". iApply "Hbr".
    + do 11 ewp_value_or_step; first done.
      rewrite bool_decide_false; last (intros ?; simplify_eq).
      ewp_pure_steps. iApply (ewpw_sub with "Hle").
      iApply ewp_do_ms.
      simpl. iDestruct "Hbr" as "#Hbr". iDestruct "HPost" as "#HPost".
      iExists Φ''. iSplitL "H"; first done.
      iIntros (w) "!# HΦ''". iApply ("HPost" with "HΦ''").
      iNext. iApply "IH". by iFrame "#∗".
Qed.

Notation handler2_spec_type Σ :=
  (coPset -d> operation -d> sem_sig Σ -d> operation -d> sem_sig Σ -d> sem_row Σ -d> mode -d> (val -d> iPropO Σ) 
          -d> expr  -d> expr -d> expr
          -d> sem_row Σ -d> (val -d> iPropO Σ) -d> iPropO Σ) (only parsing).

Definition handler2_spec `{irisGS eff_lang Σ} : handler2_spec_type Σ := (
  λ E op1 σ1 op2 σ2 ρ mh Φ h1 h2 r ρ' Φ',

  (* Subsumption on row *)
  (ρ ≤ᵣ ρ') ∗

  ⌜ op1 ≠ op2 ⌝ ∗

  □ (
  (* Correctness of the return branch. *)
    (∀ (v : val), Φ v -∗ EWPW r v @ E <| ρ' |> {{ Φ' }}) ∧

  (* Correctness of the effect branch 1. *)
    (∀ (v k : val),
       iEff_car (upcl mh σ1) v (λ w, EWPW k w @ E <| ρ' |> {{ Φ' }}) -∗
       EWPW h1 v k @ E <| ρ' |> {{ Φ' }}) ∧

  (* Correctness of the effect branch 2. *)
    (∀ (v k : val),
       iEff_car (upcl mh σ2) v (λ w, EWPW k w @ E <| ρ' |> {{ Φ' }}) -∗
       EWPW h2 v k @ E <| ρ' |> {{ Φ' }})
  ))%I.

Lemma ewpw_handler2 E (op1 op2 : operation) mh σ1 σ2 ρ ρ' e (h1 h2 r : val) Φ Φ' :
  EWPW e @ E <| (op1, σ1) · (op2, σ2) · ρ |> {{ Φ }} -∗
  handler2_spec E op1 σ1 op2 σ2 ρ mh Φ h1 h2 r ρ' Φ' -∗
  EWPW (Handler2V mh e op1 op2 h1 h2 r) @E <| ρ' |> {{ Φ' }}.
Proof.
  iIntros "He H". rewrite /Handler2V /handler2 /ewpw. 
  ewp_pure_steps.
  iApply (ewp_deep_try_with with "[He]").
  { ewp_pure_steps. iApply "He". }
  iLöb as "IH" forall (ρ' Φ').
  iDestruct "H" as "(#Hle & %Hneq & #Hbr)". 
  rewrite deep_handler_unfold /deep_handler_pre.
  iSplit; last iSplit.
  - iDestruct "Hbr" as "[$ _]".
  - iIntros (??) "(% & [] & _)".
  - iIntros (v k) "Hρ". ewp_pure_steps. 
    iDestruct "Hρ" as "(%Φ'' & (%op' & %v' & -> & H) & HPost)".
    destruct (decide (op1 = op')) as [->|].
    + ewp_pure_steps'. destruct mh; simpl.
      ++ iApply (ewp_bind [AppRCtx _; AppRCtx _]); first done. 
         iApply ewp_alloc. iIntros "!> %l Hl !> /=". ewp_pure_steps.
         iApply "Hbr". iExists Φ''. iFrame.
         iIntros (w) "HΦ''". rewrite /ewpw. ewp_pure_steps. 
         iApply (ewp_bind [AppRCtx _; AppRCtx _]); first done.
         iApply (ewp_load with "Hl"). iIntros "!> Hl !> /=".
         iApply (ewp_bind [AppRCtx _]); first done.
         iApply ewp_ms_prot_mono; first iApply iEff_le_bottom.
         iApply ewp_assert. iIntros "!> /=". ewp_pure_steps.
         iApply (ewp_bind [AppRCtx _]); first done.
         iApply (ewp_store with "Hl"). iIntros "!> _ !> /=".
         do 3 ewp_value_or_step. iApply ("HPost" with "HΦ''").
         iNext. iApply "IH". iSplit; last iSplit; by iFrame "#∗".
      ++ iDestruct "HPost" as "#HPost". iApply "Hbr". iExists Φ''. iFrame.
         iIntros "!# %w HΦ''". rewrite /ewpw. 
         iApply ("HPost" with "HΦ''"). 
         iNext. iApply "IH". iSplit; last iSplit; by iFrame "#∗".
    + iDestruct "H" as "(%op'' & %v'' & %Heq & H)".
      simplify_eq. destruct (decide (op2 = op'')) as [->|].
      ++ ewp_pure_steps'. iDestruct "HPost" as "#HPost".
         simplify_eq. destruct mh; simpl.
         +++ iApply (ewp_bind [AppRCtx _; AppRCtx _]); first done. 
             iApply ewp_alloc. iIntros "!> %l Hl !> /=". ewp_pure_steps.
             iApply "Hbr". iExists Φ''. iFrame.
             iIntros (w) "HΦ''". rewrite /ewpw. ewp_pure_steps. 
             iApply (ewp_bind [AppRCtx _; AppRCtx _]); first done.
             iApply (ewp_load with "Hl"). iIntros "!> Hl !> /=".
             iApply (ewp_bind [AppRCtx _]); first done.
             iApply ewp_ms_prot_mono; first iApply iEff_le_bottom.
             iApply ewp_assert. iIntros "!> /=". ewp_pure_steps.
             iApply (ewp_bind [AppRCtx _]); first done.
             iApply (ewp_store with "Hl"). iIntros "!> _ !> /=".
             do 3 ewp_value_or_step. iApply ("HPost" with "HΦ''").
             iNext. iApply "IH". iSplit; last iSplit; by iFrame "#∗".
         +++ iDestruct "HPost" as "#HPost". iApply "Hbr". iExists Φ''. iFrame.
             iIntros "!# %w HΦ''". rewrite /ewpw. 
             iApply ("HPost" with "HΦ''"). 
             iNext. iApply "IH". iSplit; last iSplit; by iFrame "#∗".
      ++ do 11 ewp_value_or_step; first done.
         rewrite bool_decide_false; last (intros ?; simplify_eq).
         do 3 ewp_value_or_step; first done.
         rewrite bool_decide_false; last (intros ?; simplify_eq).
         ewp_pure_steps. iApply (ewpw_sub with "Hle").
         iApply ewp_do_ms. iDestruct "HPost" as "#HPost".
         iDestruct "Hbr" as "#Hbr". iExists Φ''. iSplitL "H"; first iApply "H".
         simpl. iIntros (w) "!# HΦ''". iApply ("HPost" with "HΦ''"). 
         iNext. iApply "IH". iSplit; last iSplit; by iFrame "#∗".
Qed.

(** Deep handler spec as in Hazel with the addition of effect rows. *)

Notation deep_handler_spec_type Σ :=
  (coPset -d> sem_sig Σ -d> sem_row Σ -d> mode -d> mode -d> (val -d> iPropO Σ) 
          -d> expr -d> expr
          -d> sem_row Σ -d> (val -d> iPropO Σ) -d> iPropO Σ) (only parsing).

Definition deep_handler_spec_pre `{irisGS eff_lang Σ} : 
  deep_handler_spec_type Σ → deep_handler_spec_type Σ := (
  λ deep_handler_spec E σ ρ mh mρ Φ h r ρ' Φ',
  (* Subsumption on row *)
  (ρ ≤ᵣ ρ') ∗

  (* One-Shot Row *)
  (⌜ mρ = OS → OnceR ρ ⌝) ∗

  □?mρ (
  (* Correctness of the return branch. *)
    (∀ (v : val), Φ v -∗ EWPW r v @ E <| ρ' |> {{ Φ' }})
  ) ∧

  (* Correctness of the effect branch. *)
  □ (
  (∀ (v k : val),
     iEff_car (upcl mh σ) v (λ w, 
        ∀ ρ'' Φ'', 
          ▷ deep_handler_spec E σ ρ mh mρ Φ h r ρ'' Φ'' -∗
          EWPW k w @ E <| ρ'' |> {{ Φ'' }}
     ) -∗
       EWPW h v k @ E <| ρ' |> {{ Φ' }}))
  )%I.

Local Instance deep_handler_spec_pre_contractive `{irisGS eff_lang Σ} : Contractive deep_handler_spec_pre.
Proof.
  rewrite /deep_handler_spec_pre => n deep deep' Hne E σ ρ mh mρ Φ h r ρ' Φ'.
  repeat (f_contractive || f_equiv). intros ?; simpl.
  repeat (f_contractive || f_equiv); apply Hne.
Qed.
Definition deep_handler_spec `{irisGS eff_lang Σ} := fixpoint deep_handler_spec_pre.
Arguments deep_handler_spec _ _%S _%R _ _ _%E _%E _%R _%I.

Lemma deep_handler_spec_unfold `{irisGS eff_lang Σ} E σ ρ mh mρ Φ h r ρ' Φ' :
  deep_handler_spec E σ ρ mh mρ Φ h r ρ' Φ' ⊣⊢
    deep_handler_spec_pre deep_handler_spec E σ ρ mh mρ Φ h r ρ' Φ'.
Proof. by apply (fixpoint_unfold deep_handler_spec_pre). Qed.

Lemma ewpw_deep_handler E (op : operation) mh mρ σ ρ ρ' e (h r : val) Φ Φ' :
  EWPW e @ E <| (op, σ) · ρ |> {{ Φ }} -∗
  deep_handler_spec E σ ρ mh mρ Φ h r ρ' Φ' -∗
  EWPW (HandlerV mh e op h r) @E <| ρ' |> {{ Φ' }}.
Proof.
  iIntros "He H". rewrite /HandlerV /handler /ewpw. 
  ewp_pure_steps.
  iApply (ewp_deep_try_with with "[He]"). 
  { ewp_pure_steps. iApply "He". }
  iLöb as "IH" forall (ρ' Φ'). rewrite deep_handler_spec_unfold.
  iDestruct "H" as "(#Hle & %HOS & Hbr)". 
  rewrite deep_handler_unfold /deep_handler_pre.
  iSplit; last iSplit.
  - rewrite !bi.intuitionistically_if_elim. iDestruct "Hbr" as "[$ _]".
  - iIntros (??) "(% & [] & _)".
  - iIntros (v k) "Hρ". ewp_pure_steps. 
    iDestruct "Hρ" as "(%Φ'' & (%op' & %v' & %Heq' & Hσ') & #HPost)".
    inv Heq'. destruct (decide (op = op')) as [->|Hneg].
    + ewp_pure_steps'. 
      rewrite !bi.intuitionistically_if_elim. 
      destruct mh; simpl.
      ++ iApply (ewp_bind [AppRCtx _; AppRCtx _]); first done. 
         iApply ewp_alloc. iIntros "!> %l Hl !> /=". ewp_pure_steps.
         iApply "Hbr". iExists Φ''. iFrame.
         iIntros (w) "HΦ'' %% Hspec". rewrite /ewpw. ewp_pure_steps. 
         iApply (ewp_bind [AppRCtx _; AppRCtx _]); first done.
         iApply (ewp_load with "Hl"). iIntros "!> Hl !> /=".
         iApply (ewp_bind [AppRCtx _]); first done.
         iApply ewp_ms_prot_mono; first iApply iEff_le_bottom.
         iApply ewp_assert. iIntros "!> /=". ewp_pure_steps.
         iApply (ewp_bind [AppRCtx _]); first done.
         iApply (ewp_store with "Hl"). iIntros "!> _ !> /=".
         do 3 ewp_value_or_step. iApply ("HPost" with "HΦ''").
         iNext. iApply ("IH" with "Hspec"). 
      ++ iApply "Hbr". iExists Φ''. iFrame.
         iIntros "!# %w HΦ''". rewrite /ewpw. 
         iIntros (ρ'' Φ''') "Hdeep". ewp_pure_steps.
         iApply ("HPost" with "HΦ''").
         iNext. iApply ("IH" with "Hdeep"). 
    + do 11 ewp_value_or_step; first done.
      rewrite bool_decide_false; last (intros ?; simplify_eq).
      ewp_pure_steps. iApply (ewpw_sub with "Hle").
      iApply ewp_do_ms. destruct mρ. simpl.
      * specialize (HOS eq_refl).
         iAssert (deep_handler_spec E σ ρ mh OS Φ h r ρ' Φ') with "[Hbr]" as "H".
         { rewrite deep_handler_spec_unfold /deep_handler_spec_pre. simpl. by iFrame "#∗". }
         iExists (λ v, Φ'' v ∗ deep_handler_spec E σ ρ _ OS Φ h r ρ' Φ')%I.
         iSplitL; [|iIntros "!# %w [HΦ'' Hdeep]"; iApply ("HPost" with "HΦ''"); iNext; by iApply "IH"].
         iApply (monotonic_prot _ _ with "[H] Hσ'").
         iIntros "% $ //". 
      * simpl.
        iDestruct "Hbr" as "#Hbr". iDestruct "HPost" as "#HPost".
        iExists Φ''. iSplitL "Hσ'"; first iApply "Hσ'".
        iIntros (w) "!# HΦ''". iApply ("HPost" with "HΦ''").
        iNext. iApply "IH".
        rewrite deep_handler_spec_unfold /deep_handler_spec_pre. simpl. by iFrame "#∗". 
Qed.

End reasoning.
