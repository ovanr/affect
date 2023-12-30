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
From haffel.lang Require Import subst_map.
From haffel.logic Require Import iEff.
From haffel.logic Require Import sem_def.
From haffel.logic Require Import sem_sig.
From haffel.logic Require Import sem_row.

(* EWP wrapper *)
Definition ewpw `{!heapGS Σ} (E : coPset) (e : expr) (ρ : sem_row Σ) (Φ : val -d> iPropO Σ) : iPropO Σ := 
    (EWP e @ E <| ⟦ filter_os ρ ⟧ |> {| ⟦ ρ ⟧ |} {{ Φ }})%R%I.

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
  (ewpw E e%E ρ Φ)
  (at level 20, e, ρ, Φ at level 200,
   format "'[' 'EWPW'  e  '/' '[          ' @  E '<|' ρ '|' '>' {{  Φ  } } ']' ']'") : bi_scope.

(* Postcondition includes binder. *)
Notation "'EWPW' e @ E '<|' ρ '|' '>' {{ v , Φ } }" :=
  (ewpw E e%E ρ (λ v, Φ)%I)
  (at level 20, e, ρ, Φ at level 200,
   format "'[' 'EWPW'  e  '/' '[          ' @  E '<|' ρ '|' '>'  {{  v ,  Φ  } } ']' ']'") : bi_scope.

(* Mask is implicitly specified by ⊤. *)
Notation "'EWPW' e '<|' ρ '|' '>' {{ v , Φ } }" :=
  (ewpw ⊤ e%E ρ (λ v, Φ)%I)
  (at level 20, e, ρ, Φ at level 200,
   format "'[' 'EWPW'  e  '/' '[          ' '<|' ρ '|' '>' {{  v ,  Φ  } } ']' ']'") : bi_scope.

(* No binder and no mask. *)
Notation "'EWPW' e '<|' ρ '|' '>' {{ Φ } }" :=
  (ewpw ⊤ e%E ρ Φ%I)
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

  Lemma filter_os_nil :
    filter_os (⟨⟩ : sem_row Σ)%R = (⟨⟩ : sem_row Σ)%R.
  Proof.
    rewrite /filter_os.
    rewrite union_with_idemp; first done.
    intros ?? H. rewrite lookup_empty in H. inv H.
  Qed.

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

  Lemma ewp_mono_os E (ρ ρ' : sem_row Σ) e Φ Φ' `{! OSRow ρ } `{! OSRow ρ' } :
    EWP e @ E <| ⟦ ρ ⟧%R |> {| ⟦ ρ' ⟧%R |} {{ v, Φ v }} -∗
    (∀ v : val, Φ v ={E}=∗ Φ' v) -∗ EWP e @ E <| ⟦ ρ ⟧%R |> {| ⟦ ρ' ⟧%R |} {{ v, Φ' v }}.
  Proof.
    iIntros "Hewp Himp". 
    iLöb as "IH" forall (e).
    rewrite !ewp_unfold /ewp_pre.
    destruct (to_val e) eqn:?.
    { iMod "Hewp" as "Hewp". by iApply "Himp". }
    destruct (to_eff e) eqn:?.
    - simpl. destruct p eqn:?, p0 eqn:?, m;
      iDestruct "Hewp" as "(%Φ'' & HΨ & Hps)";
      iExists (λ w, Φ'' w ∗ (∀ v, Φ v ={E}=∗ Φ' v)%I)%I;
      iSplitL "HΨ Himp".
      2, 4: try (iDestruct "Hps" as "#Hps"; iModIntro);
            iIntros "% (HΦ'' & Himp)"; 
            iSpecialize ("Hps" with "HΦ''"); iNext;
            iApply ("IH" with "Hps Himp").
      + destruct OSRow0 as [];
        iApply (monotonic_prot with "[Himp] HΨ"); iIntros "% $ {$Himp}".
      + destruct OSRow1 as [];
        iApply (monotonic_prot with "[Himp] HΨ"); iIntros "% $ {$Himp}".
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
  
  Lemma ewpw_mono_os E ρ e Φ Φ' `{! OSRow ρ} :
    EWPW e @ E <| ρ |> {{ Φ }} -∗
    (∀ v : val, Φ v ={E}=∗ Φ' v) -∗ 
    EWPW e @E <| ρ |> {{ Φ' }}. 
  Proof.
    iIntros "Hewp HΦ". rewrite /ewpw.
    assert (OSRow (filter_os ρ)).
    { by apply sem_row_filter_os. }
    iApply (@ewp_mono_os _ (filter_os ρ) ρ e Φ Φ' H _ with "Hewp HΦ").
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
  
  Lemma ewpw_bind k `{NeutralEctx k} E ρ e e' Φ  :
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

  Definition shallow_handler_wrp
  (E : coPset)
  (ρ : sem_row Σ)
  (Φ : val -d> iProp Σ)
  (h r : expr)
  (ρ' : sem_row Σ)
  (Φ' : val -d> iProp Σ) : iProp Σ :=
    shallow_handler E ⟦ filter_os ρ ⟧%R ⟦ ρ ⟧%R Φ h r
                      ⟦ filter_os ρ' ⟧%R ⟦ ρ' ⟧%R Φ'.

  
  Definition shallow_handler_wrp_os
    (E : coPset)
    (ρ : sem_row Σ)
    (Φ : val -d> iPropO Σ)
    (h r : expr)
    (ρ' : sem_row Σ)
    (Φ' : val -d> iPropO Σ) : iProp Σ :=

    (* Correctness of the return branch. *)
    (∀ (y : val), Φ y -∗ EWPW r y @ E <| ρ' |> {{ Φ' }}) ∧

    (* Correctness of the effect branch. *)
    (∀ (v k : val),
       iEff_car (upcl OS ⟦ ρ ⟧%R) v (λ w, EWPW k w @ E <| ρ |> {{ Φ }}) -∗
         EWPW h v k @ E <| ρ' |> {{ Φ' }}).

  Lemma iEff_le_upcl_ms_os (Ψ : iEff Σ) :
    ⊢ iEff_le (upcl MS Ψ) (upcl OS Ψ).
  Proof.
    iIntros (v Φ) "!# HMSΨ". rewrite /upcl /=.
    iDestruct "HMSΨ" as "(%Φ' & HΨΦ' & #HPost)".
    iExists Φ'. iFrame "#∗".
  Qed.
  
  Lemma shallow_handler_wrp_os_impl E ρ Φ h r ρ' Φ' :
    shallow_handler_wrp_os E ρ Φ h r ρ' Φ' -∗
    shallow_handler_wrp E ρ Φ h r ρ' Φ'.
  Proof.
    iIntros "H". rewrite /shallow_handler_wrp_os /shallow_handler_wrp /ewpw.
    rewrite /shallow_handler. repeat iSplit.
    - iDestruct "H" as "[H _]". iApply "H".
    - iDestruct "H" as "[_ H]"; iIntros (v k) "Hρ"; iApply "H". 
      iApply iEff_le_upcl; last done.
      iApply row_le_iEff. iApply row_le_filter_os_elim.
    - iDestruct "H" as "[_ H]"; iIntros (v k) "Hρ"; iApply "H".
      by iApply iEff_le_upcl_ms_os.
  Qed.

  Lemma ewpw_try_with E ρ Φ ρ' Φ' e h r :
    EWPW e @ E <| ρ |> {{ Φ }} -∗
      shallow_handler_wrp E ρ Φ h r ρ' Φ' -∗
        EWPW (TryWith e h r) @ E <| ρ' |> {{ Φ' }}.
  Proof.
    iIntros "Hewp H". rewrite /shallow_handler_wrp /ewpw. 
    iApply (ewp_try_with with "Hewp"); iApply "H".
  Qed.

  Definition deep_handler_wrp
  (E : coPset)
  (ρ : sem_row Σ)
  (Φ : val -d> iProp Σ)
  (h r : expr)
  (ρ' : sem_row Σ)
  (Φ' : val -d> iProp Σ) : iProp Σ :=
    deep_handler E ⟦ filter_os ρ ⟧%R ⟦ ρ ⟧%R Φ h r
                   ⟦ filter_os ρ' ⟧%R ⟦ ρ' ⟧%R Φ'.

  Definition deep_handler_wrp_os
    (E : coPset)
    (ρ : sem_row Σ)
    (Φ : val -d> iPropO Σ)
    (h r : expr)
    (ρ' : sem_row Σ)
    (Φ' : val -d> iPropO Σ) : iProp Σ :=

    (* Correctness of the return branch. *)
    (∀ (y : val), Φ y -∗ EWPW r y @ E <| ρ' |> {{ Φ' }}) ∧

    (* Correctness of the effect branch. *)
    (∀ (v k : val),
       iEff_car (upcl OS ⟦ ρ ⟧%R) v (λ w, ∀ Ψ' Ψ'' Φ'',
          ▷ deep_handler E ⟦ filter_os ρ ⟧%R ⟦ ρ ⟧%R Φ h r Ψ' Ψ'' Φ'' -∗
          EWP k w @ E <| Ψ' |> {| Ψ'' |} {{ Φ'' }}) -∗
         EWPW h v k @ E <| ρ' |> {{ Φ' }}).

  Lemma deep_handler_wrp_os_impl E ρ Φ h r ρ' Φ' :
    deep_handler_wrp_os E ρ Φ h r ρ' Φ' -∗
    deep_handler_wrp E ρ Φ h r ρ' Φ'.
  Proof.
    iIntros "H". rewrite /deep_handler_wrp_os /deep_handler_wrp /ewpw.
    rewrite deep_handler_unfold. repeat iSplit.
    - iDestruct "H" as "[H _]"; iApply "H".
    - iDestruct "H" as "[_ H]"; iIntros (v k) "Hρ".
      iApply "H". iApply iEff_le_upcl; last done.
      iApply row_le_iEff. iApply row_le_filter_os_elim.
    - iDestruct "H" as "[_ H]". iIntros (v k) "H'".
      iApply "H". by iApply iEff_le_upcl_ms_os. 
  Qed.

  Lemma ewpw_deep_try_with E ρ Φ (h r : val) ρ' Φ' e :
    EWPW e @ E <| ρ |> {{ Φ }} -∗
      deep_handler_wrp E ρ Φ h r ρ' Φ' -∗
        EWPW DeepTryWithV e h r @ E <| ρ' |> {{ Φ' }}.
  Proof.
    iIntros "Hewp H". rewrite /deep_handler_wrp /ewpw. 
    iApply (ewp_deep_try_with with "Hewp"); iApply "H".
  Qed.

End reasoning.
