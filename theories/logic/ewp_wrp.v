(* ewp_wrp.v *)

From iris.proofmode Require Import base tactics.
From iris.algebra Require Import ofe list.
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
From haffel.lang Require Import hazel.
From haffel.lang Require Import subst_map.
From haffel.logic Require Import iEff.
From haffel.logic Require Import sem_def.
From haffel.logic Require Import sem_sig.

(* EWP wrapper *)
Definition ewp_wrp `{!heapGS Σ} (E : coPset) (e : expr) (σ : sem_sig Σ) (Φ : val -d> iPropO Σ) : iPropO Σ := 
  (match σ.1 with
    OS => EWP e @ E <| σ.2 |> {| σ.2 |} {{ Φ }}
  | MS => EWP e @ E <| ⊥ |>   {| σ.2 |} {{ Φ }}
  end)%I.

Global Opaque env_dom.

Notation "'EWPW' e @ E {{ Φ } }" :=
  (ewp_wrp E e%E ⊥ Φ)
  (at level 20, e, Φ at level 200,
   format "'[' 'EWPW'  e  '/' '[          ' @  E  {{  Φ  } } ']' ']'") : bi_scope.

(* Postcondition includes binder. *)
Notation "'EWPW' e @ E {{ v , Φ } }" :=
  (ewp_wrp E e%E ⊥ (λ v, Φ)%I)
  (at level 20, e, Φ at level 200,
   format "'[' 'EWPW'  e  '/' '[          ' @  E  {{  v ,  Φ  } } ']' ']'") : bi_scope.

(* Mask is implicitly specified by ⊤. *)
Notation "'EWPW' e {{ v , Φ } }" :=
  (ewp_wrp ⊤ e%E ⊥ (λ v, Φ)%I)
  (at level 20, e, Φ at level 200,
   format "'[' 'EWPW'  e  '/' '[          ' {{  v ,  Φ  } } ']' ']'") : bi_scope.

(* No binder and no mask. *)
Notation "'EWPW' e {{ Φ } }" :=
  (ewp_def ⊤ e%E ⊥ Φ%I)
  (at level 20, e, Φ at level 200,
   format "'[' 'EWPW'  e  '/' '[          ' {{  Φ  } } ']' ']'") : bi_scope.

Notation "'EWPW' e @ E '<|' σ '|' '>' {{ Φ } }" :=
  (ewp_wrp E e%E σ Φ)
  (at level 20, e, σ, Φ at level 200,
   format "'[' 'EWPW'  e  '/' '[          ' @  E '<|' σ '|' '>' {{  Φ  } } ']' ']'") : bi_scope.

(* Postcondition includes binder. *)
Notation "'EWPW' e @ E '<|' σ '|' '>' {{ v , Φ } }" :=
  (ewp_wrp E e%E σ (λ v, Φ)%I)
  (at level 20, e, σ, Φ at level 200,
   format "'[' 'EWPW'  e  '/' '[          ' @  E '<|' σ '|' '>'  {{  v ,  Φ  } } ']' ']'") : bi_scope.

(* Mask is implicitly specified by ⊤. *)
Notation "'EWPW' e '<|' σ '|' '>' {{ v , Φ } }" :=
  (ewp_wrp ⊤ e%E σ (λ v, Φ)%I)
  (at level 20, e, σ, Φ at level 200,
   format "'[' 'EWPW'  e  '/' '[          ' '<|' σ '|' '>' {{  v ,  Φ  } } ']' ']'") : bi_scope.

(* No binder and no mask. *)
Notation "'EWPW' e '<|' σ '|' '>' {{ Φ } }" :=
  (ewp_wrp ⊤ e%E σ Φ%I)
  (at level 20, e, σ, Φ at level 200,
   format "'[' 'EWPW'  e  '/' '[          ' '<|' σ '|' '>' {{  Φ  } } ']' ']'") : bi_scope.

Global Instance ewp_wrp_ne `{!heapGS Σ} E e σ : 
  NonExpansive (ewp_wrp E e σ).
Proof.
  rewrite /ewp_wrp. intros ????. by repeat f_equiv.
Qed.

Global Instance ewp_wrp_contractive `{!heapGS Σ} E e σ : 
  TCEq (to_val e) None →
  TCEq (to_eff e) None →
  Contractive (ewp_wrp E e σ).
Proof.
  rewrite /ewp_wrp. intros ??????. 
  f_equiv; by f_contractive. 
Qed.

Definition is_os `{!heapGS Σ} (σ : sem_sig Σ) := (
    (σ ≤S ⊥) ∨ 
      (∃ τ κ, ⌜ NonExpansive2 τ ⌝ ∗ ⌜ NonExpansive2 κ ⌝ ∗
              (σ ≤S (μ∀TS: θ, α, τ θ α ⇒ κ θ α | OS)%S) ∗ 
              ((μ∀TS: θ, α, τ θ α ⇒ κ θ α | OS)%S ≤S σ))
)%I. 

Section reasoning.

  Context `{!heapGS Σ}. 

  Lemma bot_is_os : ⊢ is_os ⊥.
  Proof. iLeft. iApply sig_le_refl. Qed.
  
  Lemma os_is_os A B `{ NonExpansive2 A, NonExpansive2 B} : 
    ⊢ is_os (μ∀TS: θ, α, A θ α ⇒ B θ α | OS)%S.
  Proof. 
    iRight. iExists A, B. 
    do 2 (iSplit; first done).
    iSplit; iApply sig_le_refl. 
  Qed.
  
  Lemma ewpw_ewp_eq E e σ (Φ : val -d> iProp Σ) :
    (EWPW e @ E <| σ |> {{ Φ }})%I = (EWP e @E <| match σ.1 with OS => σ.2 | MS => ⊥ end |> {| σ.2 |} {{ Φ }})%I.
  Proof. rewrite /ewp_wrp. by destruct σ.1. Qed.

  Lemma ewp_wrp_value (E : coPset) σ Φ (v : val) :
    Φ v -∗ EWPW v @E <| σ |> {{ Φ }}.
  Proof.
    iIntros "HΦ". rewrite /ewp_wrp. destruct σ.1; by iApply ewp_value. 
  Qed.
  
  Lemma ewp_wrp_bot E e Φ :
    EWP e @ E {{ v, Φ v }} -∗
    EWPW e @ E {{ Φ }}.
  Proof. iIntros "Hewp". by rewrite /ewp_wrp. Qed.
  
  Lemma ewp_wrp_bot_inv e E Φ :
    EWPW e @ E {{ Φ }} -∗
    EWP e @ E {{ v, Φ v }}.
  Proof. by iIntros "Hewp". Qed.
  
  Lemma ewp_sem_os_sig_le_sub E σ σ' e Φ :
    σ ≤S σ' -∗
    EWP e @ E <| σ.2 |> {| σ.2 |} {{ v, Φ v }} -∗
    EWP e @ E <| σ'.2 |> {| σ'.2 |} {{ v, Φ v }}.
  Proof.
    iIntros "[#Hbot|[#Hmle #Hple]] Hewp".
    - iApply ewp_ms_prot_mono; first iApply iEff_le_bottom.
      iApply ewp_os_prot_mono; first iApply iEff_le_bottom.
      iDestruct (ewp_ms_prot_mono with "Hbot Hewp") as "Hewp".
      by iDestruct (ewp_os_prot_mono with "Hbot Hewp") as "Hewp".
    - iApply ewp_ms_prot_mono; first iApply "Hple".
      by iApply ewp_os_prot_mono; first iApply "Hple".
  Qed.
  
  Lemma ewp_sem_ms_sig_le_sub E σ σ' e Φ :
    σ ≤S σ' -∗
    EWP e @ E <| ⊥ |> {| σ.2 |} {{ v, Φ v }} -∗
    EWP e @ E <| ⊥ |> {| σ'.2 |} {{ v, Φ v }}.
  Proof.
    iIntros "[#Hbot|[#Hmle #Hple]] Hewp".
    - iApply ewp_ms_prot_mono; first iApply iEff_le_bottom.
      by iDestruct (ewp_ms_prot_mono with "Hbot Hewp") as "Hewp".
    - by iApply ewp_ms_prot_mono; first iApply "Hple".
  Qed.
  
  Lemma ewp_wrp_sub E e σ σ' Φ :
    σ ≤S σ' -∗ 
    EWPW e @E <| σ |> {{ Φ }} -∗ EWPW e @E <| σ' |> {{ Φ }}. 
  Proof.
    iIntros "#Hσσ' Hewp". 
    iDestruct "Hσσ'" as "[Hbot|[Hmle Hple]]".
    - rewrite /ewp_wrp; destruct σ.1,σ'.1;
      (iApply ewp_ms_prot_mono; first iApply iEff_le_bottom);
      (iApply ewp_os_prot_mono; first iApply iEff_le_bottom);
      iDestruct (ewp_ms_prot_mono with "Hbot Hewp") as "Hewp";
      by try iDestruct (ewp_os_prot_mono with "Hbot Hewp") as "Hewp".
    - rewrite /ewp_wrp. destruct σ.1 eqn:H1, σ'.1 eqn:H2; 
      rewrite /mode_le /mode_le_prop; eauto.
      + iApply ewp_ms_prot_mono; first iApply "Hple".
        by iApply ewp_os_prot_mono; first iApply "Hple".
      + iApply ewp_ms_prot_mono; first iApply "Hple".
        by iApply ewp_os_prot_mono; first iApply iEff_le_bottom.
      + iApply ewp_ms_prot_mono; first iApply "Hple".
        by iApply ewp_os_prot_mono; first iApply iEff_le_bottom.
  Qed.
  
  Lemma ewp_mono_os E σ σ' e Φ Φ' :
    is_os σ -∗ is_os σ' -∗
    EWP e @ E <| σ.2 |> {| σ'.2 |} {{ v, Φ v }} -∗
    (∀ v : val, Φ v ={E}=∗ Φ' v) -∗ EWP e @ E <| σ.2 |> {| σ'.2 |} {{ v, Φ' v }}.
  Proof.
    iIntros "#HOS #HOS' Hewp Himp". 
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
      + iDestruct "HOS" as "[Hbot|Hple]".
        { iDestruct (sem_sig_bot_ieff with "Hbot HΨ") as "[]". }
        iDestruct "Hple" as "(%κ & %τ & %Hneτ & %Hneκ & Hle1 & Hle2)".
        iDestruct (sem_sig_to_ieff with "Hle1 HΨ") as "HΨ".
        iApply (sem_sig_to_ieff with "Hle2"). 
        rewrite !sem_sig_eff_rec_eq.
        iDestruct "HΨ" as "(%α & %u & Hrw & HA & HPost)".
        iExists α, u. iFrame. simpl.
        iIntros (b) "HB". iFrame. by iApply "HPost".
      + iDestruct "HOS'" as "[Hbot|Hple]".
        { iDestruct (sem_sig_bot_ieff with "Hbot HΨ") as "[]". }
        iDestruct "Hple" as "(%κ & %τ & %Hneτ & %Hneκ & Hle1 & Hle2)".
        iDestruct (sem_sig_to_ieff with "Hle1 HΨ") as "HΨ".
        iApply (sem_sig_to_ieff with "Hle2"). 
        rewrite !sem_sig_eff_rec_eq.
        iDestruct "HΨ" as "(%α & %u & Hrw & HA & HPost)".
        iExists α, u. iFrame. simpl.
        iIntros (b) "HB". iFrame. by iApply "HPost".
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
  
  Lemma ewp_wrp_mono_os E σ e Φ Φ' :
    is_os σ -∗
    EWPW e @ E <| σ |> {{ Φ }} -∗
    (∀ v : val, Φ v ={E}=∗ Φ' v) -∗ 
    EWPW e @E <| σ |> {{ Φ' }}. 
  Proof.
    iIntros "#HOS Hewp HΦ". rewrite /ewp_wrp. destruct σ.1. 
    { iApply (ewp_mono_os with "HOS HOS Hewp HΦ"). }
    iApply (ewp_mono_os _ ⊥ with "[] HOS [Hewp] HΦ"); [iLeft; iApply sig_le_nil|done].
  Qed.
  
  Lemma ewp_wrp_mono E σ e Φ Φ' :
    EWPW e @E <| σ |> {{ Φ }} -∗
    □ (∀ v : val, Φ v ={E}=∗ Φ' v) -∗ 
    EWPW e @E <| σ |> {{ Φ' }}.
  Proof.
    iIntros "Hewp HΦ". rewrite /ewp_wrp. destruct σ.1; 
    iApply (ewp_pers_mono with "Hewp HΦ").
  Qed.
  
  Lemma ewp_wrp_pure_step' E e e' σ Φ :
    pure_prim_step e e' → 
    ▷ EWPW e' @E <| σ |>  {{ Φ }} -∗
    EWPW e @E <| σ |> {{ Φ }}. 
  Proof.
    iIntros "%Hprim Hewp". rewrite /ewp_wrp. 
    destruct σ.1; by iApply ewp_pure_step'.
  Qed.
  
  Lemma ewp_wrp_bind k `{NeutralEctx k} E σ e e' Φ  :
    e' = fill k e →
    EWPW e @E <| σ |> {{ w, EWPW (fill k w) @E <| σ |> {{ Φ }} }} -∗
    EWPW e' @E <| σ |> {{ Φ }}.
  Proof.
    iIntros (?) "Hewp". rewrite /ewp_wrp. destruct σ.1;
    by iApply ewp_bind.
  Qed.
  
  Lemma ewp_wrp_alloc E σ Φ v :
    ▷ (∀ (l : loc), l ↦ v ={E}=∗ Φ #l) -∗
      EWPW (ref v)%E @E <| σ |> {{ Φ }}.
  Proof.
    iIntros "H". rewrite /ewp_wrp. destruct σ.1; by iApply ewp_alloc. 
  Qed.
  
  Lemma ewp_wrp_load E σ Φ l q v :
    ▷ l ↦{q} v -∗
      ▷ (l ↦{q} v ={E}=∗ Φ v) -∗
        EWPW (Load #l)%E @E <| σ |> {{ Φ }}.
  Proof.
    iIntros "H". rewrite /ewp_wrp. destruct σ.1; by iApply ewp_load. 
  Qed.
  
  Lemma ewp_wrp_store E σ Φ l v w :
    ▷ l ↦ v -∗
      ▷ (l ↦ w ={E}=∗ Φ #()) -∗
        EWPW (#l <- w)%E @E <| σ |> {{ Φ }}.
  Proof.
    iIntros "H". rewrite /ewp_wrp. destruct σ.1; by iApply ewp_store. 
  Qed.
  
  Lemma ewp_wrp_replace E σ Φ l v w :
    ▷ l ↦ v -∗
      ▷ (l ↦ w ={E}=∗ Φ v) -∗
        EWPW (#l <!- w)%E @E <| σ |> {{ Φ }}.
  Proof.
    iIntros "H". rewrite /ewp_wrp. destruct σ.1; by iApply ewp_replace. 
  Qed.
  
  Lemma ewp_wrp_free E σ Φ l v :
    ▷ l ↦ v -∗
      ▷ (|={E}=> Φ v) -∗
        EWPW (Free #l)%E @E <| σ |> {{ Φ }}.
  Proof.
    iIntros "H". rewrite /ewp_wrp. destruct σ.1; by iApply ewp_free. 
  Qed.
  
  Lemma ewp_wrp_atomic E1 E2 e σ Φ `{!Atomic StronglyAtomic e} :
    TCEq (to_eff e) None →
      (|={E1,E2}=> EWPW e @E2 <| σ |> {{ v, |={E2,E1}=> Φ v }}) -∗
        EWPW e @E1 <| σ |> {{ Φ }}.
  Proof.
    iIntros (?) "H". rewrite /ewp_wrp. destruct σ.1; by iApply ewp_atomic. 
  Qed.

  Lemma ewp_wrp_eff_os E σ Φ v k :
    iEff_car (upcl OS σ) v (λ w, ▷ EWPW (fill k (Val w)) @ E <| (OS, σ) |> {{ Φ }}) -∗
    EWPW (of_eff OS v k) @ E <| (OS, σ) |> {{ Φ }}.
  Proof. 
    iIntros "H". rewrite /ewp_wrp /=.
    by iApply ewp_eff_os.
  Qed.

  Lemma ewp_wrp_do_os E v σ Φ :
    σ.1 ≡ OS -∗
    iEff_car σ.2 v Φ -∗ EWPW (do: v) @ E <| σ |> {{ Φ }}.
  Proof.
    iIntros "HOS Hσ".
    rewrite /ewp_wrp /=. 
    destruct σ.1 eqn:H; rewrite H; 
    last (iDestruct "HOS" as "%HOS"; discriminate).
    iApply ewp_do_os.
    simpl. iExists Φ. iFrame. iIntros (w) "$".
  Qed.

  Lemma ewp_wrp_do_ms E v σ Φ :
    iEff_car σ.2 v Φ -∗ EWPW (doₘ: v) @ E <| σ |> {{ Φ }}.
  Proof.
    iIntros "Hσ".
    rewrite /ewp_wrp /=. 
    destruct σ.1 eqn:H; iApply ewp_do_ms;
    simpl; iExists Φ; iFrame; iIntros "!# % $".
  Qed.

  Definition shallow_handler_wrp
  (E : coPset)
  (σ : sem_sig Σ)
  (Φ : val -d> iProp Σ)
  (h r : expr)
  (σ' : sem_sig Σ)
  (Φ' : val -d> iProp Σ) : iProp Σ :=
    shallow_handler E (match σ.1 with OS => σ.2 | MS => ⊥ end) σ.2 Φ h r
                      (match σ'.1 with OS => σ'.2 | MS => ⊥ end) σ'.2 Φ'.

  
  Definition shallow_handler_wrp_os
    (E : coPset)
    (σ : sem_sig Σ)
    (Φ : val -d> iPropO Σ)
    (h r : expr)
    (σ' : sem_sig Σ)
    (Φ' : val -d> iPropO Σ) : iProp Σ :=

    (* Correctness of the return branch. *)
    (∀ (y : val), Φ y -∗ EWPW r y @ E <| σ' |> {{ Φ' }}) ∧

    (* Correctness of the effect branch. *)
    (∀ (v k : val),
       iEff_car (upcl OS σ.2) v (λ w, EWP k w @ E <| match σ.1 with OS => σ.2 | MS => ⊥ end |> {| σ.2 |} {{ Φ }}) -∗
         EWPW h v k @ E <| σ' |> {{ Φ' }}).

  Lemma shallow_handler_wrp_os_impl E σ Φ h r σ' Φ' :
    shallow_handler_wrp_os E σ Φ h r σ' Φ' -∗
    shallow_handler_wrp E σ Φ h r σ' Φ'.
  Proof.
    iIntros "H". rewrite /shallow_handler_wrp_os /shallow_handler_wrp /ewp_wrp.
    rewrite /shallow_handler. repeat iSplit.
    - iDestruct "H" as "[H _]"; destruct σ'.1; iApply "H".
    - iDestruct "H" as "[_ H]"; destruct σ'.1; iIntros (v k) "Hσ";
      last (iApply ewp_os_prot_mono; first iApply iEff_le_bottom);
      iApply "H"; destruct σ.1; try (iDestruct "Hσ" as "(%Φ''' & [] & _)");
      iApply "Hσ".
    - iDestruct "H" as "[_ H]"; destruct σ'.1; iIntros (v k) "Hσ";
      iApply "H"; simpl; iDestruct "Hσ" as "(%Φ''' & Hσ & #HPost)";
      iExists Φ'''; iFrame; iIntros (w) "HΦ".
      + destruct σ.1; last (iApply ewp_os_prot_mono; first iApply iEff_le_bottom); 
        by iApply "HPost".
      + destruct σ.1; last (iApply ewp_os_prot_mono; first iApply iEff_le_bottom); 
        by iApply "HPost".
  Qed.

  Lemma ewp_wrp_try_with E σ Φ σ' Φ' e h r :
    EWPW e @ E <| σ |> {{ Φ }} -∗
      shallow_handler_wrp E σ Φ h r σ' Φ' -∗
        EWPW (TryWith e h r) @ E <| σ' |> {{ Φ' }}.
  Proof.
    iIntros "Hewp H". rewrite /shallow_handler_wrp /ewp_wrp. 
    destruct σ.1 eqn:Hmd', σ'.1 eqn:Hmd;
    iApply (ewp_try_with with "Hewp"); iApply "H".
  Qed.

  Definition deep_handler_wrp
  (E : coPset)
  (σ : sem_sig Σ)
  (Φ : val -d> iProp Σ)
  (h r : expr)
  (σ' : sem_sig Σ)
  (Φ' : val -d> iProp Σ) : iProp Σ :=
    deep_handler E (match σ.1 with OS => σ.2 | MS => ⊥ end) σ.2 Φ h r
                   (match σ'.1 with OS => σ'.2 | MS => ⊥ end) σ'.2 Φ'.

  Definition deep_handler_wrp_os
    (E : coPset)
    (σ : sem_sig Σ)
    (Φ : val -d> iPropO Σ)
    (h r : expr)
    (σ' : sem_sig Σ)
    (Φ' : val -d> iPropO Σ) : iProp Σ :=

    (* Correctness of the return branch. *)
    (∀ (y : val), Φ y -∗ EWPW r y @ E <| σ' |> {{ Φ' }}) ∧

    (* Correctness of the effect branch. *)
    (∀ (v k : val),
       iEff_car (upcl OS σ.2) v (λ w, ∀ Ψ' Ψ'' Φ'',
          ▷ deep_handler E (match σ.1 with OS => σ.2 | MS => ⊥ end) σ.2 Φ h r Ψ' Ψ'' Φ'' -∗
          EWP k w @ E <| Ψ' |> {| Ψ'' |} {{ Φ'' }}) -∗
         EWPW h v k @ E <| σ' |> {{ Φ' }}).

  Lemma deep_handler_wrp_os_impl E σ Φ h r σ' Φ' :
    deep_handler_wrp_os E σ Φ h r σ' Φ' -∗
    deep_handler_wrp E σ Φ h r σ' Φ'.
  Proof.
    iIntros "H". rewrite /deep_handler_wrp_os /deep_handler_wrp /ewp_wrp.
    rewrite deep_handler_unfold. repeat iSplit.
    - iDestruct "H" as "[H _]"; destruct σ'.1; iApply "H".
    - iDestruct "H" as "[_ H]"; destruct σ'.1; iIntros (v k) "Hσ";
      last (iApply ewp_os_prot_mono; first iApply iEff_le_bottom);
      iApply "H"; destruct σ.1; try (iDestruct "Hσ" as "(%Φ''' & [] & _)");
      iApply "Hσ".
    - iDestruct "H" as "[_ H]"; destruct σ'.1; iIntros (v k) "Hσ";
      iApply "H"; simpl; iDestruct "Hσ" as "(%Φ''' & Hσ & #HPost)";
      iExists Φ'''; iFrame; iIntros (w) "HΦ";
      destruct σ.1; by iApply "HPost".
  Qed.

  Lemma ewp_wrp_deep_try_with E σ Φ (h r : val) σ' Φ' e :
    EWPW e @ E <| σ |> {{ Φ }} -∗
      deep_handler_wrp E σ Φ h r σ' Φ' -∗
        EWPW DeepTryWithV e h r @ E <| σ' |> {{ Φ' }}.
  Proof.
    iIntros "Hewp H". rewrite /deep_handler_wrp /ewp_wrp. 
    destruct σ.1 eqn:Hmd', σ'.1 eqn:Hmd;
    iApply (ewp_deep_try_with with "Hewp"); iApply "H".
  Qed.

End reasoning.
