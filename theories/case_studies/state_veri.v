
From stdpp Require Import base list.
From iris.proofmode Require Import base tactics.
From iris.algebra Require Import excl_auth.


(* Hazel Reasoning *)
From hazel.program_logic Require Import weakest_precondition 
                                        tactics 
                                        shallow_handler_reasoning 
                                        deep_handler_reasoning 
                                        state_reasoning.

(* Local imports *)
From affect.lib Require Import base.
From affect.lang Require Import affect.
From affect.logic Require Import sem_def.
From affect.logic Require Import sem_row.
From affect.logic Require Import sem_operators.
From affect.logic Require Import ewpw.
From affect.logic Require Import tactics.

Definition get : val := (λ: <>, perform: "get" #())%V.
Definition put : val := (λ: "s", perform: "put" "s")%V.

Definition prog : val := (λ: <>, put #4;; get #())%V.

Definition handler : val :=
  (λ: "e", let: "store" := ref #0 in
      handle2: "e" #() by
          "get" => (λ: "x" "k", "k" (Load "store"))
        | "put" => (λ: "x" "k", "store" <- "x" ;; "k" #())
        |  ret  => (λ: "x", "x")
      end)%V.

Section verification.
  Context `{heapGS Σ}.

  Program Definition put_iEff (I : nat → iProp Σ) : iEff Σ :=
    (>> (n m : nat) >> ! #n  {{ I m }}; ? #() {{ I n }} @OS)%ieff.
  
  Program Definition put_sig (I : nat → iProp Σ) : sem_sig Σ :=
    @PMonoProt Σ (put_iEff I) _.
  Next Obligation.
    rewrite /pers_mono /put_iEff. iIntros (????) "#HPost H".
    rewrite ! iEffPre_exist_eq /= iEffPre_base_eq. 
    iDestruct "H" as "(%m & %n & %Heq & HI & H)". simpl.
    iExists m, n. iFrame. iSplit; first done.
    iIntros "% HI". iApply "HPost". by iApply "H".
  Qed.
  
  Lemma put_iEff_eq (I : nat → iProp Σ) v Φ :
    iEff_car (put_iEff I) v Φ ≡
      (∃ (n m : nat), ⌜ #n = v ⌝ ∗ (I m) ∗ (I n -∗ Φ #()))%I.
  Proof. 
    rewrite /put_iEff iEffPre_exist_eq iEffPre_base_eq /= iEffPost_base_eq /= /iEffPost_base_def.  
    do 6 f_equiv. iSplit.
    - iIntros "H HI". iApply "H". eauto.
    - iIntros "H % [-> HI]". by iApply "H".
  Qed.
  
  Lemma put_sig_eq (I : nat → iProp Σ) v Φ :
    iEff_car (put_sig I) v Φ ≡
      (∃ (n m : nat), ⌜ #n = v ⌝ ∗ (I m) ∗ (I n -∗ Φ #()))%I.
  Proof. rewrite put_iEff_eq //. Qed.
  
  Program Definition get_iEff (I : nat → iProp Σ) : iEff Σ :=
    (>> (n : nat) >> ! #()  {{ I n }}; ? #n {{ I n }} @OS)%ieff.
  
  Program Definition get_sig (I : nat → iProp Σ) : sem_sig Σ :=
    @PMonoProt Σ (get_iEff I) _.
  Next Obligation.
    rewrite /pers_mono /get_iEff. iIntros (????) "#HPost H".
    rewrite ! iEffPre_exist_eq /= iEffPre_base_eq. 
    iDestruct "H" as "(%n & %Heq & HI & H)". simpl.
    iExists n. iFrame. iSplit; first done.
    iIntros "% HI". iApply "HPost". by iApply "H".
  Qed.
  
  Lemma get_iEff_eq (I : nat → iProp Σ) v Φ :
    iEff_car (get_iEff I) v Φ ≡
      (∃ (n : nat), ⌜ #() = v ⌝ ∗ (I n) ∗ (I n -∗ Φ #n))%I.
  Proof. 
    rewrite /get_iEff iEffPre_exist_eq iEffPre_base_eq /= iEffPost_base_eq /= /iEffPost_base_def.  
    do 4 f_equiv. iSplit.
    - iIntros "H HI". iApply "H". eauto.
    - iIntros "H % [-> HI]". by iApply "H".
  Qed.
  
  Lemma get_sig_eq (I : nat → iProp Σ) v Φ :
    iEff_car (get_sig I) v Φ ≡
      (∃ (n : nat), ⌜ #() = v ⌝ ∗ (I n) ∗ (I n -∗ Φ #n))%I.
  Proof. rewrite get_iEff_eq //. Qed.
  
  Definition putsig I : operation * sem_sig Σ := ("put", put_sig I).
  Definition getsig I : operation * sem_sig Σ := ("get", get_sig I).
  Definition st I : sem_row Σ := (putsig I · getsig I · ⟨⟩)%R.
  
  Lemma put_spec (n m : nat) I :
    I n ⊢ EWPW (put #m) <| st I |> {{ v, ⌜ v = #() ⌝ ∗ I m }}.
  Proof.
    iIntros "HI". rewrite /put. ewpw_pure_steps.
    iApply ewpw_do_ms. simpl. iExists "put", #m.
    iSplit; first done. simpl.
    iNext. rewrite put_sig_eq. iExists m, n.
    iSplit; first done. iFrame.
    iIntros "HI". rewrite /rec_perform. ewpw_pure_steps. eauto.
  Qed.

  Lemma get_spec (n : nat) I :
    I n ⊢ EWPW (get #()) <| st I |> {{ v, ⌜ v = #n ⌝ ∗ I n }}.
  Proof.
    iIntros "HI". rewrite /get. ewpw_pure_steps.
    iApply ewpw_sub; first by iApply row_le_swap_second.
    iApply ewpw_do_ms. simpl. iExists "get", #().
    iSplit; first done. simpl.
    iNext. rewrite get_sig_eq. iExists n.
    iSplit; first done. iFrame.
    iIntros "HI". rewrite /rec_perform. ewpw_pure_steps. eauto.
  Qed.

  Lemma handler_spec (e : expr) Φ :
    (∀ I : nat → iProp Σ, I 0 -∗ EWPW e <| st I |> {{ v, Φ v }}) -∗
    EWPW (handler (λ: <>, e)%V) {{ v, Φ v }}.
  Proof.
    iIntros "He". rewrite /handler. ewpw_pure_steps.
    iApply (ewpw_bind [AppRCtx _]); first done.
    iApply ewpw_alloc. iIntros "!> % Hl !> /=".
    ewpw_pure_steps.
    set I := (λ n, l ↦ #n)%I.
    iApply (ewpw_handler2 with "[He Hl]").
    - ewpw_pure_steps. iSpecialize ("He" $! I with "Hl"). rewrite /st.
      iApply ewpw_sub; first by iApply row_le_swap_second.
      iApply "He".
    - rewrite /handler2_spec. iSplit; first iApply row_le_nil.
      iSplit; first done. iIntros "!#". iSplit; last iSplit.
      + iIntros (v) "HΦ". by ewpw_pure_steps.
      + iIntros (v k) "(%Φ' & H & Hk)". simpl.
        rewrite get_sig_eq. 
        iDestruct "H" as "(%n & <- & HI & HPost)".
        ewpw_pure_steps. iApply (ewpw_bind [AppRCtx _]); first done.
        iApply (ewpw_load with "HI"). iIntros "!> Hl !> /=".
        iApply "Hk". by iApply "HPost".
      + iIntros (v k) "(%Φ' & H & Hk)". simpl.
        rewrite put_sig_eq. 
        iDestruct "H" as "(%n & %m & <- & HI & HPost)".
        ewpw_pure_steps. iApply (ewpw_bind [AppRCtx _]); first done.
        iApply (ewpw_store with "HI"). iIntros "!> Hl !> /=".
        ewpw_pure_steps. iApply "Hk". by iApply "HPost".
    Qed.

  Lemma prog_spec : ⊢ EWPW (handler prog) {{ v, ⌜ v = #4 ⌝ }}.
  Proof.
    iIntros. rewrite /prog. iApply handler_spec.
    iIntros (I) "HI". iApply (ewpw_bind [AppRCtx _]); first done.
    iApply (ewpw_mono with "[HI]").
    { iApply (put_spec 0 4 I with "HI"). }
    iIntros "!# % [-> HI] !> /=". ewpw_pure_steps.
    iApply (ewpw_mono with "[HI]").
    { iApply (get_spec 4 I with "HI"). }
    iIntros "!# % [-> HI] !> //". 
  Qed.

End verification.
