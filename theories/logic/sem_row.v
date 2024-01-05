
(* sem_row.v *)

(* This file contains the definition of semantic rows. *)

From iris.proofmode Require Import base tactics.
From iris.algebra Require Import ofe gmap.
From iris.base_logic Require Export iprop upred invariants.

(* Hazel Reasoning *)
From hazel.program_logic Require Import weakest_precondition 
                                        state_reasoning
                                        protocols.

(* Local imports *)
From haffel.lib Require Import logic.
From haffel.lang Require Import haffel.
From haffel.logic Require Import sem_def.
From haffel.logic Require Import mode.
From haffel.logic Require Import sem_sig.

Definition sem_row_nil {Σ} : sem_row Σ := ∅. 
Global Instance sem_row_bottom {Σ} : Bottom (sem_row Σ) := sem_row_nil.

Definition sem_row_ins {Σ} (l : label) (σ : sem_sig Σ) (ρ : sem_row Σ) : sem_row Σ := 
  insert (l, 0) σ ρ.

Definition sem_row_os {Σ} (ρ : sem_row Σ) : sem_row Σ := 
  fmap (λ σ, (σ.1, upcl OS σ.2)) ρ. 

Definition sem_row_tun_f l := 
  (λ k : label * nat, if decide (l = k.1) then (k.1, S k.2)
                                            else (k.1, k.2)).
Definition sem_row_tun {Σ} (l : label) (ρ : sem_row Σ) : sem_row Σ := 
  kmap (sem_row_tun_f l) ρ. 

Local Instance inj_sem_row_tun l : Inj eq eq (sem_row_tun_f l).
Proof. 
  intros k1 k2 H. 
  rewrite /sem_row_tun_f in H. 
  destruct (decide (l = k1.1)), (decide (l = k2.1)); inv H;
  destruct k1, k2; by f_equal.
Qed.

Program Definition sem_row_iEff {Σ} (ρ : sem_row Σ) : iEff Σ :=
  IEff (λ v, λne Φ, ∃ v' l (s : nat) σ, (v ≡ ((#(LitStr l), #s), v')%V) ∗ 
                                lookup (l, s) ρ ≡ Some σ ∗ 
                                iEff_car σ.2 v' Φ)%I.
Next Obligation.
  intros ???????. by repeat f_equiv. 
Qed.


Definition filter_os {Σ} (ρ : gmap (label * nat) (sem_sig Σ)) : sem_row Σ :=
  union_with (λ (σ : sem_sig Σ) _, match σ.1 with 
                        OS => Some σ
                     |  MS => None end) ρ ρ.

(* Notations. *)

Notation "⟨⟩" := (sem_row_nil) : sem_row_scope.
Notation "lσ · ρ" := (sem_row_ins lσ.1%S lσ.2%S ρ%R) (at level 80, right associativity) : sem_row_scope.
Notation "¡ ρ" := (sem_row_os ρ%R) (at level 10) : sem_row_scope.
Notation "⦗ ρ | l ⦘" := (sem_row_tun l%string ρ%R) (at level 5) : sem_row_scope.
Notation "⟦ ρ ⟧" := (sem_row_iEff ρ%R) : sem_row_scope.

(*  Properties *)

Global Instance sem_row_iEff_ne {Σ} :
  NonExpansive (@sem_row_iEff Σ).
Proof.
  intros ????. rewrite /sem_row_iEff. f_equiv.
  intros ??. simpl. by repeat f_equiv.
Qed.

Global Instance sem_row_iEff_proper {Σ} :
  Proper ((≡) ==> (≡)) (@sem_row_iEff Σ).
Proof. apply ne_proper. apply _. Qed.

Global Instance filter_os_ne {Σ} :
  NonExpansive (@filter_os Σ).
Proof.
  intros ????. rewrite /filter_os.
  apply union_with_ne; try done.
  intros ??????. inv H0. inv H2. rewrite H4.
  destruct y0.1 eqn:H'; rewrite H'; last done.
  f_equiv. destruct x0, y0. f_equiv; try done.
  simpl in *; by subst.
Qed.

Global Instance filter_os_proper {Σ} :
  Proper ((≡) ==> (≡)) (@filter_os Σ).
Proof. apply ne_proper. apply _. Qed.

Lemma filter_os_nil {Σ} :
  filter_os (⟨⟩ : sem_row Σ)%R = (⟨⟩ : sem_row Σ)%R.
Proof.
  rewrite /filter_os.
  rewrite union_with_idemp; first done.
  intros ?? H. rewrite lookup_empty in H. inv H.
Qed.

Lemma filter_os_lookup {Σ} (ρ : sem_row Σ) (l : label) (s : nat) (σ : sem_sig Σ) :
  (filter_os ρ !! (l, s) ≡ Some σ : iProp Σ) ⊣⊢
  (ρ !! (l, s) ≡ Some σ ∗ σ.1 ≡ OS).
Proof. 
  iSplit.
  - iIntros "H".
    rewrite /filter_os lookup_union_with. 
    destruct (ρ !! (l, s)) eqn:H; rewrite H /=; 
      last (iDestruct "H" as "%H'"; inv H').
    rewrite /union_with /=. destruct o.1 eqn:H'; rewrite H'.
    + iDestruct (option_equivI with "H") as "#H'".
      iRewrite - "H'". iSplit; first done. by rewrite H'.
    + iDestruct "H" as "%H''". inv H''.
  - iIntros "[Hlookup HσOS]". rewrite /filter_os.
    rewrite lookup_union_with /union_with. 
    destruct (ρ !! (l, s)) eqn:H; rewrite H /=;  
      last (iDestruct "Hlookup" as "%H'"; inv H').
    iDestruct (option_equivI with "Hlookup") as "#H'".
      iRewrite - "H'" in "HσOS". by iRewrite "HσOS". 
Qed.

Lemma row_tun_lookup {Σ} (ρ : sem_row Σ) (σ : sem_sig Σ) (l : label) (s : nat) :
  (⦗ ρ | l ⦘%R !! (l, s) ≡ Some σ : iProp Σ) ⊣⊢
  ∃ s', ⌜ s = S s' ⌝ ∗ (ρ !! (l, s') ≡ Some σ : iProp Σ).
Proof. 
  iSplit.
  - iIntros "Hlookup".
    destruct s.
    + destruct (lookup_kmap_None (sem_row_tun_f l) ρ (l, 0)) as [_ H].
      rewrite H; first (iDestruct "Hlookup" as "%H'"; inv H').
      intros [l'' s''] H'. rewrite /sem_row_tun_f /= in H'.
      destruct (decide (l = l'')) eqn:H''; inv H'.
    + iExists s. iSplit; first done. 
      replace (l, S s) with (sem_row_tun_f l (l, s)); last rewrite /sem_row_tun_f /= decide_True //.
      rewrite lookup_kmap //. 
  - iIntros "(%s' & -> & Hlookup)".
    replace (l, S s') with (sem_row_tun_f l (l, s')); last rewrite /sem_row_tun_f /= decide_True //.
    rewrite lookup_kmap //.
Qed.

Corollary row_tun_lookup_alt {Σ} (ρ : sem_row Σ) (σ : sem_sig Σ) (l : label) (s : nat) :
  (⦗ ρ | l ⦘%R !! (l, S s) ≡ Some σ : iProp Σ) ⊣⊢
  (ρ !! (l, s) ≡ Some σ : iProp Σ).
Proof. 
  iSplit. 
  - rewrite row_tun_lookup. iIntros "(% & %Heq & H)".
    by injection Heq as ->. 
  - iIntros "H". 
    iApply (row_tun_lookup ρ σ l (S s)). 
    iExists s. eauto.
Qed.

Lemma row_tun_lookup_ne {Σ} (ρ : sem_row Σ) (σ : sem_sig Σ) (l l' : label) (s : nat) :
  l ≠ l' →
  (⦗ ρ | l' ⦘%R !! (l, s) ≡ Some σ : iProp Σ) ⊣⊢
  (ρ !! (l, s) ≡ Some σ : iProp Σ).
Proof. 
  intros ?. 
  assert (Heq : (l, s) = (sem_row_tun_f l' (l, s))).
  { rewrite /sem_row_tun_f /= decide_False //. } 
  iSplit; iIntros "Hlookup". 
  - rewrite {1} Heq lookup_kmap //.
  - rewrite {2} Heq lookup_kmap //.
Qed.

Lemma row_os_lookup {Σ} l s (σ : sem_sig Σ) (ρ : sem_row Σ) :
  (¡ ρ)%R !! (l, s) ≡ Some σ ⊣⊢
  ∃ (σ' : sem_sig Σ), σ ≡ (¡ σ')%S ∗ (ρ !! (l, s) ≡ Some σ' : iProp Σ).
Proof. 
  iSplit.
  - rewrite lookup_fmap. iIntros "Hlookup".
    destruct (ρ !! (l, s)) as [σ'|] eqn:H; rewrite H; simpl.
    + iDestruct (option_equivI with "Hlookup") as "#Hlookup'".
      iExists σ'. iSplit; last done.
      by iRewrite - "Hlookup'".
    + iDestruct "Hlookup" as "%H'". inv H'.
  - iIntros "(%σ' & Heq & Hlookup)". rewrite lookup_fmap.
    destruct (ρ !! (l, s)) as [σ''|] eqn:H; rewrite H; simpl.
    + iDestruct (option_equivI with "Hlookup") as "#Hlookup'".
      iRewrite "Hlookup'". by iRewrite "Heq".
    + iDestruct "Hlookup" as "%H'". inv H'.
Qed.

Corollary row_os_lookup_alt {Σ} l s (σ : sem_sig Σ) (ρ : sem_row Σ) :
  (ρ !! (l, s) ≡ Some σ : iProp Σ) ⊢
  (¡ ρ)%R !! (l, s) ≡ Some (¡ σ)%S.
Proof. 
  iIntros "Hlookup". rewrite row_os_lookup.
  iExists σ. by iFrame.
Qed.

(* One-Shot Rows *)

Notation OSRow ρ := (MonoProt ⟦ ρ%R ⟧)%R.

Global Instance row_nil_os_row {Σ} :
  OSRow (⟨⟩ : sem_row Σ).
Proof.
  constructor. rewrite /sem_row_iEff /= /sem_row_nil.
  iIntros (v Φ Φ') "_ (% & % & % & % & _ & H & _)".
  rewrite lookup_empty. iDestruct "H" as "%". inv H. 
Qed.
  
(* TODO: This needs to be generalised, 
         if (l, 0) ∈ ρ then ρ(l, 0) does not need to be an OSSig.
   NOTE: we can have a separate gset of keys that we don't need to check,
         by creating a helper class *)
Global Instance row_ins_os_row {Σ} (ρ : sem_row Σ) l (σ : sem_sig Σ) `{! OSSig σ, OSRow ρ } :
  OSRow ((l, σ) · ρ).
Proof.
  constructor. iIntros (v Φ Φ') "HPost".
  rewrite /sem_row_iEff /=.
  iIntros "(%w & %l' & %s' & %σ' & -> & #Hlookup' & Hσ')".
  destruct (decide ((l, 0) = (l', s'))). 
  - rewrite /sem_row_ins. inv e. 
    iExists w, l', 0, σ'. rewrite lookup_insert. 
    iSplitR; first done. iFrame "#". 
    iDestruct (option_equivI with "Hlookup'") as "#Hlookup''".
    inv OSSig0. 
    iDestruct (monotonic_prot with "HPost") as "H".
    iDestruct (iEff_equivI σ.2 σ'.2) as "[Heq _]".
    iSpecialize ("Heq" with "[]"); first by iRewrite "Hlookup''".
    iRewrite - ("Heq" $! w Φ'). iApply "H". by iRewrite ("Heq" $! w Φ).
  - inv OSRow0. rewrite /sem_row_iEff /= in monotonic_prot.
    iDestruct (monotonic_prot (#(LitStr l'), #s', w)%V Φ Φ' with "HPost [Hσ']") as "(%w'' & %l'' & %s'' & %σ'' & %Heq & Hlookup & Hieff)".
    { iExists w, l', s', σ'. iSplit; first done.
      rewrite lookup_insert_ne; last done. iFrame "∗#". }
    inv Heq. iExists w'', l'', s'', σ''. iSplitR; first done.
    rewrite /sem_row_ins lookup_insert_ne; last done. iFrame "∗".
Qed.

Global Instance row_tun_os_row {Σ} (l : label) (ρ : sem_row Σ) `{ OSRow ρ } :
  OSRow ⦗ ρ | l ⦘.
Proof.
  constructor. rewrite /sem_row_iEff /=. 
  iIntros (v Φ Φ') "HPost".
  iIntros "(%v' & %l' & %s' & %σ' & #Heq & #Hlookup & Hσ')".
  destruct (decide (l = l')) as [->|Hll']. 
  - iDestruct (row_tun_lookup with "Hlookup") as "(%s'' & -> & Hlookup')".
    inv OSRow0.
    iDestruct (monotonic_prot (effect l', #s'', v')%V Φ Φ' with "HPost [Hσ']") as "(%w & %l'' & %s''' & %σ'' & Heq' & Hlookup'' & Hσ'')".
    { iExists v', l', s'', σ'. by iFrame "#∗". }
    iExists v', l', (S s''), σ''. iDestruct "Heq'" as "%". inv H.
    iFrame "#∗". iRewrite "Hlookup'" in "Hlookup''".
    iDestruct (option_equivI with "Hlookup''") as "Heq'".
    by iRewrite "Heq'" in "Hlookup". 
  - rewrite (row_tun_lookup_ne ρ σ' l' l s'); last done.
    inv OSRow0. rewrite /sem_row_iEff /= in monotonic_prot.
    iDestruct (monotonic_prot (effect l', #s', v')%V Φ Φ' with "HPost [Hσ']") as "(%w & %l'' & %s'' & %σ'' & Heq' & Hlookup'' & Hσ'')".
    { iExists v', l', s', σ'. by iFrame "#∗". }
    iExists v', l', s', σ''. iDestruct "Heq'" as "%". inv H.
    iRewrite "Heq"; iSplitR; first done. iFrame.
    rewrite - (row_tun_lookup_ne ρ σ'' l'' l s'') //.
Qed.

Global Instance row_os_os_row {Σ} (ρ : sem_row Σ) :
  OSRow (¡ ρ ).
Proof.
  constructor. rewrite /sem_row_iEff /=.
  iIntros (v Φ Φ') "HPost (% & % & % & % & Heq & #Hlookup & Hσ)".
  iExists v', l, s, σ. iFrame "∗#".
  rewrite row_os_lookup. iDestruct "Hlookup" as "(%σ' & Heq & Hlookup)".
  iDestruct (prod_equivI with "Heq") as "[_ Heq']". simpl.
  iPoseProof (iEff_equivI with "Heq'") as "H".
  iRewrite ("H" $! v' Φ'). 
  pose proof (upcl_mono_prot σ'.2) as [].
  iApply (monotonic_prot with "HPost").
  by iRewrite - ("H" $! v' Φ).
Qed.

Lemma row_filter_os_os_row {Σ} (ρ : sem_row Σ) `{ OSRow ρ } :
  OSRow (filter_os ρ).
Proof.
  constructor. iIntros (v Φ Φ') "HPost Hρ".
  rewrite /sem_row_iEff /=.
  iDestruct "Hρ" as "(% & % & % & % & #Heq & #Hlookup & Hσ)".
  iDestruct (filter_os_lookup ρ l s σ) as "[H _]".
  iDestruct ("H" with "Hlookup") as "[Hlookup' HσOS]".
  inv OSRow0. iPoseProof (monotonic_prot v Φ Φ' with "HPost") as "H'".
  rewrite /sem_row_iEff /=.
  iDestruct ("H'" with "[Hσ]") as "(%w & %l' & %s' & %σ' & #Heq' & #Hlookup'' & Hσ')".
  { iExists v', l, s, σ. iFrame "∗#". }
  iExists w, l', s', σ'. iFrame "#∗".
  iDestruct "Heq'" as "%".
  iDestruct "Heq" as "%". inv H0. 
  iRewrite "Hlookup''" in "Hlookup'".
  iDestruct (option_equivI with "Hlookup'") as "#Heqσ".
  iRewrite "Heqσ". iFrame "#".
Qed.

Lemma os_row_mono_prot {Σ} (ρ : sem_row Σ) l s (σ : sem_sig Σ) `{ OSRow ρ } :
  ρ !! (l, s) ≡ Some σ -∗ mono_prot σ.2.
Proof.
  inv OSRow0.
  iIntros "#Hlookup % % % HPost Hσ". 
  iDestruct (monotonic_prot (effect l, #s, v)%V Φ Φ' with "HPost") as "H".
  iDestruct ("H" with "[Hσ]") as "H".
  { iExists v, l, s, σ. by iFrame "#∗". }
  iDestruct "H" as "(%v' & %l' & %s' & %σ' & %Heq & Hlookup' & Hσ')".
  inv Heq. destruct (ρ !! (l', s')) eqn:Heq; last (iDestruct "Hlookup'" as "%H"; inv H).
  rewrite Heq !option_equivI. iRewrite "Hlookup'" in "Hlookup".
  rewrite prod_equivI_2 iEff_equivI.
  by iRewrite ("Hlookup" $! v' Φ') in "Hσ'".
Qed.

(* Subsumption relation on rows *)

Lemma row_le_refl {Σ} (ρ : sem_row Σ) :
  ⊢ ρ ≤R ρ.
Proof.
  iIntros (l s σ) "H".
  iExists σ. iFrame. iApply sig_le_refl.
Qed.

Lemma row_le_trans {Σ} (ρ₁ ρ₂ ρ₃ : sem_row Σ) :
  ρ₁ ≤R ρ₂ -∗ 
  ρ₂ ≤R ρ₃ -∗
  ρ₁ ≤R ρ₃.
Proof.
  iIntros "Hρ₁₂ Hρ₂₃".
  iIntros (l s σ₁) "Hlookup".
  iDestruct ("Hρ₁₂" with "Hlookup") as "(%σ₂ & Hlookup & Hσ₁₂)".
  iDestruct ("Hρ₂₃" with "Hlookup") as "(%σ₃ & Hlookup & Hσ₂₃)".
  iExists σ₃. iFrame. iApply (sig_le_trans with "Hσ₁₂ Hσ₂₃").
Qed.

Lemma row_le_nil {Σ} (ρ : sem_row Σ) : 
  ⊢ ⟨⟩ ≤R ρ.
Proof.
  iIntros (l s σ) "Hlookup". rewrite lookup_empty. 
  iDestruct "Hlookup" as %H. inv H.
Qed.

Lemma row_nil_iEff_bot {Σ} :
  ⊢ iEff_le (⟦ ⟨⟩ ⟧)%R (⊥ : iEff Σ).
Proof.
  rewrite /sem_row_iEff. iIntros (??) "!#".
  simpl. iIntros "(% & % & % & % & _ & H & _)".
  rewrite lookup_empty. 
  iDestruct "H" as "%". inversion H.
Qed.

Lemma row_le_iEff {Σ} (ρ ρ' : sem_row Σ) :
  ρ ≤R ρ' -∗ iEff_le ⟦ ρ ⟧%R ⟦ ρ' ⟧%R.
Proof.
  rewrite /sem_row_iEff /=.
  iIntros "#Hle !# %v %Φ (%w & %l & %s & %σ & #Heq & #Hlookup & Hσ)".
  iDestruct ("Hle" $! l s σ with "Hlookup") as "(%σ' & #Hlookup' & [_ Hσle])".
  iExists w, l, s, σ'. iFrame "∗#". by iApply "Hσle".
Qed.

Lemma row_le_filter_os_mono {Σ} (ρ ρ' : sem_row Σ) :
  ρ ≤R ρ' -∗ (filter_os ρ) ≤R (filter_os ρ').
Proof.
  iIntros "Hle". rewrite /sem_row_iEff /=.
  iIntros (l s σ) "#Hlookup".
  iDestruct (filter_os_lookup ρ l s σ) as "[Hto _]".
  iDestruct ("Hto" with "Hlookup") as "[Hlookup' HσOS]".
  iDestruct ("Hle" $! l s σ with "Hlookup'") as "(%σ' & #Hlookup'' & #[Hmle Hσle])".
  iExists σ'. rewrite /sig_le /tc_opaque. iFrame "∗#".
  iApply filter_os_lookup. iFrame "#".
  iRewrite "HσOS" in "Hmle". iDestruct "Hmle" as "[H|H]".
  { by iRewrite "H". }
  iDestruct "H" as "%". discriminate.
Qed.

Lemma row_le_filter_os_elim {Σ} (ρ : sem_row Σ) :
  ⊢ filter_os ρ ≤R ρ.
Proof.
  rewrite /sem_row_iEff /=.
  iIntros (l s σ) "#Hlookup".
  iDestruct (filter_os_lookup ρ l s σ) as "[Hto _]".
  iDestruct ("Hto" with "Hlookup") as "[Hlookup' _]".
  iExists σ. iFrame "#". iApply sig_le_refl.
Qed.

Lemma row_le_ins_comp {Σ} (ρ ρ' : sem_row Σ) (l : label) (σ σ' : sem_sig Σ) : 
  ρ ≤R ρ' -∗ σ ≤S σ' -∗
  (l, σ) · ρ ≤R (l, σ') · ρ'.
Proof.
  iIntros "#Hρρ' #Hσσ'".
  iIntros (l'' s'' σ'') "#Hlookup".
  destruct (decide (l = l'')) as [->|].
  - rewrite /sem_row_ins /=. destruct s''.
    + rewrite lookup_insert. 
      iExists σ'. rewrite lookup_insert.
      iSplitR; first done.
      iDestruct (option_equivI with "Hlookup") as "#Hlookup'".
      by iRewrite - "Hlookup'".
    + rewrite lookup_insert_ne; last done.
      iSpecialize ("Hρρ'" $! l'' (S s'') σ'' with "Hlookup").
      rewrite lookup_insert_ne; last done.
      iFrame "#".
  - rewrite lookup_insert_ne; last (intros H; inv H).
    iSpecialize ("Hρρ'" $! l'' s'' σ'' with "Hlookup").
    rewrite lookup_insert_ne; last (intros H; inv H).
    iFrame "#".
Qed.

Lemma row_le_ins {Σ} (ρ : sem_row Σ) (l : label) (σ : sem_sig Σ) : 
  ρ !! (l, 0) ≡ None -∗
  ρ ≤R (l, σ) · ρ. 
Proof. 
  iIntros "#Hlookup".
  iIntros (l' s' σ') "#Hlookup'". 
  destruct (decide ((l, 0) = (l', s'))).
  - rewrite <- e. 
    iAssert (Some σ' ≡ None)%I as "Hlookup''".
    { by iRewrite - "Hlookup'". }
    iDestruct (option_equivI with "Hlookup''") as "[]". 
  - iExists σ'. rewrite lookup_insert_ne; last done.
    iFrame "#". iApply sig_le_refl.
Qed.

Lemma row_le_ins_tun {Σ} (ρ : sem_row Σ) (l : label) (σ : sem_sig Σ) : 
  ⊢ ⦗ ρ | l ⦘ ≤R (l, σ) · ⦗ ρ | l ⦘. 
Proof. 
  iApply row_le_ins. rewrite /sem_row_tun.
  pose proof (lookup_kmap_None (sem_row_tun_f l) ρ (l, 0)) as [_ H].
  rewrite H; first done.
  intros i Hlookup. rewrite /sem_row_tun_f in Hlookup.
  destruct (decide (l = i.1)); inv Hlookup.
Qed.

Lemma row_le_tun_comp {Σ} (l : label) (ρ ρ' : sem_row Σ) :
  ρ ≤R ρ' -∗
  ⦗ ρ | l ⦘ ≤R ⦗ ρ' | l ⦘. 
Proof. 
  iIntros "Hle %l' %s' %σ' Hlookup".
  Search "∗-∗".
  destruct (decide (l = l')) as [->|Hneq].
  - rewrite (row_tun_lookup ρ σ' l' s'). 
    iDestruct "Hlookup" as "(%s'' & -> & Hlookup)".
    iDestruct ("Hle" with "Hlookup") as (σ'') "[H H']".
    iExists σ''. iFrame. 
    rewrite - (row_tun_lookup_alt ρ' σ'' l' s'') //. 
  - rewrite (row_tun_lookup_ne); last done.
    iDestruct ("Hle" with "Hlookup") as (σ'') "[H H']".
    iExists σ''. rewrite row_tun_lookup_ne; last done. iFrame.
Qed.

Lemma row_tun_ins_eq {Σ} l s σ (ρ : sem_row Σ) :
  (⦗ insert (l, s) σ ρ | l ⦘ = insert (l, S s) σ ⦗ ρ | l ⦘)%R. 
Proof.
  rewrite {1} /sem_row_tun /=. 
  rewrite (kmap_insert _ ρ (l, s) σ) // {1}/sem_row_tun_f /= decide_True //.
Qed.

Lemma row_tun_ins_eq_ne {Σ} l l' s σ (ρ : sem_row Σ) :
  l ≠ l' →
  (⦗ insert (l, s) σ ρ | l' ⦘ = insert (l, s) σ ⦗ ρ | l' ⦘)%R. 
Proof.
  intros ?. rewrite {1} /sem_row_tun /=. 
  rewrite (kmap_insert _ ρ (l, s) σ) // {1}/sem_row_tun_f /= decide_False //.
Qed.

Corollary row_le_tun_ins_ne {Σ} l l' σ (ρ : sem_row Σ) :
  l ≠ l' →
  ⊢ ⦗ (l, σ) · ρ | l' ⦘ ≤R (l, σ) · ⦗ ρ | l' ⦘.
Proof.
  intros ?. rewrite row_tun_ins_eq_ne; last done.
  iApply row_le_refl.
Qed.

Corollary row_le_ins_tun_ne {Σ} l l' σ (ρ : sem_row Σ) :
  l ≠ l' →
  ⊢ (l, σ) · ⦗ ρ | l' ⦘ ≤R ⦗ (l, σ) · ρ | l' ⦘.
Proof.
  intros ?. rewrite row_tun_ins_eq_ne; last done.
  iApply row_le_refl.
Qed.

Lemma row_le_tun_comm {Σ} l l' (ρ : sem_row Σ) :
  ⊢ ⦗ ⦗ ρ | l ⦘ | l' ⦘ ≤R ⦗ ⦗ ρ | l' ⦘ | l ⦘.
Proof. 
  iIntros (l'' s'' σ'') "Hlookup".
  destruct (decide (l' = l'')) as [->|H].
  - rewrite row_tun_lookup. iDestruct "Hlookup" as "(%si'' & -> & Hlookup)".
    destruct (decide (l = l'')) as [->|H].
    + rewrite row_tun_lookup. iDestruct "Hlookup" as "(%s & -> & Hlookup)".
      iExists σ''. rewrite ! row_tun_lookup_alt. iSplit; [done|iApply sig_le_refl].
    + rewrite row_tun_lookup_ne; last done. 
      iExists σ''. rewrite row_tun_lookup_ne; last done.
      rewrite row_tun_lookup_alt. iFrame. iApply sig_le_refl.
  - rewrite row_tun_lookup_ne; last done. 
    destruct (decide (l = l'')) as [->|].
    + rewrite row_tun_lookup. iDestruct "Hlookup" as "(%si'' & -> & Hlookup)".
      iExists σ''. rewrite row_tun_lookup_alt.
      rewrite row_tun_lookup_ne; last done. iFrame. iApply sig_le_refl.
    + rewrite row_tun_lookup_ne; last done.
      iExists σ''. do 2 (rewrite row_tun_lookup_ne; try done).
      iFrame. iApply sig_le_refl.
Qed.

Lemma row_os_ins_eq {Σ} l s σ (ρ : sem_row Σ) :
  (¡ (insert (l, s) σ ρ))%R = insert (l, s) (¡ σ)%S (¡ ρ)%R.
Proof. rewrite /sem_row_os fmap_insert //. Qed.

Corollary row_le_os_ins {Σ} l σ (ρ : sem_row Σ) :
  ⊢ ¡ ((l, σ) · ρ) ≤R (l, ¡ σ)%S · (¡ ρ).
Proof. rewrite row_os_ins_eq /=. iApply row_le_refl. Qed.

Corollary row_le_ins_os {Σ} l σ (ρ : sem_row Σ) :
   ⊢ (l, ¡ σ)%S · (¡ ρ) ≤R ¡ ((l, σ) · ρ).
Proof. rewrite row_os_ins_eq /=. iApply row_le_refl. Qed.

Lemma row_le_os_comp {Σ} (ρ ρ' : sem_row Σ) :
  ρ ≤R ρ' -∗
  ¡ ρ ≤R ¡ ρ'. 
Proof. 
  iIntros "Hle %l %s %σ #Hlookup".
  rewrite row_os_lookup. iDestruct "Hlookup" as "(%σ1 & Heq & Hlookup)".
  iDestruct ("Hle" $! l s with "Hlookup") as "(%σ' & #Hlookup' & #Hle)".
  iExists (¡ σ')%S. rewrite row_os_lookup. iSplit. 
  { iExists σ'. iSplit; by iFrame. }
  iRewrite "Heq". by iApply sig_le_os_comp.
Qed.
  
Lemma row_le_os_intro {Σ} (ρ : sem_row Σ) :
  ⊢ ρ ≤R ¡ ρ. 
Proof. 
  iIntros (l s σ) "#Hlookup".
  iExists (¡ σ)%S. rewrite row_os_lookup. 
  iSplit; last iApply sig_le_os_intro.
  iExists σ. by iFrame "#".
Qed.

Lemma row_le_os_elim {Σ} (ρ : sem_row Σ) `{OSRow ρ}:
  ⊢ ¡ ρ ≤R ρ. 
Proof. 
  iIntros (l s σ) "#Hlookup".
  rewrite row_os_lookup. iDestruct "Hlookup" as "(%σ' & Heq & Hlookup)".
  iExists σ'. iFrame "#". iRewrite "Heq". 
  iPoseProof (os_row_mono_prot with "Hlookup") as "Hmono". 
  iDestruct (prod_equivI with "Heq") as "[Heqm _]". simpl.
  (* We can't use sig_le_os_elim here because it requires OSSig σ
   * which leaves outside the current iProp context. 
   * Instead we have to prove it directly *)
  iSplit; first (iRewrite "Heqm"; iApply mode_le_refl).
  iIntros (v Φ) "!# Hσ'".  iDestruct "Hσ'" as "(%Φ' & Hσ' & HPost)".
  by iApply ("Hmono" with "HPost").
Qed.

Lemma row_os_tun_eq {Σ} l (ρ : sem_row Σ) :
  (⦗ (¡ ρ) | l ⦘ = ¡ ⦗ ρ | l ⦘)%R. 
Proof. rewrite /sem_row_tun /sem_row_os /= kmap_fmap //. Qed.

Corollary row_le_tun_os {Σ} (l : label) (ρ : sem_row Σ) :
  ⊢ ⦗ (¡ ρ) | l ⦘ ≤R ¡ ⦗ ρ | l ⦘. 
Proof. rewrite row_os_tun_eq. iApply row_le_refl. Qed.

Corollary row_le_os_tun {Σ} (l : label) (ρ : sem_row Σ) :
  ⊢  ¡ ⦗ ρ | l ⦘ ≤R ⦗ (¡ ρ) | l ⦘.
Proof. rewrite row_os_tun_eq. iApply row_le_refl. Qed.

Lemma row_le_swap_second {Σ} (l l' : label) (σ σ' : sem_sig Σ) (ρ : sem_row Σ) : 
  l ≠ l' →
  ⊢ (l, σ) · (l', σ') · ρ ≤R (l', σ') · (l, σ) · ρ. 
Proof. 
  iIntros (Heq). rewrite /sem_row_ins /= insert_commute;
  first iApply row_le_refl. 
  intros ?. inv H.
Qed.

Lemma row_le_swap_third {Σ} (l l' l'' : label) (σ σ' σ'' : sem_sig Σ) (ρ : sem_row Σ) : 
  l ≠ l' → l' ≠ l'' → l'' ≠ l →
  ⊢ (l, σ) · (l', σ') · (l'', σ'') · ρ ≤R 
    (l'', σ'') · (l, σ) · (l', σ') · ρ. 
Proof. 
  iIntros (???). rewrite /sem_row_ins /= (insert_commute _ (l',0) (l'',0)); last (intros H'; inv H').
  rewrite (insert_commute _ (l, 0) (l'', 0)); last (intros H''; inv H'').
  iApply row_le_refl. 
Qed.

Lemma row_le_swap_fourth {Σ} (l l' l'' l''' : label) (σ σ' σ'' σ''': sem_sig Σ) (ρ : sem_row Σ) : 
  l ≠ l' → l ≠ l'' → l ≠ l''' → l' ≠ l'' → l' ≠ l''' → l'' ≠ l''' → 
  ⊢ (l, σ) · (l', σ') · (l'', σ'') · (l''', σ''') · ρ ≤R 
    (l''', σ''') · (l, σ) · (l', σ') · (l'', σ'') · ρ.
Proof. 
  iIntros (??????). 
  rewrite /sem_row_ins /= (insert_commute _ (l'',0) (l''',0)); last (intros H'; inv H').
  rewrite (insert_commute _ (l', 0) (l''', 0)); last (intros H'; inv H').
  rewrite (insert_commute _ (l, 0) (l''', 0)); last (intros H'; inv H').
  iApply row_le_refl. 
Qed.
