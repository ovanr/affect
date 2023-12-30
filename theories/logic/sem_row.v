
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
From haffel.lang Require Import subst_map.
From haffel.logic Require Import iEff.
From haffel.logic Require Import sem_def.
From haffel.logic Require Import mode.
From haffel.logic Require Import sem_sig.

Definition sem_row_nil {Σ} : sem_row Σ := ∅. 
Global Instance sem_row_bottom {Σ} : Bottom (sem_row Σ) := sem_row_nil.

Definition sem_row_ins {Σ} (l : string) (σ : sem_sig Σ) (ρ : sem_row Σ) : sem_row Σ := 
  insert (l, 0) σ ρ.

Definition sem_row_os {Σ} (ρ : sem_row Σ) : sem_row Σ := 
  fmap (λ σ, (σ.1, upcl OS σ.2)) ρ. 

Definition sem_row_tun_f l := 
  (λ k : stringO * nat, if decide (l = k.1) then (k.1, S k.2)
                                            else (k.1, k.2)).
Definition sem_row_tun {Σ} (l : string) (ρ : sem_row Σ) : sem_row Σ := 
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

Global Instance sem_row_iEff_ne {Σ} :
  NonExpansive (@sem_row_iEff Σ).
Proof.
  intros ????. rewrite /sem_row_iEff. f_equiv.
  intros ??. simpl. by repeat f_equiv.
Qed.

Global Instance sem_row_iEff_proper {Σ} :
  Proper ((≡) ==> (≡)) (@sem_row_iEff Σ).
Proof. apply ne_proper. apply _. Qed.

Definition filter_os {Σ} (ρ : gmap (string * nat) (sem_sig Σ)) : sem_row Σ :=
  union_with (λ (σ : sem_sig Σ) _, match σ.1 with 
                        OS => Some σ
                     |  MS => None end) ρ ρ.

Instance filter_os_ne {Σ} :
  NonExpansive (@filter_os Σ).
Proof.
  intros ????. rewrite /filter_os.
  apply union_with_ne; try done.
  intros ??????. inv H0. inv H2. rewrite H4.
  destruct y0.1 eqn:H'; rewrite H'; last done.
  f_equiv. destruct x0, y0. f_equiv; try done.
  simpl in *; by subst.
Qed.

Instance filter_os_proper {Σ} :
  Proper ((≡) ==> (≡)) (@filter_os Σ).
Proof. apply ne_proper. apply _. Qed.


(* Notations. *)

Notation "⟨⟩" := (sem_row_nil) : sem_row_scope.
Notation "lσ · ρ" := (sem_row_ins lσ.1%S lσ.2%S ρ%R) (at level 80, right associativity) : sem_row_scope.
Notation "¡ ρ" := (sem_row_os ρ%R) (at level 10) : sem_row_scope.
Notation "⦗ ρ | l ⦘" := (sem_row_tun l%string ρ%R) (at level 5) : sem_row_scope.
Notation "⟦ ρ ⟧" := (sem_row_iEff ρ%R) : sem_row_scope.

(* One-Shot Rows *)

Notation OSRow ρ := (MonoProt ⟦ ρ%R ⟧)%R.

Global Instance sem_row_nil_os_row {Σ} :
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
Global Instance sem_row_ins_os_row {Σ} (ρ : sem_row Σ) l σ `{ OSSig σ, OSRow ρ } :
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
    iDestruct (monotonic_prot w Φ Φ' with "HPost") as "H".
    iDestruct (iEff_equivI σ.2 σ'.2) as "[Heq _]".
    iSpecialize ("Heq" with "[]"); first by iRewrite "Hlookup''".
    iRewrite ("Heq" $! w Φ) in "H". 
    iRewrite ("Heq" $! w Φ') in "H". 
    by iApply "H".
  - inv OSRow0. rewrite /sem_row_iEff /= in monotonic_prot.
    iDestruct (monotonic_prot (#(LitStr l'), #s', w)%V Φ Φ' with "HPost [Hσ']") as "(%w'' & %l'' & %s'' & %σ'' & %Heq & Hlookup & Hieff)".
    { iExists w, l', s', σ'. iSplit; first done.
      rewrite lookup_insert_ne; last done. iFrame "∗#". }
    inv Heq. iExists w'', l'', s'', σ''. iSplitR; first done.
    rewrite /sem_row_ins lookup_insert_ne; last done. iFrame "∗".
Qed.

Global Instance sem_row_tun_os_row {Σ} (l : string) (ρ : sem_row Σ) `{ OSRow ρ } :
  OSRow ⦗ ρ | l ⦘.
Proof.
  constructor. rewrite /sem_row_iEff /=. 
  iIntros (v Φ Φ') "HPost".
  iIntros "(%v' & %l' & %s' & %σ' & #Heq & #Hlookup & Hσ)".
  destruct (decide (l = l')) as [->|Hll']; first destruct s'.
  - destruct (lookup_kmap_None (sem_row_tun_f l') ρ (l', 0)) as [_ H].
    rewrite H; first (iDestruct "Hlookup" as "%H'"; inv H').
    intros [l'' s''] H'. rewrite /sem_row_tun_f /= in H'.
    destruct (decide (l' = l'')) eqn:H''. rewrite H'' in H'; first inv H'.
    rewrite decide_False in H'; last done. inv H'.
  - replace (l', S s') with (sem_row_tun_f l' (l', s')); last rewrite /sem_row_tun_f /= decide_True //.
    rewrite lookup_kmap. inv OSRow0.
    iDestruct (monotonic_prot (effect l', #s', v')%V Φ Φ' with "HPost [Hσ]") as "(%w & %l'' & %s'' & %σ'' & Heq' & Hlookup'' & Hσ'')".
    { iExists v', l', s', σ'. by iFrame "#∗". }
    iExists v', l', (S s'), σ''. iDestruct "Heq'" as "%". inv H.
    iFrame "#∗".
    replace (l'', S s'') with (sem_row_tun_f l'' (l'', s'')); last rewrite /sem_row_tun_f /= decide_True //.
    rewrite lookup_kmap //.
  - replace (l', s') with (sem_row_tun_f l (l', s')); last rewrite /sem_row_tun_f /= decide_False //. 
    rewrite lookup_kmap. inv OSRow0.
    rewrite /sem_row_iEff /= in monotonic_prot.
    iDestruct (monotonic_prot (effect l', #s', v')%V Φ Φ' with "HPost [Hσ]") as "(%w & %l'' & %s'' & %σ'' & Heq' & Hlookup' & Hσ')".
    { iExists v', l', s', σ'. by iFrame "#∗". }
    iExists v', l', s', σ''. iDestruct "Heq'" as "%". inv H.
    iRewrite "Heq"; iSplitR; first done. iFrame.
    assert (H : (l'', s'') = sem_row_tun_f l (l'', s'')). 
    { rewrite /sem_row_tun_f /= decide_False //. }
    rewrite {3} H. rewrite /sem_row_tun lookup_kmap //. 
Qed.

Global Instance sem_row_os_os_row {Σ} (ρ : sem_row Σ) :
  OSRow (¡ ρ ).
Proof.
  constructor. rewrite /sem_row_iEff /=.
  iIntros (v Φ Φ') "HPost (% & % & % & % & Heq & #Hlookup & Hσ)".
  iExists v', l, s, σ. iFrame "∗#".
  rewrite /sem_row_os lookup_fmap.
  destruct (ρ !! (l, s)) eqn:H; rewrite H /=. 
  - iDestruct (option_equivI with "Hlookup") as "#Hlookup'".
    destruct σ. simpl.
    iDestruct (prod_equivI with "Hlookup'") as "[_ Heq]". simpl.
    iDestruct (iEff_equivI (upcl OS o.2) o1) as "[Heq' _]".
    iSpecialize ("Heq'" with "Heq"). iRewrite - ("Heq'" $! v' Φ').
    pose proof (upcl_mono_prot o.2) as [].
    iApply (monotonic_prot with "HPost").
    by iRewrite ("Heq'" $! v' Φ).
  - iDestruct "Hlookup" as "%H'". inv H'.
Qed.

Lemma filter_os_lookup {Σ} (ρ : sem_row Σ) (l : string) (s : nat) (σ : sem_sig Σ) :
  (filter_os ρ !! (l, s) ≡ Some σ : iProp Σ) ∗-∗
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

Lemma sem_row_filter_os {Σ} (ρ : sem_row Σ) `{ OSRow ρ } :
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

Lemma row_tun_ins {Σ} l s σ (ρ : sem_row Σ) :
  (⦗ insert (l, s) σ ρ | l ⦘ = insert (l, S s) σ ⦗ ρ | l ⦘)%R. 
Proof.
  rewrite {1} /sem_row_tun /=. 
  rewrite (kmap_insert _ ρ (l, s) σ) // {1}/sem_row_tun_f /= decide_True //.
Qed.

Lemma row_tun_ins_ne {Σ} l l' s σ (ρ : sem_row Σ) :
  l ≠ l' →
  (⦗ insert (l, s) σ ρ | l' ⦘ = insert (l, s) σ ⦗ ρ | l' ⦘)%R. 
Proof.
  intros ?. rewrite {1} /sem_row_tun /=. 
  rewrite (kmap_insert _ ρ (l, s) σ) // {1}/sem_row_tun_f /= decide_False //.
Qed.

Lemma row_os_ins_gen {Σ} l s σ (ρ : sem_row Σ) :
  (¡ (insert (l, s) σ ρ))%R = insert (l, s) (¡ σ)%S (¡ ρ)%R.
Proof. rewrite /sem_row_os fmap_insert //. Qed.

Corollary row_os_ins {Σ} l σ (ρ : sem_row Σ) :
  (¡ ((l, σ) · ρ))%R = ((l, ¡ σ)%S · (¡ ρ))%R.
Proof. apply row_os_ins_gen. Qed.

Lemma row_le_ins_comp {Σ} (ρ ρ' : sem_row Σ) (l : string) (σ σ' : sem_sig Σ) : 
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

Lemma row_le_ins {Σ} (ρ : sem_row Σ) (l : string) (σ : sem_sig Σ) : 
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

Lemma row_le_ins_tun {Σ} (ρ : sem_row Σ) (l : string) (σ : sem_sig Σ) : 
  ⊢ ⦗ ρ ⦘ ≤R (l, σ) · ⦗ ρ ⦘. 
Proof. 
  iApply row_le_ins. rewrite /sem_row_tun.
  pose proof (lookup_kmap_None sem_row_tun_f ρ (l, 0)) as [_ H].
  rewrite H; first done.
  intros i Hlookup. inv Hlookup.
Qed.

Lemma row_le_tun_comp {Σ} (ρ ρ' : sem_row Σ) :
  ρ ≤R ρ' -∗
  ⦗ ρ ⦘ ≤R ⦗ ρ' ⦘. 
Proof. 
  iIntros "Hle %l %s %σ Hlookup".
  destruct s.
  - destruct (lookup_kmap_None sem_row_tun_f ρ (l, 0)) as [_ H].
    rewrite H; first (iDestruct "Hlookup" as "%H'"; inv H').
    intros [l' s'] H'. inv H'. 
  - rewrite /sem_row_tun.
    assert (Heq : (l, S s) = (sem_row_tun_f (l, s))) by done.
    rewrite Heq !lookup_kmap.
    by iApply "Hle".
Qed.

Lemma row_le_os_comp {Σ} (ρ ρ' : sem_row Σ) :
  ρ ≤R ρ' -∗
  ¡ ρ ≤R ¡ ρ'. 
Proof. Admitted.
  
Lemma row_le_os_intro {Σ} (ρ : sem_row Σ) `{OSRow ρ} :
  ⊢ ρ ≤R ¡ ρ. 
Proof. Admitted.

Lemma row_le_os_elim {Σ} (ρ : sem_row Σ) :
  ⊢ ¡ ρ ≤R ρ. 
Proof. Admitted.

Lemma row_le_swap_second {Σ} (l l' : string) (σ σ' : sem_sig Σ) (ρ : sem_row Σ) : 
  l ≠ l' →
  ⊢ (l, σ) · (l', σ') · ρ ≤R (l', σ') · (l, σ) · ρ. 
Proof. 
  iIntros (Heq). rewrite /sem_row_ins /= insert_commute;
  first iApply row_le_refl. 
  intros ?. inv H.
Qed.

Lemma row_le_swap_third {Σ} (l l' l'' : string) (σ σ' σ'' : sem_sig Σ) (ρ : sem_row Σ) : 
  l ≠ l' → l' ≠ l'' → l'' ≠ l →
  ⊢ (l, σ) · (l', σ') · (l'', σ'') · ρ ≤R 
    (l'', σ'') · (l, σ) · (l', σ') · ρ. 
Proof. 
  iIntros (???). rewrite /sem_row_ins /= (insert_commute _ (l',0) (l'',0)); last (intros H'; inv H').
  rewrite (insert_commute _ (l, 0) (l'', 0)); last (intros H''; inv H'').
  iApply row_le_refl. 
Qed.

Lemma row_le_swap_fourth {Σ} (l l' l'' l''' : string) (σ σ' σ'' σ''': sem_sig Σ) (ρ : sem_row Σ) : 
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
