
Definition sem_row_mode {Σ} (ρ : sem_row Σ) : mode := 
  (map_fold (λ _ m acc, mode_mult acc m) OS (fst <$> ρ)).

Notation "'MODE' ρ" := (sem_row_mode ρ%R) (at level 50).

Global Instance sem_row_mode_ne {Σ} :
  NonExpansive (@sem_row_mode Σ).
Proof.
  intros n ρ ρ' H. rewrite /sem_row_mode. 
  f_equiv. 
  apply map_eq. intros i; rewrite !lookup_fmap.
  destruct (ρ !! i) as [mσ|] eqn:Heq, (ρ' !! i) as [m'σ'|] eqn:Heq'; rewrite Heq Heq'.
  - assert (H': Some mσ  ≡{n}≡ Some m'σ'). 
    { rewrite - Heq - Heq'. apply (H i). }
    simpl. f_equal. destruct mσ as [m σ], m'σ' as [m' σ']. 
    inv H'. inv H2. apply leibniz_equiv; simpl in *.
    eapply discrete_iff; [|apply H0]. apply _.
  - assert (H' : Some mσ ≡{n}≡ None). 
    { rewrite - Heq - Heq'. apply (H i). }
    inv H'.
  - assert (H' : None ≡{n}≡ Some m'σ'). 
    { rewrite - Heq - Heq'. apply (H i). }
    inv H'.
  - done.
Qed.

Global Instance sem_row_mode_proper {Σ} (ρ ρ' : sem_row Σ) :
  Proper ((≡) ==> (≡)) (@sem_row_mode Σ).
Proof. apply ne_proper. apply _. Qed.

Lemma row_mode_nil {Σ} :
  MODE (⟨⟩ : sem_row Σ) = OS.
Proof. rewrite /sem_row_mode fmap_empty map_fold_empty //. Qed.

Lemma row_mode_ins_delete {Σ} (x : string * nat) (σ : sem_sig Σ) (ρ : sem_row Σ) :
  MODE (insert x σ (delete x ρ)) = mode_mult σ.1 (MODE (delete x ρ)).
Proof.
  rewrite /sem_row_mode fmap_insert map_fold_insert_L.
  - by rewrite mode_mult_comm.
  - intros ????????. rewrite - mode_mult_assoc (mode_mult_comm z2 z1) - mode_mult_assoc //.
  - rewrite fmap_delete lookup_delete //.
Qed.
(* OS ̷≤ MS *)
(* When can we have that MODE (l, σ) ⋅ ρ = OS *)
(* ∙ when σ.1 = OS and MODE ρ = OS *)  
(* ∙ when σ.1 = OS and MODE (delete (l, 0) ρ) = OS but ρ(l,0).1 = MS *)
(*     Counter-example in this case: *) 
(*            ρ := { (l, MS), (l', OS) } = MS *)
(*   (l, σ) · ρ := { (l, OS), (l', OS) } = OS *)
(*           ρ' := { (l, MS), (l', OS), (l'', MS) } = MS *)  
(* (l, σ') · ρ' := { (l, OS), (l', OS), (l'', MS) } = MS *)

(* In case something like this is needed: *)  
Lemma mode_le_row_ins {Σ} (ρ ρ' : sem_row Σ) (σ σ' : sem_sig Σ) l :
  MODE ρ ≤M MODE ρ' -∗ σ ≤S σ' -∗
  MODE ((l, σ) · ρ) ≤M MODE ((l, σ') · ρ').
Proof.
  iIntros "#Hρρ' #Hσσ'". 
  destruct (MODE ((l, σ) · ρ)) eqn:H; last iApply mode_le_MS.
  iDestruct (sem_row_mode_ms ((l, σ) · ρ)%R) as "[H _]".
  iSpecialize ("H" with "[]"). first by rewrite H.
  iDestruct "H" as "(%l'' & %s'' & %σ'' & Hlookup'' & Hσ''OS)".
  destruct (decide ((l, 0) = (l'', s''))).
  - inv e. 
    rewrite /sem_row_ins /= lookup_insert. 
    iDestruct (option_equivI with "Hlookup''") as "#Hlookup'''".
    iDestruct (sem_row_mode_os (insert (l'', 0) σ' ρ')) as "[_ H]".
    iSpecialize ("H" with "[]"); last (iRewrite - "H"; iApply mode_le_refl).
    iExists l'', 0, σ'. iSplit; first by rewrite lookup_insert. 
    iRewrite "Hlookup'''" in "Hσσ'".
    iDestruct "Hσσ'" as "[Hmmσ' _]".
    iDestruct "Hσ''OS" as %?.
    iDestruct "Hmmσ'" as "[%|H]"; first rewrite - H1 H0 //.
    rewrite H0. iDestruct "H" as %?. discriminate.
  - iDestruct ("Hρρ'" $! l'' s'' σ'' with "[]") as "(%σ''' & Hlookup''' & Hσ''')".
    { by rewrite lookup_insert_ne; last done. }
    iDestruct (sem_row_mode_os (insert (l, 0) σ' ρ')) as "[_ H]".
    iSpecialize ("H" with "[]"); last (iRewrite - "H"; iApply mode_le_refl).
    iExists l'', s'' , σ'''. iSplit. 
    { by rewrite !lookup_insert_ne. }
    iDestruct "Hσ'''" as "[Hm''' _]".
    iDestruct "Hσ''OS" as %Heq. rewrite Heq. 
    iDestruct "Hm'''" as "[->|H]"; first done.
    iDestruct "H" as %?. discriminate.
Qed.

Lemma sem_row_mode_os {Σ} (ρ : gmap (string * nat) (sem_sig Σ)) :
  (MODE ρ ≡ OS : iProp Σ) ∗-∗ ∀ l s σ, (ρ !! (l, s)) ≡ Some σ -∗ σ.1 ≡ OS.
Proof. 
  iInduction ρ as [|[l s] σ] "IH" using map_ind; iSplit. 
  - iIntros "%Hmd". iIntros (???) "H".
    rewrite lookup_empty. iDestruct "H" as %H. inv H.
  - done.
  - iDestruct "IH" as "[IH1 IH2]".
    iIntros "%Hmd".
    assert (Heq : m = delete (l, s) m).
    { by rewrite delete_notin; last done. }
    rewrite Heq row_mode_ins_delete /= -Heq in Hmd.
    destruct σ.1 eqn:Hσ; last inv Hmd; simpl in Hmd.
    iIntros (l' s' σ') "#Hlookup". 
    destruct (decide ((l, s) = (l', s'))).
    + rewrite - !e. rewrite lookup_insert.
      iDestruct (option_equivI with "Hlookup") as "#Hlookup'".
      iRewrite - "Hlookup'". by rewrite Hmd.
    + rewrite lookup_insert_ne; last done.
      iApply "IH1"; first by rewrite Hmd.
      iApply "Hlookup".
  - iDestruct "IH" as "[IH1 IH2]".
    iIntros "H". 
    assert (Heq : m = delete (l, s) m).
    { by rewrite delete_notin; last done. }
    rewrite Heq row_mode_ins_delete /= -Heq.
    destruct σ.1 eqn:Hσ; simpl.
    + iApply "IH2". iIntros (l' s' σ') "Hlookup".
      destruct (decide ((l, s) = (l', s'))).
      { rewrite - e. rewrite H. iDestruct "Hlookup" as "%H'". inv H'. }
      iApply "H". by rewrite lookup_insert_ne; last done.
    + iDestruct ("H" $! l s σ with "[]") as "%"; first rewrite lookup_insert //. 
      by rewrite Hσ in H0.
Qed.

Lemma sem_row_mode_ms {Σ} (ρ : gmap (string * nat) (sem_sig Σ)) :
  (MODE ρ ≡ MS : iProp Σ) ∗-∗ ∃ l s σ, (ρ !! (l, s)) ≡ Some σ ∗ σ.1 ≡ MS.
Proof. 
  iInduction ρ as [|[l s] σ] "IH" using map_ind; iSplit. 
  - iIntros "%Hmd"; discriminate. 
  - iIntros "(% & % & % & H & _)".
    rewrite lookup_empty. iDestruct "H" as %H. inv H.
  - iDestruct "IH" as "[IH1 IH2]".
    iIntros "%Hmd".
    assert (Heq : m = delete (l, s) m).
    { by rewrite delete_notin; last done. }
    destruct σ.1 eqn:Hσ'.
    2: { iExists l, s, σ. iSplit; first by rewrite lookup_insert. by rewrite Hσ'. }
    rewrite Heq row_mode_ins_delete Hσ' /= -Heq in Hmd.
    iDestruct ("IH1" with "[]") as "(%l' & %s' & %σ' & Hlookup & Hσ')".
    { by rewrite Hmd. }
    iExists l', s', σ'. iFrame "#".
    destruct (decide ((l, s) = (l', s'))).
    { rewrite - !e. rewrite H. iDestruct "Hlookup" as %?. inv H0. }
    by rewrite lookup_insert_ne; last done. 
  - iDestruct "IH" as "[IH1 IH2]".
    iIntros "(%l' & %s' & %σ' & Hlookup & HσOS)". 
    assert (Heq : m = delete (l, s) m).
    { by rewrite delete_notin; last done. }
    rewrite Heq row_mode_ins_delete /= -Heq.
    destruct σ.1 eqn:Hσ; simpl; last done.
    iApply "IH2". 
    destruct (decide ((l, s) = (l', s'))).
    { rewrite - !e. rewrite lookup_insert. 
      iDestruct (option_equivI with "Hlookup") as "#Hlookup'".
      iRewrite - "Hlookup'" in "HσOS".
      iDestruct "HσOS" as "%". rewrite Hσ in H0. discriminate. }
    rewrite lookup_insert_ne; last done.
    iExists l', s', σ'. iFrame.
Qed.

Lemma mode_tun {Σ} (ρ : sem_row Σ) :
  MODE ⦗ ρ ⦘ = MODE ρ.
Proof. 
  apply (map_ind (λ ρ, MODE ⦗ ρ ⦘ = MODE ρ)); first done.
  intros [l s] σ ρ' Hlookup IH.
  - rewrite row_tun_ins. 
    rewrite - insert_delete_insert - (insert_delete_insert _ (l, S s)). 
    rewrite !row_mode_ins_delete !delete_notin; [by rewrite IH|done|].
    rewrite /sem_row_tun.  
    replace (l, S s) with (sem_row_tun_f (l, s)); last done.
    rewrite lookup_kmap //.
Qed.

Lemma mode_tun_os_comm {Σ} (ρ : sem_row Σ) :
  (¡ ⦗ ρ ⦘)%R = (⦗ ¡ ρ ⦘)%R.
Proof. 
  apply (map_ind (λ ρ, ¡ ⦗ ρ ⦘ = ⦗ ¡ ρ ⦘)%R).
  { rewrite /sem_row_tun /sem_row_os kmap_empty fmap_empty //. }
  intros [l s] σ ρ' Hlookup IH.
  rewrite row_tun_ins.
  rewrite !row_os_ins_gen IH row_tun_ins //.
Qed.
