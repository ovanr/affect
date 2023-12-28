

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

