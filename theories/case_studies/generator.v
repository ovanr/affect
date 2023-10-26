
From iris.proofmode Require Import base tactics.

(* Hazel Reasoning *)
From hazel.program_logic Require Import weakest_precondition 
                                        tactics 
                                        state_reasoning.

(* Local imports *)
From affine_tes.lib Require Import logic.
From affine_tes.lang Require Import hazel.
From affine_tes.case_studies Require Import representable.
From affine_tes.logic Require Import sem_types.


Section generator.
  Context `{!heapGS Σ}.
  
  Context {G : Type → Type} `{DataStructure Σ G, Iterable G}.
  Context {A : Type} `{Representable Σ A}.
      
  Definition YIELD I T : iEff Σ :=
    (>> (us : list A) (u : A) x >> !x   {{ represents x u ∗ ⌜permitted T (us ++ [u])⌝ ∗ I us }}; 
                                   ?#() {{ I (us ++ [u]) }} @ OS).
  Lemma upcl_yield I T v Φ:
    iEff_car (upcl OS (YIELD I T)) v Φ ⊣⊢
      (∃ us u x, ⌜ v = x ⌝ ∗ (represents x u ∗ ⌜ permitted T (us ++ [u])⌝ ∗ I us) ∗ 
                             ((I (us ++ [u])) -∗ Φ #()))%I.
  Proof.
    by rewrite /YIELD (upcl_tele' [tele _ _ _ ] [tele]). 
  Qed.
  
  Definition isGen_pre (isGen : val -d> G A -d> list A -d> iPropO Σ) 
                              : val -d> G A -d> list A -d> iPropO Σ := 
    λ gen T us,
      (EWP (gen #()) {{ v, match v with 
                            NONEV => ⌜complete T us⌝ ∗ isGen gen T us
                          | SOMEV x => ∃ u, represents x u ∗ ⌜permitted T (us ++ [u])⌝ ∗ 
                                            isGen gen T (us ++ [u])
                          | _ => False
                          end }})%I.
  
  Global Instance isGen_contractive : Contractive isGen_pre.
  Proof.
    intros ?????. rewrite /isGen_pre. intros ??.
    apply ewp_contractive; try done. intros ?. destruct n; [apply dist_later_0|]. 
    simpl in *. f_equiv. 
    { do 2 f_equiv. apply dist_later_S. f_equiv.
      apply non_dep_fun_dist3. by rewrite -dist_later_S in H2. }
    apply dist_later_S. do 4 f_equiv. apply non_dep_fun_dist3. 
    by rewrite -dist_later_S in H2.
  Qed.
  
  Definition isGen : val -d> G A -d> list A -d> iPropO Σ := fixpoint isGen_pre.
  
  Lemma isGen_unfold T gen us :
    isGen gen T us ⊣⊢ isGen_pre isGen gen T us.
  Proof.
    rewrite /isGen. apply (fixpoint_unfold isGen_pre).
  Qed.

End generator.

Section list_generator.

  Context `{!heapGS Σ}.

  Definition list_gen :=
      (λ: "xs",
        let: "rxs" := ref "xs" in 
        (λ: <>,
          list-match: Load "rxs" with
            CONS "x" => "xxs" => "rxs" <- !"xxs" ;; SOME "x"
          | NIL => NONE
          end)
      )%E.

  Lemma list_gen_helper `{Representable Σ A} l xs us (T : list A) :
    ⌜permitted T us ⌝ -∗
    l ↦ xs ∗ represents xs (drop (length us) T)  -∗ 
       isGen (λ: <>,
              list-match: Load #l with
                CONS "x" => "xxs" => #l <- !"xxs" ;; SOME "x"
              | NIL => NONE
              end)%V T us.
  Proof.
    iLöb as "IH" forall (xs us T).
    iIntros "(%zs & %Hperm) [Hl Hrepr]". rewrite isGen_unfold /isGen_pre /ListMatch.
    ewp_pure_steps. ewp_bind_rule. iApply (ewp_load with "Hl").
    iIntros "!> Hl !> /=". rewrite /rec_unfold. destruct zs.
    - rewrite app_nil_r in Hperm. subst. rewrite drop_all.
      iDestruct "Hrepr" as "->". ewp_pure_steps. iSplitR "Hl"; first done.
      iApply "IH"; [iPureIntro; exists []; by rewrite app_nil_r|].
      iIntros "{$Hl} /=". by rewrite drop_all.
    - subst. rewrite drop_app_length. ewp_pure_steps.
      iDestruct "Hrepr" as "(%x & %tl & %tlv & Hrepr & -> & Htl & Hgen)".
      rewrite -/(represents tlv).
      ewp_pure_steps. ewp_bind_rule. iApply (ewp_load with "Htl").
      iIntros "!> Htl !> /=". ewp_bind_rule. iApply (ewp_store with "Hl").
      iIntros "!> Hl !> /=". ewp_pure_steps.
      iExists a. iFrame. iSplitR.
      { iPureIntro. exists zs. by rewrite -app_assoc. }
      iApply ("IH" with "[]").
      { iPureIntro. exists zs. by rewrite -app_assoc. }
      iIntros "{$Hl}". replace (us ++ a :: zs) with (us ++ [a] ++ zs) by done.
      rewrite app_assoc. rewrite drop_app_length. iFrame.
  Qed.

  Lemma list_gen_isGen `{Representable Σ A} (T : list A) xs :
    represents xs T -∗ EWP list_gen xs {{ g, isGen g T [] }}. 
  Proof.
    iIntros "Hrepr". rewrite /list_gen. 
    ewp_pure_steps. ewp_bind_rule.
    iApply ewp_alloc. iIntros "!> %l Hl !> /=".
    ewp_pure_steps. 
    iApply (list_gen_helper l xs [] T with "[] [Hl Hrepr]").
    { iPureIntro. by exists T. }
    rewrite drop_0. iFrame.
  Qed.

End list_generator.
