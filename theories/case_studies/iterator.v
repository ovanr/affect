
From iris.proofmode Require Import base tactics.

(* Hazel Reasoning *)
From hazel.program_logic Require Import weakest_precondition 
                                        tactics 
                                        shallow_handler_reasoning 
                                        deep_handler_reasoning 
                                        state_reasoning.

(* Local imports *)
From haffel.lang Require Import haffel.
From haffel.case_studies Require Import representable.


Section iterator.
  Context `{!heapGS Σ}.

  Context {G : Type → Type} `{DataStructure Σ G, Iterable G}.
  Context {A : Type} `{Representable Σ A}.
  
  Definition isIter (iter : val) (T : G A) : iProp Σ :=
    ∀ Ψ (f : val) I,
      □ (∀ us u v, ⌜permitted T (us ++ [u])⌝ -∗ 
                   represents v u -∗
                   I us -∗ 
               EWP (f v) <| Ψ |> {{ _, I (us ++ [u]) }}) -∗
      I [] -∗
      EWP (iter <_> f) <| Ψ |> {{ _, ∃ us, ⌜complete T us⌝ ∗ I us }}.

End iterator.

Section list_iterator.

  Context `{!heapGS Σ}.

  Definition list_iter :=
      (λ: "xs",
        (Λ: (λ: "f", 
              (rec: "go" "xs" := 
                list-match: "xs" with
                  CONS "x" => "xxs" => ("f" "x" ;; "go" (Load "xxs"))
                | NIL => #()
                end) "xs"
           ))
      )%V.

  Lemma list_iter_go_helper A `{Representable Σ A} Ψ l I T (f : val) xs :
    □ (∀ us u v,
        ⌜permitted (l ++ T) (us ++ [u])⌝ -∗
        represents v u -∗ I us -∗ EWP f v <| Ψ |> {{ _, I (us ++ [u]) }})%I -∗
     I l -∗ represents xs T -∗
    (EWP (rec: "go" "xs" :=
              list-match: "xs" with
                CONS "x" => "xxs" => (f "x" ;; "go" (Load "xxs"))
              | NIL => #()
           end)%V xs <| Ψ |> {{ _, ∃ us : list A, ⌜complete (l ++ T) us⌝ ∗ I us }})%I.
  Proof.
    iLöb as "IH" forall (l T xs); simpl.
    iIntros "#Hf HIl Hrepr"; destruct T; simpl.
    - iDestruct "Hrepr" as "->". rewrite /ListMatch /rec_unfold. ewp_pure_steps.
      iExists l. iIntros "{$HIl} !%". by rewrite app_nil_r.
    - iDestruct "Hrepr" as "(%x & %tl & %tlv & Hrepr & -> & Htl & Hrepr')".
      rewrite -{1}/(represents tlv T). 
      ewp_pure_steps. rewrite /rec_unfold. ewp_pure_steps. ewp_bind_rule. 
      iApply (ewp_mono with "[Hf Hrepr HIl]").   
      { iApply ("Hf" with "[] Hrepr HIl").
        iPureIntro. exists T.  rewrite -app_assoc. done. }
      iIntros (v) "HI !> /=". ewp_pure_steps.
      ewp_bind_rule. iApply (ewp_load with "Htl").
      iIntros "!> Htl !> /=".
      iSpecialize ("IH" $! (l ++ [a]) T tlv).
      rewrite -{2}app_assoc. simpl.
      iApply ("IH" with "[] HI Hrepr'").
      rewrite -{2}app_assoc. simpl. iApply "Hf".
  Qed.

  Lemma list_iter_isIter {A} `{Representable Σ A} (xs : val)  (T : list A) :
    represents xs T -∗ EWP list_iter xs {{ i, isIter i T }}.
  Proof.
    iIntros "Hrepr". rewrite /list_iter. ewp_pure_steps. 
    rewrite /isIter. 
    iIntros (Ψ f I) "#Hf HI". 
    do 4 ewp_value_or_step. iApply (ewp_bind [AppLCtx _]); first done.
    do 2 ewp_value_or_step.
    assert (HTeq : T = [] ++ T) by done.
    rewrite {1 3}HTeq.
    iApply (list_iter_go_helper _ Ψ [] I T f xs with "Hf HI Hrepr").
  Qed. 

End list_iterator.
