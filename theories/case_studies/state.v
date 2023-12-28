
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
From haffel.lib Require Import base.
From haffel.lang Require Import haffel.
From haffel.logic Require Import sem_def.
From haffel.logic Require Import sem_env.
From haffel.logic Require Import sem_sig.
From haffel.logic Require Import sem_types.
From haffel.logic Require Import sem_judgement.
From haffel.logic Require Import copyable.
From haffel.logic Require Import sem_operators.
From haffel.logic Require Import compatibility.
From haffel.logic Require Import tactics.

Definition get : val := (λ: <>, performₘ: (InjL #()))%V.
Definition put : val := (λ: "s", (performₘ: InjR "s") ;; #())%V.

Definition fact : val :=
  (rec: "fact" "n" := if: #1 < "n" then put (get #() * "n");; "fact" ("n" - #1)
                                   else #())%V.

Definition fact_ref : val :=
  (λ: "n", let: "store" := ref #1 in
            deep-try: (fact "n") with
              effect (λ: "x" "k",
                match: "x" with 
                  InjL <> => 
                    (* get effect *)
                    "k" (Load "store")
                | InjR "s" =>
                    (* put effect *)
                    "store" <- "s" ;; "k" (Load "store") 
                end)%E
            | return (λ: "x", Load "store")%E end)%V.

Definition fact_st : val :=
  (λ: "n", deep-try: (fact "n") with
              effect (λ: "x" "k",
                match: "x" with 
                  InjL <> => 
                    (* get effect *) 
                    (λ: "s", "k" "s" "s")%E
                | InjR "s" =>
                    (* put effect *) 
                    (λ: <>, "k" "s" "s")%E
                end)%E
            | return (λ: "x", (λ: "y", "y")%V)%E end #1)%V.

Section typing.

  Context `{!heapGS Σ}.

  Definition stsig : sem_sig Σ := (μ∀TS: _ , _, () + ℤ ⇒ ℤ | MS)%S.

  Lemma get_typed :
    ⊢ ⊨ᵥ get : (() -{ stsig }-> ℤ).
  Proof.
    iIntros. iApply sem_typed_closure; solve_sidecond.
    simpl. iApply (sem_typed_perform_ms _ _ _ () with "[] []"); first solve_copy.
    simpl. iApply sem_typed_left_inj. 
    iApply sem_typed_sub_nil. iApply sem_typed_unit.
  Qed.

  Lemma put_typed :
    ⊢ ⊨ᵥ put : (ℤ -{ stsig }-> ()).
  Proof.
    iIntros. iApply sem_typed_closure; solve_sidecond.
    simpl. iApply (sem_typed_seq _ []);
      last (iApply sem_typed_sub_nil; iApply sem_typed_unit).
    iApply (sem_typed_perform_ms _ _ _ () with "[] []"); first solve_copy.
    simpl. iApply sem_typed_right_inj. 
    iApply sem_typed_sub_nil. iApply sem_typed_var.
  Qed.

  Lemma fact_typed :
    ⊢ ⊨ᵥ fact : (ℤ -{ stsig }-> ()).
  Proof.
    iIntros. iApply sem_typed_closure; solve_sidecond.
    set n := ("n", ℤ : sem_ty Σ).
    set fact := ("fact", ℤ -{ stsig }-> () : sem_ty Σ).
    rewrite /= -/n -/fact.
    iApply (sem_typed_if _ [n; fact]);
      last (iApply sem_typed_sub_nil; 
            do 2 iApply sem_typed_weaken;
            iApply sem_typed_unit).
    { iApply sem_typed_sub_nil. 
      iApply sem_typed_contraction; solve_sidecond.
      iApply sem_typed_bin_op; [constructor|iApply sem_typed_int|].
      iApply sem_typed_var. }
    iApply (sem_typed_seq _ [n;fact]).
    - iApply sem_typed_contraction; solve_copy.
      iApply sem_typed_frame_ms; first solve_copy.
      iApply sem_typed_swap_second.
      iApply sem_typed_frame_ms; first solve_copy.
      iApply (sem_typed_app_ms _ [] _ _ _ ℤ); solve_sidecond.
      { iApply sem_typed_sub_nil. 
        iApply sem_typed_sub_ty; [iApply ty_le_u2aarr|].
        iApply sem_typed_val. iApply put_typed. }
      iApply sem_typed_bin_op; 
        [constructor| |iApply sem_typed_sub_nil;iApply sem_typed_var].
      iApply (sem_typed_app_ms _ _ _ _ _ ()); solve_sidecond; 
        last (iApply sem_typed_sub_nil; iApply sem_typed_unit).
      iApply sem_typed_sub_nil; 
      iApply sem_typed_sub_ty; [iApply ty_le_u2aarr|].
      iApply sem_typed_val. iApply get_typed. 
    - iApply (sem_typed_app_ms _ [fact] _ _ _ ℤ); solve_copy;
        [iApply sem_typed_sub_ty; [iApply ty_le_u2aarr|];
         iApply sem_typed_sub_nil; iApply sem_typed_var|].
      iApply sem_typed_sub_nil.
      iApply sem_typed_bin_op; 
        [constructor|iApply sem_typed_var|iApply sem_typed_int].
  Qed.

  Lemma fact_ref_typed :
    ⊢ ⊨ᵥ fact_ref : (ℤ → ℤ).
  Proof.
    iIntros. iApply sem_typed_closure; solve_sidecond.
    simpl. iApply (sem_typed_let _ [("n", ℤ)]); solve_sidecond. 
    { iApply sem_typed_alloc_cpy. iApply sem_typed_int. }
    iApply sem_typed_swap_second.
    rewrite app_singletons.
    set A : sem_sig Σ → sem_ty Σ → sem_ty Σ := (λ _ _, () + ℤ)%T.
    set B : sem_sig Σ → sem_ty Σ → sem_ty Σ := (λ _ _, ℤ)%T.
    iApply (sem_typed_deep_try_os MS _ [] _ _ "x" _ _ _ _ A B () _ ⊥ with "[] [] []"); solve_sidecond.
    { rewrite /A /B -/stsig. 
      iApply (sem_typed_app_ms _ [] _ _ _ ℤ); solve_copy; 
      iApply sem_typed_sub_nil; last (iApply sem_typed_var).
      iApply sem_typed_sub_ty; [iApply ty_le_u2aarr|].
      iApply sem_typed_val. iApply fact_typed. }
    - iIntros (?). rewrite /A /B.
      iApply (sem_typed_match _ [("k", _); ("store", _)]); 
        solve_sidecond; [iApply sem_typed_var| |]; simpl.
        + iApply sem_typed_app; [iApply sem_typed_var|].
        iApply (sem_typed_load_cpy _ _ _ _ ℤ); solve_sidecond.
        iApply sem_typed_swap_second. 
        iApply sem_typed_var.
      + iApply sem_typed_swap_third. iApply sem_typed_contraction; solve_sidecond.
        iApply sem_typed_swap_third.
        iApply (sem_typed_seq _ [("store", _); ("k", _)]). 
        { iApply sem_typed_store_cpy; iApply sem_typed_var. }
        iApply sem_typed_app; [iApply sem_typed_var|].
        iApply (sem_typed_load_cpy _ _ _ _ ℤ); solve_sidecond.
        iApply sem_typed_var.
    - simpl. iApply sem_typed_weaken. iApply sem_typed_load_cpy; solve_sidecond.
      iApply sem_typed_var.
  Qed.

  Lemma fact_st_typed :
    ⊢ ⊨ᵥ fact_st : (ℤ → ℤ).
  Proof.
    iIntros. iApply sem_typed_closure; solve_sidecond.
    simpl. iApply sem_typed_app; [|iApply sem_typed_int].
    set A : sem_sig Σ → sem_ty Σ → sem_ty Σ := (λ _ _, () + ℤ)%T.
    set B : sem_sig Σ → sem_ty Σ → sem_ty Σ := (λ _ _, ℤ)%T.
    rewrite - {1} (app_nil_r [("n", ℤ)]).
    iApply (sem_typed_deep_try_os MS _ [] _ _ _ _ _ _ _ A B); solve_sidecond.
    { rewrite /A /B -/stsig. 
      iApply (sem_typed_app_ms _ _ _ _ _ ℤ); solve_copy; 
      iApply sem_typed_sub_nil; last iApply sem_typed_var.
      iApply sem_typed_sub_ty; [iApply ty_le_u2aarr|].
      iApply sem_typed_val. iApply fact_typed. }
    - iIntros (?). rewrite /A /B.
      iApply (sem_typed_match _ [("k", _)]); 
        solve_sidecond; [iApply sem_typed_var| |]; simpl.
      + rewrite - {1} (app_nil_r [("k", _)]).
        iApply sem_typed_afun; solve_sidecond. simpl.
        iApply sem_typed_contraction; solve_sidecond.
        do 2 (iApply sem_typed_app; [|iApply sem_typed_var]).
        iApply sem_typed_var.
      + rewrite - {1} (app_nil_r [("s", _); ("k", _)]).
        iApply sem_typed_afun; solve_sidecond. simpl.
        iApply sem_typed_contraction; solve_sidecond.
        do 2 (iApply sem_typed_app; [|iApply sem_typed_var]).
        iApply sem_typed_var.
    - simpl. iApply sem_typed_weaken.
      iApply sem_typed_sub_ty; [iApply ty_le_u2aarr|].
      iApply sem_typed_val. iApply sem_typed_closure; solve_sidecond.
      simpl. iApply sem_typed_var.
  Qed.

End typing.
