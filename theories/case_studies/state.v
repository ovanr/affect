
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
From affine_tes.lib Require Import base.
From affine_tes.lang Require Import hazel.
From affine_tes.logic Require Import sem_def.
From affine_tes.logic Require Import sem_env.
From affine_tes.logic Require Import sem_types.
From affine_tes.logic Require Import reasoning.
From affine_tes.logic Require Import sem_sub_typing.
From affine_tes.logic Require Import sem_operators.
From affine_tes.logic Require Import compatibility.
From affine_tes.logic Require Import tactics.

Definition get : val := (λ: <>, perform: (InjL #()))%V.
Definition put : val := (λ: "s", (perform: InjR "s") ;; #())%V.

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

  Definition stsig := (∀μTS: θ , α, (@sem_ty_unit Σ) + ℤ ⇒ ℤ)%R.  

  Lemma get_typed :
    ⊢ ⊨ᵥ get : (() -{ stsig }-> ℤ).
  Proof.
    iIntros. iApply sem_typed_closure; solve_sidecond.
    simpl. iApply (sem_typed_perform _ _ _ () with "[]").
    simpl. iApply sem_typed_left_inj. 
    iApply sem_typed_sub_nil. iApply sem_typed_unit.
  Qed.

  Lemma put_typed :
    ⊢ ⊨ᵥ put : (ℤ -{ stsig }-> ()).
  Proof.
    iIntros. iApply sem_typed_closure; solve_sidecond.
    simpl. iApply (sem_typed_seq _ []);
      last (iApply sem_typed_sub_nil; iApply sem_typed_unit).
    iApply (sem_typed_perform _ _ _ () with "[]").
    simpl. iApply sem_typed_right_inj. 
    iApply sem_typed_sub_nil. iApply sem_typed_var.
  Qed.

  Lemma fact_typed :
    ⊢ ⊨ᵥ fact : (ℤ -{ stsig }-> ()).
  Proof.
    iIntros. iApply sem_typed_closure; solve_sidecond.
    simpl. iApply (sem_typed_if _ [("n", _); ("fact", _)]);
      last (iApply sem_typed_sub_nil; 
            do 2 iApply sem_typed_weaken;
            iApply sem_typed_unit).
    { iApply sem_typed_sub_nil. 
      iApply sem_typed_contraction; solve_sidecond.
      iApply sem_typed_bin_op; [constructor|iApply sem_typed_int|].
      iApply sem_typed_var. }
    iApply sem_typed_seq.
    - iApply sem_typed_contraction; solve_sidecond.
      iApply sem_typed_frame.
      iApply sem_typed_swap_second.
      iApply sem_typed_frame.
      iApply sem_typed_app.
      { iApply sem_typed_sub_nil. iApply sem_typed_val. iApply put_typed. }
      iApply sem_typed_bin_op; 
        [constructor| |iApply sem_typed_sub_nil;iApply sem_typed_var].
      iApply sem_typed_app; 
        last (iApply sem_typed_sub_nil; iApply sem_typed_unit).
      iApply sem_typed_sub_nil; iApply sem_typed_val.
      iApply get_typed.
    - iApply (sem_typed_app _ [("fact", _)]); 
        [iApply sem_typed_sub_ty; [apply ty_le_u2aarr|];
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
    set A := (λ (α : sem_ty Σ) (θ : sem_sig Σ), (@sem_ty_unit Σ) + ℤ)%T.
    set B := (λ (_ : sem_ty Σ) (_ : sem_sig Σ), @sem_ty_int Σ)%T.
    iApply (sem_typed_deep_try _ _ [] _ _ _ _ _ _ ⟨⟩%R A B); solve_sidecond.
    { rewrite /A /B -/stsig. 
      iApply sem_typed_app; iApply sem_typed_sub_nil; 
      last (iApply sem_typed_var).
      iApply sem_typed_val. iApply fact_typed. }
    - iIntros (?). rewrite /A /B.
      iApply (sem_typed_match _ [("k", _); ("store", _)]); 
        solve_sidecond; [iApply sem_typed_var| |]; simpl.
      + iApply sem_typed_app; [iApply sem_typed_var|].
        iApply (sem_typed_load_cpy _ _ _ _ ℤ); solve_sidecond.
        iApply sem_typed_swap_second. iApply sem_typed_var.
      + iApply sem_typed_swap_third. iApply sem_typed_contraction; solve_sidecond.
        iApply sem_typed_swap_third.
        iApply (sem_typed_seq _ [("store", _); ("k", _)]). 
        { iApply (sem_typed_store_cpy _ _ _ _ _ _ ℤ); 
            solve_sidecond; iApply sem_typed_var. }
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
    set A := (λ (α : sem_ty Σ) (θ : sem_sig Σ), (@sem_ty_unit Σ) + ℤ)%T.
    set B := (λ (_ : sem_ty Σ) (_ : sem_sig Σ), @sem_ty_int Σ)%T.
    rewrite - {1} (app_nil_r [("n", ℤ)]).
    iApply (sem_typed_deep_try _ _ [] _ _ _ _ _ _ ⟨⟩%R A B); solve_sidecond.
    { rewrite /A /B -/stsig. 
      iApply sem_typed_app; iApply sem_typed_sub_nil; 
      last (iApply sem_typed_var).
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
      iApply sem_typed_sub_ty; [apply ty_le_u2aarr|].
      iApply sem_typed_val. iApply sem_typed_closure; solve_sidecond.
      simpl. iApply sem_typed_var.
  Qed.

End typing.
