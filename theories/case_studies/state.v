
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
From haffel.logic Require Import sem_row.
From haffel.logic Require Import sem_types.
From haffel.logic Require Import sem_judgement.
From haffel.logic Require Import copyable.
From haffel.logic Require Import sem_operators.
From haffel.logic Require Import compatibility.
From haffel.logic Require Import tactics.

(* Make all the definitions opaque so that we do not rely on their definition in the model to show that the programs are well-typed terms. *)
Opaque sem_typed sem_typed_val ty_le row_le sig_le row_type_sub row_env_sub.
Opaque sem_ty_void sem_ty_unit sem_ty_bool sem_ty_int sem_ty_string sem_ty_top sem_ty_cpy sem_env_cpy sem_ty_ref_cpy sem_ty_ref sem_ty_prod sem_ty_sum sem_ty_arr sem_ty_aarr sem_ty_uarr sem_ty_forall sem_ty_row_forall sem_ty_exists sem_ty_rec sem_ty_option sem_ty_list.
Opaque sem_sig_eff sem_sig_os.
Opaque sem_row_nil sem_row_ins sem_row_os sem_row_tun sem_row_cons sem_row_rec.

Definition get : val := (λ: <>, perform: "get" #())%V.
Definition put : val := (λ: "s", perform: "put" "s")%V.

Definition fact : val :=
  (rec: "fact" "n" := if: #1 < "n" then put (get #() * "n");; "fact" ("n" - #1)
                                   else #())%V.

Definition fact_ref : val :=
  (λ: "n", let: "store" := ref #1 in
      handle2: (fact "n") by
          "get" => (λ: "x" "k", "k" (Load "store"))
        | "put" => (λ: "x" "k", "store" <- "x" ;; "k" #())
        |  ret  => (λ: "x", Load "store")
      end)%V.

Definition fact_st : val :=
  (λ: "n", 
    (handle2: (fact "n") by
        "get" => (λ: "x" "k", (λ: "s", "k" "s" "s"))
      | "put" => (λ: "x" "k", (λ: <>, "k" #() "x"))
      |  ret  => (λ: "x", (λ: "y", "y"))
      end #1))%V.

Section typing.

  Context `{!heapGS Σ}.

  Definition putsig : operation * sem_sig Σ := ("put", ∀S: (_ : sem_ty Σ), ℤ =[MS]=> ())%S.  
  Definition getsig : operation * sem_sig Σ := ("get", ∀S: (_ : sem_ty Σ), () =[MS]=> ℤ)%S.
  Definition st : sem_row Σ := (putsig ·: getsig ·: ⟨⟩)%R.

  Lemma get_typed :
    ⊢ ⊨ᵥ get : (() -{ st }-> ℤ).
  Proof.
    iIntros. iApply sem_typed_closure; solve_sidecond.
    simpl. rewrite /st. iApply sem_typed_sub_row.
    { by iApply row_le_swap_second. }
    iApply (sem_typed_perform_ms (TT:=[tele _]) [tele_arg ()] with "[] []"); first solve_copy.
    simpl. iApply sem_typed_unit'.
  Qed.

  Lemma put_typed :
    ⊢ ⊨ᵥ put : (ℤ -{ st }-> ()).
  Proof.
    iIntros. iApply sem_typed_closure; solve_sidecond.
    iApply (sem_typed_perform_ms (TT:=[tele _]) [tele_arg ()] with "[] []"); first solve_copy.
    iApply sem_typed_var'.
  Qed.


  Lemma fact_typed :
    ⊢ ⊨ᵥ fact : (ℤ -{ st }-> ()).
  Proof.
    iIntros. iApply sem_typed_closure; solve_sidecond.
    set n := ("n", ℤ : sem_ty Σ).
    set fact := ("fact", ℤ -{ st }-> () : sem_ty Σ).
    rewrite /= -/n -/fact.
    iApply (sem_typed_if _ _ _ [n; fact]);
      last (do 2 iApply sem_typed_weaken; iApply sem_typed_unit').
    { iApply sem_typed_contraction; solve_sidecond.
      iApply sem_typed_bin_op; [constructor|iApply sem_typed_int'|].
      iApply sem_typed_var'. }
    iApply (sem_typed_seq _ _ _ _ [n;fact]).
    - iApply sem_typed_contraction; solve_copy.
      iApply sem_typed_frame_ms; first solve_copy.
      iApply sem_typed_swap_second.
      iApply sem_typed_frame_ms; first solve_copy.
      iApply (sem_typed_app_ms ℤ); solve_sidecond.
      { iApply sem_typed_sub_u2aarr. iApply sem_typed_sub_nil.
        iApply sem_typed_val. iApply put_typed. }
      iApply sem_typed_bin_op; 
        [constructor| |iApply sem_typed_var'].
      iApply (sem_typed_app_ms ()); solve_sidecond; 
        last (iApply sem_typed_unit').
      iApply sem_typed_sub_nil; iApply sem_typed_sub_u2aarr.
      iApply sem_typed_val. iApply get_typed. 
    - iApply (sem_typed_app_ms ℤ); solve_copy; 
        [iApply sem_typed_sub_u2aarr; iApply sem_typed_var'|].
      iApply sem_typed_bin_op; 
        [constructor|iApply sem_typed_var'|iApply sem_typed_int'].
  Qed.

  Lemma fact_ref_typed :
    ⊢ ⊨ᵥ fact_ref : (ℤ → ℤ).
  Proof.
    iIntros. iApply sem_typed_closure; solve_sidecond.
    simpl. iApply (sem_typed_let _ _ _ _ [("n", ℤ)]); solve_sidecond. 
    { iApply sem_typed_alloc_cpy. iApply sem_typed_int. }
    iApply sem_typed_swap_second. rewrite app_singletons. 
    iApply (sem_typed_handler2 (TT:=[tele _]) OS "get" "put" (tele_app (λ _, ())) (tele_app (λ _, ℤ)) (tele_app (λ _, ℤ)) (tele_app (λ _, ())) () ℤ ⊥ _ _ [] with "[] [] []"); solve_sidecond.
    { iApply row_le_refl. }
    - iApply sem_typed_sub_row; first by iApply row_le_swap_second.
      iApply (sem_typed_app_ms ℤ); solve_copy; last iApply sem_typed_var'.
      iApply sem_typed_sub_u2aarr. iApply sem_typed_sub_nil.
      iApply sem_typed_sub_ty; first iApply ty_le_uarr; try iApply ty_le_refl.
      { do 2 (iApply row_le_cons_comp; first iApply sig_le_eff_mode). iApply row_le_nil. }
      iApply sem_typed_val. simpl. iApply fact_typed.
    - iIntros (?).  iApply sem_typed_weaken.
      iApply sem_typed_swap_second. 
      iApply (sem_typed_app_os ℤ); solve_copy. 
      { iApply sem_typed_var'. }
      iApply (sem_typed_load_cpy ℤ); solve_sidecond.
      iApply sem_typed_var'.
    - iIntros (?).
      iApply sem_typed_swap_third. iApply sem_typed_swap_second.
      iApply (sem_typed_seq _ _ _ _  [("k", _)]).
      { iApply sem_typed_store_cpy; iApply sem_typed_var'. }
      iApply sem_typed_app_os; [iApply sem_typed_var'|].
      iApply sem_typed_unit.
    - simpl. iApply sem_typed_weaken. iApply (sem_typed_load_cpy ℤ); solve_sidecond.
      iApply sem_typed_var'.
  Qed.

  Lemma fact_st_typed :
    ⊢ ⊨ᵥ fact_st : (ℤ → ℤ).
  Proof.
    iIntros. iApply sem_typed_closure; solve_sidecond.
    simpl. iApply (sem_typed_app_ms ℤ); solve_copy; last iApply sem_typed_int.
    rewrite - {1} (app_nil_r [("n", ℤ)]).
    iApply (sem_typed_handler2 (TT:=[tele _]) OS "get" "put" (tele_app (λ _, ())) (tele_app (λ _, ℤ)) (tele_app (λ _, ℤ)) (tele_app (λ _, ())) () _ _ _ _ []); solve_sidecond.
    { iApply row_le_refl. }
    - iApply sem_typed_sub_row; first by iApply row_le_swap_second.
      iApply (sem_typed_app_ms ℤ); solve_copy; last iApply sem_typed_var'.
      iApply sem_typed_sub_u2aarr. iApply sem_typed_sub_nil.
      iApply sem_typed_sub_ty; first iApply ty_le_uarr; try iApply ty_le_refl.
      { do 2 (iApply row_le_cons_comp; first iApply sig_le_eff_mode). iApply row_le_nil. }
      iApply sem_typed_val. iApply fact_typed.
    - iIntros (?). iApply sem_typed_weaken.
      rewrite - {1} (app_nil_r [("k", _)]).
      iApply sem_typed_afun; solve_sidecond. simpl.
      iApply (sem_typed_contraction _ _ _ _ _ ℤ); solve_sidecond.
      do 2 (iApply (sem_typed_app_ms ℤ); solve_copy; last iApply sem_typed_var').
      iApply sem_typed_var.
    - iIntros (?).
      rewrite - (app_nil_r [("x", _); ("k", _)]).
      iApply sem_typed_afun; solve_sidecond. simpl.
      iApply (sem_typed_app_ms ℤ); solve_copy; last iApply sem_typed_var.
      iApply (sem_typed_app_ms ()); solve_copy; last iApply sem_typed_unit.
      iApply sem_typed_var.
    - simpl. iApply sem_typed_weaken.
      rewrite - (app_nil_r []).
      iApply sem_typed_afun; solve_sidecond. iApply sem_typed_var.
  Qed.

End typing.
