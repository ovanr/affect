
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

(* The verboseClose example from paper Soundly Hanlding Linearity by Tang et al. *)

(* Since we do not support files (as in the example) we instead use sub-structurally treated references. *)
(* the concept is the same: instead of closing a file, we free the reference *)
Definition verboseFree : val := 
    (λ: "f", let: "s" := perform: "get" #() in
             let: <>  := Free "f" in
             perform: "print" "s")%V.

Section typing.

  Context `{!heapGS Σ}.

  Definition getSig : operation * sem_sig Σ := ("get", ∀S: (_ : sem_ty Σ), () =[OS]=> Str)%S.  
  Definition printSig : operation * sem_sig Σ := ("print", ∀S: (_ : sem_ty Σ), Str =[MS]=> ())%S.
  Definition st : sem_row Σ := (getSig ·: printSig ·: ⟨⟩)%R.

  Local Instance os_row_get_sig : OSRow (getSig ·: ⟨⟩)%R. 
  Proof.
    apply row_cons_os_row; last apply row_nil_os_row.
    apply sig_eff_os_os_sig; apply _.
  Qed.

  Lemma verboseFree_typed :
    ⊢ ⊨ᵥ verboseFree : (Ref 𝔹 -{ st }-> ()).
  Proof.
    iIntros. iApply sem_typed_closure; solve_sidecond.
    simpl. 
    iApply (sem_typed_let Str _ _ _ [("f", _)]); solve_sidecond.
    - rewrite /st.
      iApply sem_typed_sub_row.
      { iApply row_le_cons_comp; [iApply sig_le_refl|iApply row_le_nil]. }
      iApply sem_typed_frame.
      iApply (sem_typed_perform_os (TT:=[tele _]) [tele_arg ()%T] ⟨⟩%R "get" 
                      (tele_app (λ _, ())) (tele_app (λ _, Str))).
      iApply sem_typed_unit'.
    - iApply sem_typed_seq; first iApply sem_typed_sub_nil.
      { iApply sem_typed_frame. iApply sem_typed_free. iApply sem_typed_var. }
      rewrite /st. iApply sem_typed_sub_row; first by iApply row_le_swap_second.
      rewrite -/getSig.
      iApply (sem_typed_perform_ms (TT:=[tele _]) [tele_arg ()] (getSig ·: ⟨⟩)%R 
                      "print" (tele_app (λ _, Str)) (tele_app ((λ _, ())))); solve_copy.
      iApply sem_typed_var'.
  Qed.

End typing.
