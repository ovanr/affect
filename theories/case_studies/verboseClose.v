
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

(* The verboseClose example from paper Soundly Hanlding Linearity by Tang et al. *)

(* Since we do not support files (as in the example) we instead use sub-structurally treated references. *)
(* the concept is the same: instead of closing a file, we free the reference *)
Definition verboseFree : val := 
    (λ: "f", let: "s" := perform: "get" #() in
             let: <>  := Free "f" in
             performₘ: "print" "s")%V.

Section typing.

  Context `{!heapGS Σ}.

  Definition getSig : operation * sem_sig Σ := ("get", ∀S: _, () ⇒ Str | OS)%S.  
  Definition printSig : operation * sem_sig Σ := ("print", ∀S: _, Str ⇒ () | MS)%S.
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
      iApply (sem_typed_perform_os () ⟨⟩%R "get" (λ _, ()) (λ _, Str)).
      iApply sem_typed_unit'.
    - iApply sem_typed_seq; first iApply sem_typed_sub_nil.
      { iApply sem_typed_frame. iApply sem_typed_free. iApply sem_typed_var. }
      rewrite /st. iApply sem_typed_sub_row; first by iApply row_le_swap_second.
      rewrite -/getSig.
      iApply (sem_typed_perform_ms () (getSig ·: ⟨⟩)%R MS "print" (λ _, Str) (λ _, ())); solve_copy.
      iApply sem_typed_var'.
  Qed.

End typing.
