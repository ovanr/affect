
From stdpp Require Import base list.
From iris.proofmode Require Import base tactics.
From iris.algebra Require Import excl_auth.

(* Local imports *)
From affect.lib Require Import base.
From affect.lang Require Import affect.
From affect.logic Require Import sem_def.
From affect.logic Require Import sem_env.
From affect.logic Require Import sem_sig.
From affect.logic Require Import sem_row.
From affect.logic Require Import sem_types.
From affect.logic Require Import sem_judgement.
From affect.logic Require Import sem_operators.
From affect.logic Require Import compatibility.
From affect.logic Require Import tactics.

(* Make all the definitions opaque so that we do not rely on their definition in the model to show that the programs are well-typed terms. *)
Opaque sem_typed sem_typed_val ty_le row_le sig_le row_type_sub row_env_sub.
Opaque sem_ty_bot sem_ty_unit sem_ty_bool sem_ty_int sem_ty_string sem_ty_top sem_ty_mbang env_mbang sem_ty_ref_cpy sem_ty_ref sem_ty_prod sem_ty_sum sem_ty_arr sem_ty_type_forall sem_ty_row_forall sem_ty_exists sem_ty_rec sem_ty_option sem_ty_list.
Opaque sem_sig_eff sem_sig_flip_mbang.
Opaque sem_row_nil sem_row_flip_mbang sem_row_cons sem_row_rec.

(* The verboseClose example from paper Soundly Handling Linearity by Tang et al. *)

(* Since we do not support files (as in the example) we instead use sub-structurally treated references. *)
(* the concept is the same: instead of closing a file, we free the reference *)
Definition verboseFree : val := 
    (λ: "f", let: "s" := perform: "get" #() in
             let: <>  := Free "f" in
             perform: "print" "s")%V.

Section typing.

  Context `{!heapGS Σ}.

  Definition getSig : operation * sem_sig Σ := ("get", 𝟙 =[OS]=> Str)%S.  
  Definition printSig : operation * sem_sig Σ := ("print", Str =[MS]=> 𝟙)%S.
  Definition st : sem_row Σ := (getSig · printSig · ⟨⟩)%R.

  Lemma verboseFree_typed :
    ⊢ ⊨ᵥ verboseFree : (Ref 𝔹 -{ st }-> 𝟙).
  Proof.
    iIntros. iApply sem_typed_closure; first done. simpl. 
    smart_apply (sem_typed_let Str _ _ _ [("f", _)]).
    - rewrite /st.
      iApply sem_typed_sub_row.
      { iApply row_le_cons_comp; [iApply sig_le_refl|iApply row_le_nil]. }
      iApply sem_typed_frame.
      iApply (sem_typed_perform_os (TT:=[tele ]) [tele_arg] ⟨⟩%R "get" 
                      (tele_app 𝟙) (tele_app Str)).
      iApply sem_typed_unit'.
    - iApply sem_typed_seq; first iApply sem_typed_sub_nil.
      { iApply sem_typed_frame. iApply sem_typed_free. iApply sem_typed_var. }
      rewrite /st. iApply sem_typed_sub_row; first by iApply row_le_swap_second.
      rewrite -/getSig.
      iApply (sem_typed_perform_ms (TT:=[tele]) [tele_arg] (getSig · ⟨⟩)%R 
                      "print" (tele_app Str) (tele_app 𝟙)).
      iApply sem_typed_var'.
  Qed.

End typing.
