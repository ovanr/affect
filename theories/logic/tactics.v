
From iris.proofmode Require Import base tactics.

(* Hazel Reasoning *)
From hazel.program_logic Require Import weakest_precondition 
                                        tactics 
                                        shallow_handler_reasoning 
                                        deep_handler_reasoning 
                                        state_reasoning.

(* Local imports *)
From haffel.lib Require Import base.
From haffel.lib Require Import logic.
From haffel.lang Require Import hazel.
From haffel.lang Require Import subst_map.
From haffel.logic Require Import iEff.
From haffel.logic Require Import sem_def.
From haffel.logic Require Import sem_types.
From haffel.logic Require Import sem_env.
From haffel.logic Require Import sem_sub_typing.
From haffel.logic Require Import reasoning_os.


Ltac ewp_bottom := iApply ewp_os_prot_mono; [by iApply iEff_le_bottom|].

Ltac destruct_binder_in_not_elem_goal :=
  match goal with 
    | |- context[(@elem_of binder _ _ ?X [])] => destruct X
  end.

Ltac solve_dom := 
    try rewrite !env_dom_nil;
    try rewrite !env_dom_cons; 
    try destruct_binder_in_not_elem_goal;
    repeat (
      (by apply not_elem_of_nil) ||
      (by apply not_elem_of_cons; split; solve_dom) || 
        (intros ?; match goal with
          | H : (BAnon ∈ _) |- _ => destruct H
          end) ||
    done).
  
Ltac solve_disjoint := 
    repeat (
      apply disjoint_empty ||
      apply disjoint_cons_inv ||
      done
    ).

Ltac solve_copy :=
  repeat (
    rewrite !env_sem_typed_empty ||
    rewrite !env_sem_typed_cons ||
    iIntros "#?" ||
    iApply copy_ty_void ||
    iApply copy_ty_unit ||
    iApply copy_ty_bool ||
    iApply copy_ty_nat  ||
    iApply copy_ty_moved ||
    iApply copy_ty_cpy  ||
    iApply copy_ty_uarr ||
    iApply copy_ty_prod ||
    iApply copy_ty_sum ||
    iApply copy_ty_forallT || 
    iApply copy_ty_forallS || 
    iApply copy_ty_ref  || 
    iApply copy_ty_exists || 
    iApply copy_ty_rec || 
    iApply copy_ty_option || 
    iApply copy_ty_list || 
    iApply copy_env_nil || 
    iApply copy_env_cons).

Ltac solve_is_os := try (iApply bot_is_os || iApply os_is_os).

Ltac solve_sidecond := 
    try rewrite !env_dom_nil;
    try rewrite !env_dom_cons;
    solve_dom; 
    solve_disjoint;
    solve_copy;
    solve_is_os.

Ltac solve_dec := 
    ((rewrite decide_True; last (done || split; eauto; intros ?; by simplify_eq)) ||
     (rewrite decide_False; last (done || intros []; by simplify_eq))); 
    simpl.
