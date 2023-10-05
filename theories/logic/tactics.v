
From iris.proofmode Require Import base tactics.

(* Hazel Reasoning *)
From program_logic Require Import weakest_precondition 
                                  tactics 
                                  shallow_handler_reasoning 
                                  deep_handler_reasoning 
                                  state_reasoning.

(* Local imports *)
From affine_tes.lib Require Import base.
From affine_tes.lib Require Import logic.
From affine_tes.lang Require Import hazel.
From affine_tes.lang Require Import subst_map.
From affine_tes.logic Require Import iEff.
From affine_tes.logic Require Import sem_def.
From affine_tes.logic Require Import sem_types.
From affine_tes.logic Require Import sem_env.


Ltac ewp_bottom := iApply ewp_os_prot_mono; 
                   [by iApply iEff_le_bottom|].

Ltac solve_dom := 
    try rewrite !env_dom_nil;
    try rewrite !env_dom_cons; 
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

Global Ltac solve_copy :=
  repeat (
    rewrite !env_sem_typed_empty ||
    rewrite !env_sem_typed_cons ||
    intros ? ||
    apply bi.emp_persistent ||
    apply bi.sep_persistent ||
    apply bi.and_persistent ||
    apply bi.or_persistent ||
    apply bi.forall_persistent ||
    apply bi.exist_persistent ||
    apply bi.pure_persistent ||
    apply plainly_persistent ||
    apply bi.later_persistent ||
    apply bi.persistently_persistent ||
    apply bi.intuitionistically_persistent ||
    apply inv_persistent).

Ltac solve_sidecond := 
    try rewrite !env_dom_nil;
    try rewrite !env_dom_cons;
    solve_dom; 
    solve_disjoint;
    solve_copy.
