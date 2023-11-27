
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
From haffel.logic Require Import sem_sig.
From haffel.logic Require Import sem_env.
From haffel.logic Require Import sem_sub_typing.
From haffel.logic Require Import ewp_wrp.


Ltac ewp_bottom := 
  iApply ewp_os_prot_mono; [by iApply iEff_le_bottom|].

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

Ltac solve_sidecond := 
    try rewrite !env_dom_nil;
    try rewrite !env_dom_cons;
    solve_dom; 
    solve_disjoint;
    solve_copy.

Ltac solve_dec := 
    ((rewrite decide_True; last (done || split; eauto; intros ?; by simplify_eq)) ||
     (rewrite decide_False; last (done || intros []; by simplify_eq))); 
    simpl.

Ltac match_ewp_wrp_goal lemma tac :=
  match goal with
  | [ |- @bi_emp_valid _                (ewp_wrp ?E ?e ?σ ?ϕ) ] => tac lemma e
  | [ |- @environments.envs_entails _ _ (ewp_wrp ?E ?e ?σ ?ϕ) ] => tac lemma e
  end.

(* Tactic for applying the lemma [ewp_pure_step']. *)
Ltac ewp_wrp_pure_step_lemma :=
  iApply ewp_wrp_pure_step'.

(* Tactic for applying the lemma [ewp_bind]. *)
Ltac ewp_wrp_bind_rule_lemma k :=
  iApply (ewp_wrp_bind k).

Ltac ewp_wrp_bind_rule :=
  match_ewp_wrp_goal ewp_wrp_bind_rule_lemma bind_rule_tac.

(* The tactic [ewp_bind_rule]*)
Ltac ewp_wrp_pure_step :=
  match_ewp_wrp_goal ewp_wrp_pure_step_lemma pure_step_tac.

(* The tactic [ewp_value_or_step] either applies the reasoning rule
   for values ([ewp_value]) or applies the combination of the bind
   rule and the step rule. *)
Ltac ewp_wrp_value_or_step :=
  ((iApply ewp_wrp_value) || (ewp_wrp_bind_rule; ewp_wrp_pure_step));
  try iNext; simpl.

Ltac ewp_wrp_pure_steps :=
  repeat ewp_wrp_value_or_step.
