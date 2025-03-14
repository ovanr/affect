
(* tactics.v *)

From iris.proofmode Require Import base tactics.

(* Local imports *)
From affect.lib Require Import base.
From affect.lib Require Import logic.
From affect.lang Require Import affect.
From affect.logic Require Import sem_def.
From affect.logic Require Import sem_types.
From affect.logic Require Import sem_sig.
From affect.logic Require Import sem_row.
From affect.logic Require Import sem_env.
From affect.logic Require Import ewpw.

(* Transform a weakest precondition from ewp e {| Ψ |} { Φ } to ewp e { Φ }  *)
Ltac ewp_bottom := 
  iApply ewp_os_prot_mono; [by iApply iEff_le_bottom|].

Ltac destruct_binder_in_not_elem_goal :=
  match goal with 
    | |- context[(@elem_of binder _ _ ?X [])] => destruct X
  end.

(* Solves trivial propositions and ones related to env_dom, such as x ∉ env_dom [] *)
Ltac solve_sidecond := 
    try rewrite !env_dom_nil;
    try rewrite !env_dom_cons; 
    try destruct_binder_in_not_elem_goal;
    repeat (
      (by apply not_elem_of_nil) ||
      (by apply not_elem_of_cons; split; solve_sidecond) || 
        (intros ?; match goal with
          | H : (BAnon ∈ _) |- _ => destruct H
          end) ||
    done).
  
(* Solves propositions related to Decide typeclass *)
Ltac solve_dec := 
    ((rewrite decide_True; last (done || split; eauto; intros ?; by simplify_eq)) ||
     (rewrite decide_False; last (done || intros []; by simplify_eq))); 
    simpl.

Ltac match_ewpw_goal lemma tac :=
  match goal with
  | [ |- @bi_emp_valid _                (ewpw ?E ?e ?σ ?ϕ) ] => tac lemma e
  | [ |- @environments.envs_entails _ _ (ewpw ?E ?e ?σ ?ϕ) ] => tac lemma e
  end.

(* Tactic for applying the lemma [ewp_pure_step']. *)
Ltac ewpw_pure_step_lemma :=
  iApply ewpw_pure_step'.

Ltac pwp_pure_step_lemma :=
  iApply pwp_pure_step'.

(* Tactic for applying the lemma [ewpw_bind]. *)
Ltac ewpw_bind_rule_lemma k :=
  iApply (ewpw_bind k).

Ltac ewpw_bind_rule :=
  match_ewpw_goal ewpw_bind_rule_lemma bind_rule_tac.

(* The tactic [ewp_bind_rule]*)
Ltac ewpw_pure_step :=
  match_ewpw_goal ewpw_pure_step_lemma pure_step_tac.

Ltac pwp_pure_step :=
  match_ewpw_goal pwp_pure_step_lemma pure_step_tac.

(* The tactic [ewp_value_or_step] either applies the reasoning rule
   for values ([ewp_value]) or applies the combination of the bind
   rule and the step rule. *)
Ltac ewpw_value_or_step :=
  ((iApply ewpw_value) || (ewpw_bind_rule; ewpw_pure_step));
  try iNext; simpl.

Ltac ewpw_pure_steps :=
  repeat ewpw_value_or_step.

Tactic Notation "smart_apply" open_constr(lem) := iApply lem; solve_sidecond.
