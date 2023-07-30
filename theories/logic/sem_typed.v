
(* sem_typed.v *)

(* This file contains the definition semantic typing judgments and 
   typed environments.
*)

From iris.proofmode Require Import base tactics classes.
From iris.program_logic Require Import weakestpre.

(* Hazel Reasoning *)
From program_logic Require Import weakest_precondition 
                                  state_reasoning.

(* Local imports *)
From affine_tes.lang Require Import hazel.
From affine_tes.logic Require Import iEff.
From affine_tes.logic Require Import sem_types.


(** The Type Environment

The type environment is represented as a list.
Due to the requirement that a type environment Γ is env_sem_typed,
we can utilize the seperation logic's disjointness to argue about
variables occuring twice in the environment.

Thus if we have a `env_sem_typed Γ vs` assumption and
the same variable occurs twice in Γ we get that:

∙ They cannot be of the same non-persistent type (e.g. ref nat):
  So if we have `env_typed (l : ref nat; l : ref nat) vs`,  
  since the variables l are the same, we would have
  that l, v ∈ vs, and that ⟦ ref nat ⟧ v ∗ ⟦ ref nat ⟧ v
  But that means we would need to provide that l ↦ w ∗ l ↦ w
  which would be impossible.

∙ If they have the same type which is a persistent type (e.g. nat):
  Then it is fine, in fact it must be allowed to allow for Copy types

∙ If they don't have the same type:
  Then `vs` would still have only 1 value for the variable `l` so
  it would be impossible to provide env_typed proof.

*) 

Notation env Σ := (list (string * sem_ty Σ)).

(** The domain of the environment. *)
Notation env_dom := (map fst).

Fixpoint env_sem_typed `{heapGS Σ} (Γ : env Σ)
                        (vs : gmap string val) : iProp Σ :=
  match Γ with
    | [] => emp
    | (x,A) :: Γ' => (∃ v, ⌜ vs !! x = Some v ⌝ ∗ A v) ∗ 
                     env_sem_typed Γ' vs
  end.

Section environment. 

  Context `{!heapGS Σ}.

  Lemma env_sem_typed_empty vs : ⊢ env_sem_typed [] vs.
  Proof. done. Qed.

  Lemma env_sem_typed_insert Γ vs (x : string) v :
    x ∉ (env_dom Γ) →
    env_sem_typed Γ vs ⊢ env_sem_typed Γ (binder_insert x v vs).
  Proof.
    iIntros (Helem) "Henv".
    iInduction Γ as [|[y A] Γ'] "IH"; first done. simpl in *.
    iDestruct "Henv" as "((%w & %Hvs & HAw) & HΓ')". iSplitL "HAw".
    - iExists w. iFrame. iPureIntro.
      destruct (decide (y = x)) as [->|]. 
      { destruct Helem. by apply elem_of_list_here. }
      by rewrite lookup_insert_ne.
    - iApply "IH"; last done. iPureIntro. 
      destruct (not_elem_of_cons (env_dom Γ') x y) as [[ ] _]; done.
  Qed.
  
  Lemma env_sem_typed_delete Γ vs (x : string) v :
    x ∉ (env_dom Γ) →
    env_sem_typed Γ (binder_insert x v vs) ⊢ env_sem_typed Γ vs.
  Proof.
    iIntros (Helem) "Henv".
    iInduction Γ as [|[y A] Γ'] "IH"; first done. simpl in *.
    iDestruct "Henv" as "((%w & %Hvs & HAw) & HΓ')". iSplitL "HAw".
    - iExists w. iFrame. iPureIntro.
      destruct (decide (y = x)) as [->|]. 
      { destruct Helem. by apply elem_of_list_here. }
      by rewrite lookup_insert_ne in Hvs.
    - iApply "IH"; last done. iPureIntro. 
      destruct (not_elem_of_cons (env_dom Γ') x y) as [[ ] _]; done.
  Qed.

  Lemma env_sem_typed_app Γ₁ Γ₂ vs :
    env_sem_typed (Γ₁ ++ Γ₂) vs ⊣⊢ 
    env_sem_typed Γ₁ vs ∗ env_sem_typed Γ₂ vs.
  Proof. 
    iSplit.
    - iIntros "HΓ₁₂". iInduction Γ₁ as [|[y A] Γ₁'] "IH"; first (by iFrame).
      simpl in *. 
      iDestruct "HΓ₁₂" as "($ & HΓ₁'₂)". by iApply "IH".
    - iIntros "[HΓ₁ HΓ₂]". 
      iInduction Γ₁ as [|[y A] Γ₁'] "IH"; first (by iFrame). simpl. 
      iDestruct ("HΓ₁") as "[HA HΓ₁']".
      iFrame.
      iApply ("IH" with "HΓ₁' HΓ₂").
  Qed.

End environment.

(* Semantic typing judgment. *)

(* The semantic typing judgement is defined to be persistent
 * because we want the persistent resources it uses to only be 
 * from the environment Γ.
 *)
Definition sem_typed `{!heapGS Σ}
  (Γ₁  : env Σ)
  (e  : expr)
  (ρ  : sem_row Σ)
  (τ  : sem_ty Σ) 
  (Γ₂  : env Σ) : iProp Σ :=
    tc_opaque( □ (∀ (vs : gmap string val),
                    env_sem_typed Γ₁ vs -∗ EWP (subst_map vs e) <| ρ |> {{ v, τ v ∗ env_sem_typed Γ₂ vs }}))%I.

Global Instance sem_typed_persistent `{!heapGS Σ} (Γ Γ' : env Σ) e ρ τ :
  Persistent (sem_typed Γ e ρ τ Γ').
Proof.
  unfold sem_typed, tc_opaque. apply _.
Qed.

Notation "Γ₁ ⊨ e : ρ : α ⊨ Γ₂" := (sem_typed Γ₁ e%E ρ%R α%T Γ₂)
  (at level 74, e, ρ, α at next level) : bi_scope.

Notation "⊨ e : ρ : α" := (sem_typed [] e%E ρ%R α%T [])
  (at level 74, e, ρ, α at next level) : bi_scope.

(* The value semantic typing judgement is also defined
 * to be persistent, so only persistent values hold for it.
 *) 
Definition sem_val_typed `{!heapGS Σ} 
  (v : val) 
  (A : sem_ty Σ) : iProp Σ := □ (A v).

Notation "⊨ᵥ v : A" := (sem_val_typed v A)
  (at level 20, v, A at next level) : bi_scope.
