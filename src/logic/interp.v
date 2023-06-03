(* interp.v *)

(* This file contains the definition of the 
   interpretation of types, of rows, and of typing judgments. 
   Types are interpreted as semantic types which are Iris's predicates, 
   a row is interpreted as a semantic row which is an iEff protocol,
   and typing judgments are interpreted as specifications written in 
   terms of the extended weakest precondition.
*)

From iris.proofmode Require Import base tactics classes.
From iris.base_logic.lib Require Import iprop.
From iris.program_logic Require Import weakestpre.
From iris Require Import bi.
From stdpp Require Import base stringmap fin_map_dom fin_maps.

(* Hazel language *)
From language Require Import eff_lang.
From program_logic Require Import protocols weakest_precondition tactics.

(* Local imports *)
From logic Require Import subst_map.

(** * Semantic Types. *)

Definition sem_ty Σ := val → iProp Σ.

Declare Scope sem_ty_scope.
Bind Scope sem_ty_scope with sem_ty.
Delimit Scope sem_ty_scope with sem_ty.

(** * Semantic Row. *)

Definition sem_row Σ := iEff Σ.

Bind Scope ieff_scope with sem_row.

Section sem_type_interp.

  (* Base types. *)
  Definition sem_ty_unit {Σ} : sem_ty Σ := (λ v, ⌜ v = #() ⌝)%I.

  Definition sem_ty_bool {Σ} : sem_ty Σ := (λ v, ∃ b : bool, ⌜ v = #b ⌝)%I.

  Definition sem_ty_int {Σ} : sem_ty Σ := (λ v, ∃ n : Z, ⌜ v = #n ⌝)%I.

  (* Product type. *)
  Definition sem_ty_prod {Σ} (A1 A2 : sem_ty Σ) : sem_ty Σ := 
    (λ v, ∃ v1 v2, ⌜v = (v1, v2)%V⌝ ∧ A1 v1 ∧ A2 v2)%I.

  (* Empty Effect Row. *)
  Definition sem_row_null {Σ} : (sem_row Σ) := iEff_bottom.

  (* Effect Row. *)
  Definition sem_row_eff {Σ} (A B : sem_ty Σ) : (sem_row Σ) :=
    (>> (a : val) >> ! a {{ A a }};
     << (b : val) << ? b {{ B b }} @OS).

  (* Arrow type. *)
  Definition sem_ty_arr `{!irisGS eff_lang Σ}
    (A : sem_ty Σ)
    (R : sem_row Σ)
    (B : sem_ty Σ) :=
    (λ (v : val), ∀ (w : val), A w -∗ EWP (v w) <| R |> {{ B }})%I.

End sem_type_interp.

(* Notations. *)
Notation "()" := sem_ty_unit : sem_ty_scope.
Notation "'𝔹'" := (sem_ty_bool) : sem_ty_scope.
Notation "'ℤ'" := (sem_ty_int) : sem_ty_scope.
Infix "*" := sem_ty_prod : sem_ty_scope.
Notation "A '-{' R '}->' B" := (sem_ty_arr A R B)
  (at level 100, R, B at level 200) : sem_ty_scope.

Notation "⟨⟩" := sem_row_null : ieff_scope.
Notation "A ⇒ B" := (sem_row_eff A B) 
  (at level 100, B at level 200) : ieff_scope.


Section environment.

  Definition env_sem_typed Σ (Γ : gmap string (sem_ty Σ)) 
                             (vs : gmap string val) :=
    (⌜ dom stringset Γ ⊆ dom stringset vs ⌝ ∗ 
     [∗ map] i ↦ Av ∈ map_zip Γ vs, Av.1 Av.2)%I.
  
  Lemma env_sem_typed_lookup Σ Γ vs x A :
    Γ !! x = Some A →
    env_sem_typed Σ Γ vs -∗ ∃ v, ⌜ vs !! x = Some v ⌝ ∧ A v.
  Proof.
    iIntros (HΓx) "[%Hseq HΓ]".
    assert (x ∈ (dom stringset vs)).
    { eapply elem_of_subseteq; first done.
      apply (elem_of_dom_2 _ _ _ HΓx). }
    assert (Hsome : is_Some (vs !! x)) by (by apply elem_of_dom).
    destruct Hsome as [w Hw]. iExists w. iSplitR; first done.
    iDestruct (big_sepM_lookup _ _ x (A,w) with "HΓ") as "Av"; last done.
    apply map_lookup_zip_Some; split; done. 
  Qed.

  Lemma env_sem_typed_empty Σ : ⊢ env_sem_typed Σ ∅ ∅.
  Proof. 
    iIntros "". rewrite /env_sem_typed. iSplit.
    - iPureIntro. by rewrite !dom_empty. 
    - by rewrite map_zip_with_empty.
  Qed.

  Lemma env_sem_typed_insert Σ Γ vs (x : string) A v :
    A v -∗ env_sem_typed Σ Γ vs -∗
    env_sem_typed Σ (binder_insert x A Γ) (binder_insert x v vs).
  Proof.
    iIntros "HA [%Hdom HΓ]". rewrite /env_sem_typed. iSplit.
    - rewrite !dom_insert. iPureIntro.
      by apply union_mono_l.
    - simpl. rewrite <- map_insert_zip_with. 
      by iApply (big_sepM_insert_2 with "[HA] HΓ").
  Qed.

  Lemma env_sem_typed_union Σ Γ₁ Γ₂ vs :
    Γ₁ ##ₘ Γ₂ →
    env_sem_typed Σ (Γ₁ ∪ Γ₂) vs ⊢ 
    (env_sem_typed Σ Γ₁ vs ∗ env_sem_typed Σ Γ₂ vs)%I.
  Proof. 
    iIntros (Hdis) "[%Hdom HΓ₁₂]". unfold env_sem_typed.
    assert (dom stringset Γ₁ ⊆ dom stringset vs ∧ 
            dom stringset Γ₂ ⊆ dom stringset vs) as [Hdom₁ Hdom₂]. 
    { apply union_subseteq. by rewrite <- dom_union. }
    rewrite (bi.sep_comm (⌜dom stringset Γ₂ ⊆ dom stringset vs⌝)%I). 
    iApply bi.sep_assoc. iSplitL; last (by iPureIntro).
    iApply bi.sep_assoc. iSplitR; first (by iPureIntro).
    assert (map_zip (Γ₁ ∪ Γ₂) vs = map_zip Γ₁ vs ∪ map_zip Γ₂ vs) as ->.
    - admit.
    - iApply big_sepM_union; last done. 
      Search "map_disjoint".
      admit.
  Admitted.

End environment.


(* Semantic typing judgment. *)
Definition sem_typed `{!irisGS eff_lang Σ}
  (Γ  : gmap string (sem_ty Σ))
  (e  : expr)
  (ρ  : sem_row Σ)
  (α  : sem_ty Σ) : Prop :=
    ∀ (vs : gmap string val),
        env_sem_typed Σ Γ vs ⊢ EWP (subst_map vs e) <| ρ |> {{ α }}.

Notation "Γ ⊨ e : ρ : α" := (sem_typed Γ e ρ α)
  (at level 74, e, ρ, α at next level) : bi_scope.

Open Scope bi_scope.

(* Semantic typing rules. *)

(* Base rules *)

Lemma sem_typed_unit `{!irisGS eff_lang Σ} Γ ρ : 
  Γ ⊨ #() : ρ : ().
Proof.
  iIntros (vs) "HΓvs //=". by iApply ewp_value.
Qed.

Lemma sem_typed_bool `{!irisGS eff_lang Σ} Γ ρ (b : bool) : 
  Γ ⊨ #b : ρ : 𝔹.
Proof.
  iIntros (vs) "HΓvs //=". iApply ewp_value. by iExists b.
Qed.

Lemma sem_typed_int `{!irisGS eff_lang Σ} Γ ρ (i : Z) : 
  Γ ⊨ #i : ρ : ℤ.
Proof.
  iIntros (vs) "HΓvs //=". iApply ewp_value. by iExists i.
Qed.


Lemma sem_typed_fun `{!irisGS eff_lang Σ} Γ x e τ ρ κ: 
  let Γ' := binder_insert x τ Γ in
  Γ' ⊨ e : ρ : κ →
  Γ  ⊨ (λ: x, e)%E : ⟨⟩ : (τ -{ ρ }-> κ).
Proof.
  iIntros (Γ' He vs) "HΓvs //=".
  ewp_pure_steps. iIntros (w) "Hτw". ewp_pure_steps. 
  destruct x eqn:H; simpl in *.
  { by iApply He. }
  rewrite <- subst_map_insert.
  iApply He. unfold Γ'. 
  iApply (env_sem_typed_insert with "Hτw HΓvs").
Qed.

Lemma sem_typed_app `{!irisGS eff_lang Σ} Γ₁ Γ₂ e₁ e₂ τ ρ κ: 
  Γ₁ ##ₘ Γ₂ →
  Γ₁ ⊨ e₁ : ρ : (τ -{ ρ }-> κ) →
  Γ₂ ⊨ e₂ : ρ : τ →
  Γ₁ ∪ Γ₂ ⊨ (e₁ e₂)%E : ρ : κ.
Proof.
  iIntros (Hdis He₁ He₂ vs) "HΓ₁₂vs //=".
  rewrite env_sem_typed_union; last done. 
  iDestruct "HΓ₁₂vs" as "[HΓ₁vs HΓ₂vs]".
  iApply (ewp_bind ([AppRCtx (subst_map vs e₁)])); first done.
  iApply (ewp_mono with "[HΓ₂vs]").
  { by iApply He₂. }
  iIntros (v) "Hτv //=". iModIntro.
  iApply (ewp_bind ([AppLCtx v])); first done.
  iApply (ewp_mono with "[HΓ₁vs]").
  { by iApply He₁. }
  iIntros (w) "Hτκw //=". iModIntro; by iApply "Hτκw". 
Qed.

  


