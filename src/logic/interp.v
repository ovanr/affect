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
From program_logic Require Import protocols weakest_precondition tactics.

(* Local imports *)
From lang Require Import hazel subst_map.

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
    (λ v, ∃ v1 v2, ⌜v = (v1, v2)%V⌝ ∗ A1 v1 ∗ A2 v2)%I.

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


Notation ctx Σ := (list (string * (sem_ty Σ))).

(** The domain of the context. *)
Definition ctx_dom Σ : ctx Σ -> list string := map fst.

Fixpoint env_sem_typed Σ (Γ : ctx Σ)
                          (vs : gmap string val) : iProp Σ :=
  match Γ with
    | [] => True
    | (x,A) :: Γ' => (∃ v, ⌜ vs !! x = Some v ⌝ ∗ A v) ∗ 
                          env_sem_typed Σ Γ' vs
  end.

Lemma env_sem_typed_empty Σ vs : ⊢ env_sem_typed Σ [] vs.
Proof. done. Qed.

Lemma env_sem_typed_insert Σ Γ vs x v :
  ~In x (ctx_dom Σ Γ) →
  env_sem_typed Σ Γ vs ⊢ env_sem_typed Σ Γ (binder_insert x v vs).
Proof.
  iIntros (HIn) "Henv".
  iInduction Γ as [|[y A] Γ'] "IH"; first done. simpl in *.
  iDestruct "Henv" as "((%w & %Hvs & HAw) & HΓ')". iSplitL "HAw".
  - iExists w. iFrame. iPureIntro.
    destruct (decide (y = x)) as [->|]. 
    { destruct HIn. auto. }
    by rewrite lookup_insert_ne.
  - iApply "IH"; last done. iPureIntro. tauto.
Qed.

Lemma env_sem_typed_app Σ Γ₁ Γ₂ vs :
  env_sem_typed Σ (Γ₁ ++ Γ₂) vs ⊢ 
  (env_sem_typed Σ Γ₁ vs ∗ env_sem_typed Σ Γ₂ vs)%I.
Proof. 
  iIntros "HΓ₁₂". iInduction Γ₁ as [|[y A] Γ₁'] "IH"; first (by iFrame).
  simpl in *. 
  iDestruct "HΓ₁₂" as "($ & HΓ₁'₂)". by iApply "IH".
Qed.


(* Semantic typing judgment. *)
Definition sem_typed `{!irisGS eff_lang Σ}
  (Γ  : ctx Σ)
  (e  : expr)
  (ρ  : sem_row Σ)
  (α  : sem_ty Σ) : Prop :=
    ∀ (vs : gmap string val),
        env_sem_typed Σ Γ vs ⊢ EWP (subst_map vs e) <| ρ |> {{ α }}.

Notation "Γ ⊨ e : ρ : α" := (sem_typed Γ e ρ α)
  (at level 74, e, ρ, α at next level) : bi_scope.

Notation "⊨ e : ρ : α" := (sem_typed [] e ρ α)
  (at level 74, e, ρ, α at next level) : bi_scope.

Open Scope bi_scope.

(* Semantic typing rules. *)

(* Base rules *)

Lemma sem_typed_unit `{!irisGS eff_lang Σ} Γ ρ : 
  Γ ⊨ #() : ρ : ().
Proof.
  iIntros (vs) "HΓ //=". by iApply ewp_value.
Qed.

Lemma sem_typed_bool `{!irisGS eff_lang Σ} Γ ρ (b : bool) : 
  Γ ⊨ #b : ρ : 𝔹.
Proof.
  iIntros (vs) "HΓ //=". iApply ewp_value. by iExists b.
Qed.

Lemma sem_typed_int `{!irisGS eff_lang Σ} Γ ρ (i : Z) : 
  Γ ⊨ #i : ρ : ℤ.
Proof.
  iIntros (vs) "HΓ //=". iApply ewp_value. by iExists i.
Qed.

Lemma sem_typed_fun `{!irisGS eff_lang Σ} Γ x e τ ρ κ: 
  ~In x (ctx_dom Σ Γ) →
  (x,τ) :: Γ ⊨ e : ρ : κ →
  Γ ⊨ (λ: x, e)%E : ⟨⟩ : (τ -{ ρ }-> κ).
Proof.
  iIntros (HIn He vs) "HΓ //=".
  ewp_pure_steps. iIntros (w) "Hτw". ewp_pure_steps. 
  rewrite <- subst_map_insert.
  iApply He. simpl in *. iSplitL "Hτw".
  - iExists w. iFrame. iPureIntro.
    by rewrite lookup_insert.
  - by iApply env_sem_typed_insert.
Qed.

Lemma sem_typed_app `{!irisGS eff_lang Σ} Γ₁ Γ₂ e₁ e₂ τ ρ κ: 
  Γ₁ ⊨ e₁ : ρ : (τ -{ ρ }-> κ) →
  Γ₂ ⊨ e₂ : ρ : τ →
  Γ₁ ++ Γ₂ ⊨ (e₁ e₂)%E : ρ : κ.
Proof.
  iIntros (He₁ He₂ vs) "HΓ₁₂ //=".
  rewrite env_sem_typed_app.
  iDestruct "HΓ₁₂" as "[HΓ₁ HΓ₂]".
  iApply (ewp_bind ([AppRCtx (subst_map vs e₁)])); first done.
  iApply (ewp_mono with "[HΓ₂]").
  { by iApply He₂. }
  iIntros (v) "Hτv //=". iModIntro.
  iApply (ewp_bind ([AppLCtx v])); first done.
  iApply (ewp_mono with "[HΓ₁]").
  { by iApply He₁. }
  iIntros (w) "Hτκw //=". iModIntro; by iApply "Hτκw". 
Qed.

Lemma sem_typed_pair `{!irisGS eff_lang Σ} Γ₁ Γ₂ e₁ e₂ τ ρ κ: 
  Γ₁ ⊨ e₁ : ρ : τ →
  Γ₂ ⊨ e₂ : ρ : κ →
  Γ₁ ++ Γ₂ ⊨ (e₁,e₂)%E : ρ : τ * κ.
Proof.
  iIntros (He₁ He₂ vs) "HΓ₁₂ //=".
  rewrite env_sem_typed_app.
  iDestruct "HΓ₁₂" as "[HΓ₁ HΓ₂]".
  iApply (ewp_bind ([PairRCtx (subst_map vs e₁)])); first done.
  iApply (ewp_mono with "[HΓ₂]").
  { by iApply He₂. }
  iIntros (v) "Hτv //=". iModIntro.
  iApply (ewp_bind ([PairLCtx v])); first done.
  iApply (ewp_mono with "[HΓ₁]").
  { by iApply He₁. }
  iIntros (w) "Hκw //=". iModIntro. ewp_pure_steps.
  iExists w, v. iFrame. by iPureIntro.
Qed.

Lemma sem_typed_pair_elim `{!irisGS eff_lang Σ} Γ₁ Γ₂ x₁ x₂ e₁ e₂ τ ρ κ ι: 
  ~In x₁ (ctx_dom Σ Γ₂) ->
  ~In x₂ (ctx_dom Σ Γ₂) ->
  x₁ ≠ x₂ ->
  Γ₁ ⊨ e₁ : ρ : (τ * κ) →
  (x₁, τ) :: (x₂, κ) :: Γ₂ ⊨ e₂ : ρ : ι →
  Γ₁ ++ Γ₂ ⊨ (let: (x₁, x₂) := e₁ in e₂)%E : ρ : ι.
Proof.
  iIntros (HIn₁ HIn₂ Hnex₁₂ He₁ He₂ vs) "HΓ₁₂ //=".
  rewrite env_sem_typed_app.
  iDestruct "HΓ₁₂" as "[HΓ₁ HΓ₂]".
  ewp_pure_steps.
  set ex1x2 := (λ: x₁ x₂, subst_map (binder_delete x₂ 
                                    (binder_delete x₁ vs)) e₂)%V. 
  iApply (ewp_bind ([AppLCtx ex1x2])); first done.
  iApply (ewp_bind ([AppRCtx pair_elim])); first done.
  iApply (ewp_mono with "[HΓ₁]").
  { by iApply He₁. }
  iIntros (v) "Hτκv". iModIntro. simpl in *. 
  unfold pair_elim. ewp_pure_steps.
  iDestruct "Hτκv" as "(%v₁ & %v₂ & -> & Hτ & Hκ)".
  unfold ex1x2. ewp_pure_steps. 
  destruct (decide _) as [[]|[]]; [|split; [done|congruence]].
  rewrite delete_commute -subst_map_insert -delete_insert_ne
    ;last congruence.
  rewrite <- subst_map_insert.
  iApply He₂. simpl. iSplitL "Hτ".
  { iExists v₁. iFrame. iPureIntro. 
    rewrite lookup_insert_ne; last done.
    by rewrite lookup_insert. }
  iSplitL "Hκ".
  { iExists v₂. iFrame. iPureIntro. 
    by rewrite lookup_insert. }
  by repeat (iApply env_sem_typed_insert; first done).
Qed.

Lemma sem_typed_if `{!irisGS eff_lang Σ} Γ₁ Γ₂ e₁ e₂ e₃ ρ τ: 
  Γ₁ ⊨ e₁ : ρ : 𝔹 →
  Γ₂ ⊨ e₂ : ρ : τ →
  Γ₂ ⊨ e₃ : ρ : τ →
  Γ₁ ++ Γ₂ ⊨ (if: e₁ then e₂ else e₃)%E : ρ : τ.
Proof.
  iIntros (He₁ He₂ He₃ vs) "HΓ₁₂ //=".
  rewrite env_sem_typed_app.
  iDestruct "HΓ₁₂" as "[HΓ₁ HΓ₂]".
  iApply (ewp_bind ([IfCtx (subst_map vs e₂) (subst_map vs e₃)])); first done.
  iApply (ewp_mono with "[HΓ₁]").
  { by iApply He₁. }
  iIntros (v) "(%b & ->)". iModIntro. simpl.
  destruct b; ewp_pure_steps.
  - by iApply He₂.
  - by iApply He₃.
Qed.

