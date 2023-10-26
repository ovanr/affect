
From iris.proofmode Require Import base tactics.
From iris.base_logic.lib Require Import iprop invariants.

(* Hazel Reasoning *)
From hazel.program_logic Require Import weakest_precondition 
                                        tactics 
                                        shallow_handler_reasoning 
                                        deep_handler_reasoning 
                                        state_reasoning.

(* Local imports *)
From affine_tes.lib Require Import base.
From affine_tes.lang Require Import hazel.
From affine_tes.lang Require Import subst_map.
From affine_tes.logic Require Import iEff.
From affine_tes.logic Require Import sem_def.
From affine_tes.logic Require Import sem_types.
From affine_tes.logic Require Import sem_env.
From affine_tes.logic Require Import sem_sub_typing.
From affine_tes.logic Require Import sem_operators.


Open Scope bi_scope.
Open Scope stdpp_scope.
Open Scope ieff_scope.


Lemma lambdas_is_lambda domΓ x e :
  exists y e', (λ*λ: domΓ , x, e)%E = (λ: y, e')%E.
Proof.
  destruct domΓ; [by exists x, e|].
  by exists s, (ctx_lambda domΓ (λ: x, e)%E).  
Qed.

Lemma app_mult_cons e₁ es e₂ :
  (e₁ <_ es _> e₂)%E = (e₁ <_ es ++ [e₂] _>)%E.
Proof.
  revert e₁. induction es; first done. simpl.
  intros ?. apply IHes.
Qed.

Lemma ctx_lambda_env_dom_nil {Σ} e :
  e = (λ*: env_dom ([] : env Σ), e)%E.
Proof. by rewrite env_dom_nil. Qed.

Lemma app_mult_env_dom_nil {Σ} e :
  e = (e <_ map Var (env_dom ([] : env Σ)) _>)%E.
Proof. by rewrite env_dom_nil. Qed.

Lemma map_subst_map_singleton_ne Γ x v :
  x ∉ Γ → map (subst_map {[x:=v]} ∘ Var) Γ = map Var Γ.
Proof.
  intros H. induction Γ; first done. simpl.
  edestruct (not_elem_of_cons Γ) as [[] _]; first done.
  rewrite lookup_singleton_ne; last done. by rewrite IHΓ.
Qed.

Lemma map_map_subst_map Γ ws :
  map (subst_map ws) (map Var Γ) = map (subst_map ws ∘ Var) Γ.
Proof. by rewrite map_map. Qed.

Lemma ewp_bind_app_mult `{heapGS Σ} e ρ (vs : list val) Φ : 
  EWP e <| ρ |> {{ w, EWP w <_ map Val vs _> <| ρ |> {{ Φ }} }} -∗
  EWP e <_ map Val vs _> <| ρ |> {{ Φ }}.
Proof. 
  iIntros "He".
  pose k vs := (map AppLCtx (rev vs)).
  assert (Hfill : ∀ vs e, fill (k vs) e = (e <_ map Val vs _>)%E).
  { clear. rewrite /k. induction vs; first done; simpl; intros ?. 
    rewrite map_app fill_app. simpl. by rewrite IHvs. }
  iApply (ewp_bind (k vs)); first done. Unshelve.
  + iApply (ewp_mono with "[He]"); [iApply "He"|].
    iIntros (u) "Hu !>". by rewrite Hfill.
  + rewrite /k. induction vs; simpl; first done.
    rewrite map_app.
    assert (neutral_app : ∀ xs ys, NeutralEctx xs → NeutralEctx ys → NeutralEctx (xs ++ ys)).
    { clear. induction xs; intros ???; first done. simpl. 
      destruct (Forall_cons_1 _ _ _ neutral_ectx) as [Ha Hxs].
      apply ConsCtx_neutral; first done. by apply IHxs. }
    apply neutral_app; first done. simpl. apply _.
Qed.

Lemma subst_map_var `{heapGS Σ} Γ vs :
  ⟦ Γ ⟧ vs -∗
  ∃ ws, ⌜map (subst_map vs ∘ Var) (env_dom Γ) = map Val ws ⌝.
Proof.
  iIntros "HΓ". iInduction Γ as [|[x τ] Γ'] "IH"; [by iExists []|].
  rewrite env_dom_cons. simpl.
  iDestruct "HΓ" as "[%m (%Hrw & _ & HΓ')]". rewrite Hrw.
  iDestruct ("IH" with "HΓ'") as "(%ws & %HIH)". 
  iExists (m :: ws). iPureIntro. simpl. by f_equal.
Qed.

Lemma ewp_bind_app_mult' `{heapGS Σ} Δ e ρ vs Φ : 
  ⟦ Δ ⟧ vs -∗
  (⟦ Δ ⟧ vs -∗ EWP e <| ρ |> {{ w, EWP w <_ map (subst_map vs ∘ Var) (env_dom Δ) _> <| ρ |> {{ Φ }} }}) -∗
  EWP e <_ map (subst_map vs ∘ Var) (env_dom Δ) _> <| ρ |> {{ Φ }}.
Proof. 
  iIntros "HΔ He".
  iDestruct (subst_map_var with "HΔ") as "[%vs' %Hrwvs']". 
  rewrite Hrwvs'. iApply ewp_bind_app_mult. rewrite -Hrwvs'.
  by iApply "He".
Qed.

Lemma ewp_bind_inv_lambda `{heapGS Σ} (x y : string) e v ρ (vs : list val) Φ : 
  EWP (λ: y, if decide (x ≠ y) then subst x v e else e)%V <_ map Val vs _> <| ρ |> {{ Φ }} -∗
  EWP (λ: x y, e)%V v <_ map Val vs _> <| ρ |> {{ Φ }}.
Proof. 
  iIntros "H". 
  iApply ewp_bind_app_mult. ewp_pure_steps.
  destruct (decide (x ≠ y)) as [H'|H'].
  { rewrite decide_True; last (split; intros ?; by simplify_eq). iApply "H". }
  rewrite decide_False; last (intros [_ H'']; apply H'; intros ?; apply H''; simplify_eq). 
  iApply "H".
Qed.


Lemma ewp_app_mult' `{heapGS Σ} (z : string) κ ρ (Γ' : env Σ) vs e Φ :
  let Γ := (z, κ) :: Γ' in
  □ env_sem_typed Γ vs -∗
  (EWP (subst_map (vs ∖ (delete (env_dom Γ) vs)) e) <| ρ |> {{ Φ }}) -∗
  EWP (λλ*: z, env_dom Γ', e)%V <_ map (subst_map vs ∘ Var) (env_dom Γ) _> <| ρ |> {{ Φ }}.
Proof.
  iIntros "/= #HΓ He". iInduction Γ' as [|[y τ] Γ''] "IH" forall (z e κ).
  - rewrite env_dom_cons /=. iDestruct "HΓ" as "[%m (%Hrw & _ & _)] /=". 
    rewrite Hrw delete_list_delete /= (difference_delete _ _ _ m); last done.
    rewrite map_difference_diag insert_empty env_dom_nil /=.
    ewp_value_or_step. by rewrite subst_map_singleton.
  - iDestruct "HΓ" as "[%m (%Hrwm & _ & [%n (%Hrwn & Hτ & HΓ'')])]". 
    rewrite !(env_dom_cons z). iSimpl. rewrite Hrwm. 
    iSimpl in "He". 
    iDestruct (subst_map_var ((y, τ) :: Γ'') with "[HΓ'']") as "(%ws & %Hrw')"; 
      first solve_env.
    rewrite Hrw' {2}env_dom_cons. iSimpl. iApply ewp_bind_inv_lambda. 
    rewrite -Hrw' -subst_map_singleton. 
    destruct (decide (z = y)).
    + rewrite decide_False; last (simplify_eq; auto). subst.
      iApply "IH"; first solve_env. 
      by rewrite env_dom_cons !delete_list_cons delete_idemp.
    + rewrite decide_True; last done.
      rewrite subst_map_ctx_lambda. iSimpl.
      set e' := subst_map (delete _ {[z :=m]}) e.
      iSpecialize ("IH" $! y e' τ). iApply "IH"; first solve_env. 
      rewrite /e'. 
      rewrite subst_map_union (env_dom_cons y).
      replace (vs ∖ delete (z :: y :: env_dom Γ'') vs) with 
              (delete (env_dom Γ'') {[z := m]} ∪ vs ∖ delete (y :: env_dom Γ'') vs); first done.
      destruct (decide (z ∈ env_dom Γ'')).
      * rewrite delete_list_singleton; last done. 
        rewrite map_empty_union (delete_list_delete_cons z (y :: env_dom Γ'')); first done. 
        apply elem_of_cons. auto.
      * rewrite delete_list_singleton_ne; last done.
        apply map_eq. intros ?. destruct (decide (i = z)).
        { subst. rewrite (lookup_union_Some_l _ _ _ m); last (apply lookup_insert).
          symmetry. by rewrite lookup_difference_delete. }
        rewrite lookup_union_r; last (by eapply lookup_singleton_ne). 
        rewrite (lookup_difference_delete_ne z i vs (delete (y :: env_dom Γ'') vs)); auto.
Qed.

Lemma ewp_app_mult `{heapGS Σ} (z : string) κ (Γ' : env Σ) ρ vs e Φ :
  let Γ := (z, κ) :: Γ' in
  env_sem_typed Γ vs -∗
  (env_sem_typed Γ vs -∗ EWP (subst_map (vs ∖ (delete (env_dom Γ) vs)) e) <| ρ |> {{ Φ }}) -∗
  EWP (λλ*: z, env_dom Γ', e)%V <_ map (subst_map vs ∘ Var) (env_dom Γ) _> <| ρ |> {{ Φ }}.
Proof.
  iIntros (Γ) "HΓ He".
  iDestruct (env_sem_typed_mk_moved _ Γ with "HΓ") as "[#HΓM HΓ]".
  rewrite /Γ. iSimpl in "HΓM".
  iDestruct "HΓM" as "[%m (? & ? & HΓ'M)]". 
  set Γ'M := map (prod_map id (const Moved)) Γ'.
  assert (HΓ'eq : env_dom Γ' = env_dom Γ'M).
  { clear - Γ' Γ'M. induction Γ' as [|[]]; first done. 
    rewrite /Γ'M !env_dom_cons /=. f_equal. apply IHΓ'. }
  rewrite env_dom_cons !HΓ'eq.
  iApply (ewp_app_mult' _ _ with "[HΓ'M]"); first (iModIntro; iExists m; by iFrame "#").
  rewrite env_dom_cons. by iApply "He".
Qed.
