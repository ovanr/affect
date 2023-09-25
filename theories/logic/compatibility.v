
(* compatibility.v *)

(* 
  The compatibility lemmas are what one gets when the syntactic typing judgment
  is replaced with a semantic typing judgment.
*)

From iris.proofmode Require Import base tactics.
From iris.base_logic.lib Require Import iprop invariants.

(* Hazel Reasoning *)
From program_logic Require Import weakest_precondition 
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

(* Helper Tactics *)

Ltac ewp_bottom := iApply ewp_os_prot_mono; 
                   [by iApply iEff_le_bottom|].

  
(* Semantic typing rules. *)

Section compatibility.

  Context `{!heapGS Σ}.
  
  Lemma sem_typed_val Γ τ v : 
    ⊨ᵥ v : τ -∗ Γ ⊨ v : ⟨⟩ : τ ⊨ Γ.
  Proof.
    iIntros "#Hv !# %Φ %vs HΓ HΦ /=".
    iApply ewp_value. iApply "HΦ". iIntros "{$Hv} {$HΓ}".
  Qed.

  (* Base rules *)
  
  Lemma sem_typed_unit Γ : 
    ⊢ Γ ⊨ #() : ⟨⟩ : () ⊨ Γ.
  Proof.
    iIntros (Φ vs) "!# HΓ₁ HΦ //=". iApply ewp_value. 
    iApply "HΦ". by iFrame.
  Qed.
  
  Lemma sem_typed_bool Γ (b : bool) : 
    ⊢ Γ ⊨ #b : ⟨⟩ : 𝔹 ⊨ Γ.
  Proof.
    iIntros (Φ vs) "!# HΓ₁ HΦ //=". iApply ewp_value. 
    iApply "HΦ". iSplitR; first (iExists b); done.
  Qed.
  
  Lemma sem_typed_int Γ (i : Z) : 
    ⊢ Γ ⊨ #i : ⟨⟩ : ℤ ⊨ Γ.
  Proof.
    iIntros (Φ vs) "!# HΓ₁ HΦ //=". iApply ewp_value. 
    iApply "HΦ". iSplitR; first (iExists i); done.
  Qed.
  
  Lemma sem_typed_var Γ x τ : 
    ⊢ (x, τ) :: Γ ⊨ x : ⟨⟩ : τ ⊨ Γ.
  Proof.
    iIntros (Φ vs) "!# /= [%v (-> & Hτ & HΓ₁)] HΦ //=". 
    iApply ewp_value. iApply "HΦ". iFrame.
  Qed.

  Lemma sem_typed_closure x e τ ρ κ :
    [(x, τ)] ⊨ e : ρ : κ ⊨ [] -∗ 
    ⊨ᵥ (λ: x, e) : (τ -{ ρ }-> κ).
  Proof.
      iIntros "#He !# %v !# Hv /=".
      ewp_pure_steps. rewrite -subst_map_singleton.
      iApply ("He" with "[Hv] []"); first solve_env.
      iIntros (w) "[Hκ _] {$Hκ}".
  Qed.

  Lemma sem_typed_closure_to_unrestricted x e τ ρ κ :
    ⊨ᵥ (λ: x, e) : (τ -{ ρ }-∘ κ) -∗
    ⊨ᵥ (λ: x, e) : (τ -{ ρ }-> κ).
  Proof. iIntros "#He !# !#". iApply "He". Qed.

  (* Subsumption rule *)
  
  Lemma sem_typed_sub Γ₁ Γ₁' Γ₂ Γ₂' e ρ ρ' τ τ':
    Γ₁  ≤E Γ₁' →
    Γ₂' ≤E Γ₂ →
    ρ'  ≤R ρ → 
    τ'  ≤T τ →
    Γ₁' ⊨ e : ρ' : τ' ⊨ Γ₂' -∗ Γ₁ ⊨ e : ρ : τ ⊨ Γ₂.
  Proof.
    iIntros (HΓ₁le HΓ₂le Hρle Hτle) "#He !# %Φ %vs HΓ₁ HΦ //=".
    rewrite HΓ₁le.
    iApply ewp_os_prot_mono.
    { iApply Hρle. }
    iApply ("He" with "HΓ₁").
    iIntros (v) "[Hτ' HΓ₂]". iApply "HΦ".
    rewrite HΓ₂le. iFrame.
    by iApply Hτle.
  Qed. 
  
  (* Convenient Subsumption rules *)
  Lemma sem_typed_sub_ty τ' τ Γ₁ Γ₂ e ρ :
  τ' ≤T τ →
  (Γ₁ ⊨ e : ρ : τ' ⊨ Γ₂) -∗ Γ₁ ⊨ e : ρ : τ ⊨ Γ₂.
  Proof.
    iIntros (Hτ).
    iApply (sem_typed_sub Γ₁ Γ₁ Γ₂ Γ₂ _ ρ ρ);
      (apply sig_le_refl || apply env_le_refl || done). 
  Qed.

  Lemma sem_typed_sub_sig ρ ρ' Γ₁ Γ₂ e τ :
    ρ' ≤R ρ →
    (Γ₁ ⊨ e : ρ' : τ ⊨ Γ₂) -∗ Γ₁ ⊨ e : ρ : τ ⊨ Γ₂.
  Proof.
    iIntros (Hρ).
    iApply (sem_typed_sub Γ₁ Γ₁ Γ₂ Γ₂ _ ρ ρ' τ τ);
      (apply sig_le_refl || apply env_le_refl || apply ty_le_refl || done).
  Qed.

  Lemma sem_typed_sub_nil Γ₁ Γ₂ e τ ρ :
    (Γ₁ ⊨ e : ⟨⟩ : τ ⊨ Γ₂) -∗ Γ₁ ⊨ e : ρ : τ ⊨ Γ₂.
  Proof. iApply sem_typed_sub_sig. apply sig_le_nil. Qed.
  
  Lemma sem_typed_sub_env Γ₁ Γ₁' Γ₂ e ρ τ :
    Γ₁ ≤E Γ₁' →
    (Γ₁' ⊨ e : ρ : τ ⊨ Γ₂) -∗ Γ₁ ⊨ e : ρ : τ ⊨ Γ₂.
  Proof.
    iIntros (HΓ₁).
    iApply (sem_typed_sub Γ₁ Γ₁' Γ₂ Γ₂ _ ρ ρ τ τ);
      (apply sig_le_refl || apply env_le_refl || apply ty_le_refl || done).
  Qed.

  Lemma sem_typed_swap_second Γ₁ Γ₂ x y e ρ τ₁ τ₂ κ :
    ((y, τ₂) :: (x, τ₁) :: Γ₁ ⊨ e : ρ : κ ⊨ Γ₂) -∗ 
    ((x, τ₁) :: (y, τ₂) :: Γ₁ ⊨ e : ρ : κ ⊨ Γ₂).
  Proof.
    iIntros "He".
    iApply sem_typed_sub_env; [apply env_le_swap_second|iApply "He"].
  Qed.

  Lemma sem_typed_swap_third Γ₁ Γ₂ x y z e ρ τ₁ τ₂ τ₃ κ :
    ((z, τ₃) :: (x, τ₁) :: (y, τ₂) :: Γ₁ ⊨ e : ρ : κ ⊨ Γ₂) -∗ 
    ((x, τ₁) :: (y, τ₂) :: (z, τ₃) :: Γ₁ ⊨ e : ρ : κ ⊨ Γ₂).
  Proof.
    iIntros "He".
    iApply sem_typed_sub_env; [|iApply "He"].
    eapply env_le_trans; apply env_le_swap_third.
  Qed.

  Lemma sem_typed_weaken Γ₁ Γ₂ x e ρ τ κ :
    (Γ₁ ⊨ e : ρ : κ ⊨ Γ₂) -∗ ((x, τ) :: Γ₁ ⊨ e : ρ : κ ⊨ Γ₂).
  Proof.
    iIntros "He".
    iApply sem_typed_sub_env; [apply env_le_weaken|iApply "He"].
  Qed.

  (* λ-calculus rules *)

  Lemma sem_typed_afun Γ₁ Γ₂ x e τ ρ κ: 
    x ∉ (env_dom Γ₁) →
    x ∉ (env_dom Γ₂) →
    (x,τ) ::? Γ₁ ⊨ e : ρ : κ ⊨ [] -∗
    Γ₁ ++ Γ₂ ⊨ (λ: x, e) : ⟨⟩ : (τ -{ ρ }-∘ κ) ⊨ Γ₂.
  Proof.
    iIntros (??) "#He !# %Φ %vs HΓ₁₂ HΦ //=".
    ewp_pure_steps. iApply "HΦ". 
    iDestruct (env_sem_typed_app with "HΓ₁₂") as "[HΓ₁ $]".
    iIntros (w) "Hτ ". ewp_pure_steps. destruct x; simpl.
    - iApply ("He" with "HΓ₁ []").
      iIntros (v) "//= [Hκ _] {$Hκ}". 
    - rewrite -subst_map_insert.
      iApply ("He" with "[HΓ₁ Hτ] []"); first solve_env. 
      iIntros (v) "//= [Hκ _]". by iApply "Hκ".
  Qed.

  Lemma sem_typed_ufun Γ₁ Γ₂ f x e τ ρ κ:
    x ∉ (env_dom Γ₁) →
    f ∉ (env_dom Γ₁) →
    match (x,f) with (BNamed x, BNamed f) => x ≠ f | _ => True%type end →
    copy_env Γ₁ →
    (x, τ) ::? (f, τ -{ ρ }-> κ) ::? Γ₁ ⊨ e : ρ : κ ⊨ [] -∗
    Γ₁ ++ Γ₂ ⊨ (rec: f x := e) : ⟨⟩ : (τ -{ ρ }-> κ) ⊨ Γ₂.
  Proof.
    iIntros (??? HcpyΓ₁) "#He !# %Φ %vs HΓ₁₂ HΦ //=".
    ewp_pure_steps. iApply "HΦ".
    iDestruct (env_sem_typed_app with "HΓ₁₂") as "[HΓ₁ $]".
    rewrite HcpyΓ₁. iDestruct "HΓ₁" as "#HΓ₁".
    iLöb as "IH".
    iIntros (w) "!# Hτ". ewp_pure_steps. destruct f; destruct x; simpl.
    - iApply ("He" with "HΓ₁ []").
      iIntros (v) "[Hκ _] {$Hκ}".
    - rewrite -subst_map_insert. 
      iApply ("He" with "[HΓ₁ Hτ] []"); first solve_env.
      iIntros (v) "//= [Hκ _] {$Hκ}".
    - rewrite -subst_map_insert.
      iApply ("He" with "[HΓ₁ Hτ] []"); first solve_env.
      iIntros (v) "//= [Hκ _] {$Hκ}".
    - rewrite subst_subst_ne; last done.
      rewrite -subst_map_insert.
      rewrite -delete_insert_ne; last done.
      rewrite -subst_map_insert.
      iApply ("He" with "[Hτ] []"); [iExists w; iFrame; iSplit|].
      + iPureIntro. rewrite lookup_insert_ne; last done.
        by rewrite lookup_insert.
      + iExists _. iFrame "#"; iSplit; [iPureIntro; apply lookup_insert|].
        by do 2 (rewrite -env_sem_typed_insert; last done).
      + iIntros (v) "[Hκ _]". by iApply "Hκ".
  Qed.

  Lemma ewp_bind_inv_lambda (x y : string) e v (vs : list val) Φ : 
    EWP (λ: y, if decide (x ≠ y) then subst x v e else e)%V <_ map Val vs _> {{ Φ }} -∗
    EWP (λ: x y, e)%V v <_ map Val vs _> {{ Φ }}.
  Proof. 
    pose k vs := (map AppLCtx (rev vs)).
    assert (Hfill : ∀ vs e, fill (k vs) e = (e <_ map Val vs _>)%E).
    { clear. rewrite /k. induction vs; first done; simpl; intros ?. 
      rewrite map_app fill_app. simpl. by rewrite IHvs. }
    iIntros "H". 
    iApply (ewp_bind (k vs)); first done. Unshelve.
    + ewp_pure_steps. rewrite Hfill.
      destruct (decide (x ≠ y)) as [H'|H'].
      { rewrite decide_True; last (split; intros ?; by simplify_eq). iApply "H". }
      rewrite decide_False; last (intros [_ H'']; apply H'; intros ?; apply H''; simplify_eq). 
      iApply "H".
    + rewrite /k. induction vs; simpl; first done.
      rewrite map_app.
      assert (neutral_app : ∀ xs ys, NeutralEctx xs → NeutralEctx ys → NeutralEctx (xs ++ ys)).
      { clear. induction xs; intros ???; first done. simpl. 
        destruct (Forall_cons_1 _ _ _ neutral_ectx) as [Ha Hxs].
        apply ConsCtx_neutral; first done. by apply IHxs. }
      apply neutral_app; first done. simpl. apply _.
  Qed.

  Lemma subst_map_var Γ vs :
    env_sem_typed Γ vs -∗
    ∃ ws, ⌜map (subst_map vs ∘ Var) (env_dom Γ) = map Val ws ⌝.
  Proof.
    iIntros "HΓ". iInduction Γ as [|[x τ] Γ'] "IH"; [by iExists []|].
    rewrite env_dom_cons. simpl.
    iDestruct "HΓ" as "[%m (-> & _ & HΓ')]".
    iDestruct ("IH" with "HΓ'") as "(%ws & %HIH)". 
    iExists (m :: ws). iPureIntro. simpl. by f_equal.
  Qed.

  Lemma ewp_app_mult (z : string) x κ (Γ' : env Σ) vs e Φ :
    let Γ := (z, κ) :: Γ' in
    □ env_sem_typed Γ vs -∗
    EWP (subst_map (vs ∖ (delete (env_dom Γ) vs)) (λ: x, e)) {{ Φ }} -∗
    EWP (λλ*λ: z, env_dom Γ', x , e)%V <_ map (subst_map vs ∘ Var) (env_dom Γ) _> {{ Φ }}.
  Proof. 
    iIntros "#HΓ He". iInduction Γ' as [|[y τ] Γ''] "IH" forall (z e κ).
    - rewrite env_dom_cons /=. iDestruct "HΓ" as "[%m (%Hrw & _ & _)] /=". 
      rewrite Hrw delete_list_delete /= (difference_delete _ _ _ m); last done.
      rewrite map_difference_diag insert_empty env_dom_nil /=.
      ewp_value_or_step. destruct (decide (BNamed z = x)).
      + rewrite decide_False; last tauto; subst. simpl.
        by rewrite delete_singleton subst_map_empty.
      + rewrite decide_True; last auto. destruct x; simpl;
          [|rewrite delete_singleton_ne; last congruence];
        by rewrite subst_map_singleton.
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
        set e' := subst_map (binder_delete x (delete (env_dom Γ'') {[z := m]})) e.
        iSpecialize ("IH" $! y e' τ). iApply "IH"; first solve_env. 
        rewrite /e'. iSimpl. 
        rewrite subst_map_union -binder_delete_union (env_dom_cons y).
        replace (vs ∖ delete (z :: y :: env_dom Γ'') vs) with 
                (delete (env_dom Γ'') {[z := m]} ∪ vs ∖ delete (y :: env_dom Γ'') vs); first done.
        destruct (decide (z ∈ env_dom Γ'')).
        * rewrite delete_list_singleton; last done. 
          rewrite map_empty_union (delete_list_delete_cons z (y :: env_dom Γ'')); first done. 
          apply elem_of_cons. auto.
        * rewrite delete_list_singleton_ne; last done.
          apply map_eq. intros ?. destruct (decide (i = z)).
          { subst. rewrite lookup_union_l; [|eapply mk_is_Some; apply lookup_singleton].
            by rewrite lookup_singleton lookup_difference_delete. }
          rewrite lookup_union_r; last (by eapply lookup_singleton_ne). 
          rewrite (lookup_difference_delete_ne z i vs (delete (y :: env_dom Γ'') vs)); auto.
  Qed.

  Lemma sem_typed_sufun Γ₁ Γ₂ Δ₁ Δ₂ x e τ ρ κ:
    x ∉ (env_dom Γ₁) → x ∉ (env_dom Δ₁) → x ∉ (env_dom Γ₂) →
    env_dom Δ₂ ⊆ env_dom Δ₁ →
    env_dom Γ₁ ## env_dom Δ₁ →
    (x, τ) ::? Δ₁ ++ Γ₁ ⊨ e : ρ : κ ⊨ Δ₂ ++ Γ₁ -∗
    Γ₁ ++ Γ₂ ⊨ (λ*λ: env_dom Δ₁, x, e) : ⟨⟩ : (τ ∘-{ ρ ; Δ₁ ; Δ₂ }-> κ) ⊨ Γ₂.
  Proof.
    iIntros (?????) "#He !# %Φ %vs HΓ₁₂ HΦ /=".
    iDestruct (env_sem_typed_app with "HΓ₁₂") as "[HΓ₁ HΓ₂]".
    iApply (ewp_mono _ _ (λ v, (τ ∘-{ ρ; Δ₁; Δ₂ }-> κ) v ∗ env_sem_typed Γ₂ vs) 
            with "[HΓ₁ HΓ₂]"); [|iIntros (w); iIntros "? !>"; by iApply "HΦ"].
    iApply (ewp_frame_r with "[HΓ₁] HΓ₂").
    rewrite subst_map_ctx_lambda. iSimpl.
    destruct Δ₁ as [|[z ι] Δ₁'].
    - rewrite env_dom_nil delete_list_nil. iSimpl. ewp_pure_steps.
      replace Δ₂ with ([] : env Σ) 
          by (symmetry; apply (map_eq_nil fst); by apply list_nil_subseteq). 
      iLöb as "IH". iApply sem_ty_suarr_unfold.
      iIntros (u ws) "_ Hτ /=". rewrite env_dom_nil. iSimpl.
      ewp_pure_steps. destruct x as [|x]. iSimpl.
      + iApply ("He" with "HΓ₁"). iIntros "%v [Hκ HΓ₁] {$Hκ}".
        iSpecialize ("IH" with "HΓ₁"). solve_env.
      + iSimpl. rewrite -subst_map_insert.
        iApply ("He" with "[Hτ HΓ₁]"); iSimpl; first solve_env. 
        iIntros "%v [Hκ HΓ₁] {$Hκ}".
        rewrite -env_sem_typed_insert; last done.
        iSpecialize ("IH" with "HΓ₁"); solve_env.
    - rewrite env_dom_cons /=. ewp_pure_steps.
      iLöb as "IH". iApply sem_ty_suarr_unfold.
      iIntros (u ws) "HΔ₁ Hτ". 
      iApply (ewp_bind [AppLCtx _]); first done. 
      iApply ewp_os_prot_mono; [iApply sig_le_nil|].
      set Δ₁ := (z, ι) :: Δ₁'.
      set e' := subst_map (binder_delete x (delete (z :: env_dom Δ₁') vs)) e.
      rewrite (env_sem_typed_mk_moved _ Δ₁). iDestruct "HΔ₁" as "[#HΔ₁M HΔ₁]".
      rewrite /Δ₁. iSimpl in "HΔ₁M".
      iDestruct "HΔ₁M" as "[%m (? & ? & HΔ₁'M)]". 
      set Δ₁'M := map (prod_map id (const Moved)) Δ₁'.
      assert (HΔ₁'eq : env_dom Δ₁' = env_dom Δ₁'M).
      { clear - Δ₁' Δ₁'M. induction Δ₁' as [|[]]; first done. 
        rewrite /Δ₁'M !env_dom_cons /=. f_equal. apply IHΔ₁'. }
      rewrite {1}env_dom_cons !HΔ₁'eq.
      iApply (ewp_app_mult with "[HΔ₁'M]"); first (iModIntro; iExists m; by iFrame "#").
      rewrite -/Δ₁. iSimpl. rewrite env_dom_cons -!HΔ₁'eq. ewp_pure_steps.
      rewrite /e' subst_map_union -binder_delete_union subst'_subst_map_insert -(env_dom_cons _ ι).
      iApply ("He" with "[HΔ₁ Hτ HΓ₁]"); destruct x as [|x]. 
      + rewrite app_comm_cons env_sem_typed_app -/Δ₁. iSimpl.
        iSplitL "HΔ₁".
        { rewrite (env_sem_typed_difference_delete Δ₁); last reflexivity. 
          by rewrite (env_sem_typed_delete_union Δ₁); last reflexivity. }
        { rewrite (env_sem_typed_delete_disjoint Γ₁ Δ₁); last done. 
        by iApply env_sem_typed_union. }
      + iExists u. iSplitL ""; first (iPureIntro; apply lookup_insert). iFrame.
        rewrite app_comm_cons -/Δ₁.
        rewrite -(env_sem_typed_insert (Δ₁ ++ Γ₁) _ x u);
          last (rewrite env_dom_app; by eapply not_elem_of_app).
        rewrite env_sem_typed_app.
        rewrite (env_sem_typed_difference_delete Δ₁); last reflexivity.
        rewrite (env_sem_typed_delete_union Δ₁); last reflexivity. iFrame.
        rewrite (env_sem_typed_delete_disjoint Γ₁ Δ₁); last done. 
        by iApply (env_sem_typed_union Γ₁). 
      + iIntros (w) "[$ HΔ₂Γ₁] /=". 
        iDestruct (env_sem_typed_app with "HΔ₂Γ₁") as "[HΔ₂ HΓ₁]".
        rewrite -(env_sem_typed_delete_union Δ₂ Δ₁); last done. 
        rewrite -(env_sem_typed_difference_delete Δ₂ Δ₁); last done. iFrame. 
        iApply "IH".
        rewrite (env_sem_typed_union_difference_delete Γ₁ Δ₁); last done.
        by iApply env_sem_typed_delete_disjoint.
      + iIntros (w) "[$ HΔ₂Γ₁] /=". 
        iDestruct (env_sem_typed_app with "HΔ₂Γ₁") as "[HΔ₂ HΓ₁]".
        assert (x ∉ env_dom Δ₂).
        { intros ?. apply H0. 
          destruct (elem_of_subseteq (env_dom Δ₂) (env_dom Δ₁)) as [H' _]. by apply H'. }
        do 2 (rewrite -env_sem_typed_insert; last done).
        rewrite -(env_sem_typed_delete_union Δ₂ Δ₁); last done. 
        rewrite -(env_sem_typed_difference_delete Δ₂ Δ₁); last done. iFrame. 
        iApply "IH".
        rewrite (env_sem_typed_union_difference_delete Γ₁ Δ₁); last done.
        by iApply env_sem_typed_delete_disjoint.
  Qed.

  Lemma sem_typed_app Γ₁ Γ₂ Γ₃ e₁ e₂ τ ρ κ: 
    Γ₂ ⊨ e₁ : ρ : (τ -{ ρ }-∘ κ) ⊨ Γ₃ -∗
    Γ₁ ⊨ e₂ : ρ : τ ⊨ Γ₂ -∗
    Γ₁ ⊨ (e₁ e₂) : ρ : κ ⊨ Γ₃.
  Proof.
    iIntros "#He₁ #He₂ !# %Φ %vs HΓ₁ HΦ //=".
    iApply (ewp_bind ([AppRCtx (subst_map vs e₁)])); first done.
    iApply ("He₂" with "HΓ₁").
    iIntros (v) "[Hτ HΓ₂] //=".
    iApply (ewp_bind ([AppLCtx v])); first done.
    iApply ("He₁" with "HΓ₂").
    iIntros (w) "[Hτκw HΓ₃] //=". 
    iApply (ewp_mono with "[Hτκw Hτ]").
    { iApply ("Hτκw" with "Hτ"). }
    iIntros (u) "Hκ !>". iApply "HΦ". iFrame.
  Qed.
  
  Lemma sem_typed_suapp Γ₁ Γ₂ Δ₁ Δ₂ f e₂ τ ρ κ: 
    Γ₁ ⊨ e₂ : ρ : τ ⊨ (f, τ ∘-{ ρ ; Δ₁ ; Δ₂ }-> κ) :: Δ₁ ++ Γ₂ -∗
    Γ₁ ⊨ (f <_ map Var (env_dom Δ₁) _> e₂) : ρ : κ ⊨ (f, τ ∘-{ ρ ; Δ₁ ; Δ₂  }-> κ) :: Δ₂ ++ Γ₂. 
  Proof.
    iIntros "#He₂ !# %Φ %vs HΓ₁ HΦ /=".
    rewrite subst_map_app_mult. simpl.
    iApply (ewp_bind ([AppRCtx _])); first done.
    iApply ("He₂" with "HΓ₁").
    iIntros (v) "/= [Hτ [%w (%Hrw & Hw & HΓ₂)]] /=". rewrite Hrw.
    iDestruct (env_sem_typed_app with "HΓ₂") as "[HΔ₁ HΓ₂]".
    rewrite sem_ty_suarr_unfold.
    iApply (ewp_mono with "[Hτ HΔ₁ Hw]").
    - iSpecialize ("Hw" $! v vs with "HΔ₁ Hτ").
      rewrite -map_map. iApply "Hw". 
    - iIntros (u) "[Hκ [HΔ₂ Hw]] !>". iApply "HΦ". iFrame.
      iExists w. rewrite env_sem_typed_app. by iFrame.
  Qed.

  Lemma sem_typed_let Γ₁ Γ₂ Γ₃ x e₁ e₂ τ ρ κ: 
    x ∉ (env_dom Γ₂) → x ∉ (env_dom Γ₃) →
    Γ₁ ⊨ e₁ : ρ : τ ⊨ Γ₂ -∗
    (x, τ) :: Γ₂ ⊨ e₂ : ρ : κ ⊨ Γ₃ -∗
    Γ₁ ⊨ (let: x := e₁ in e₂) : ρ : κ ⊨ Γ₃.
  Proof.
    iIntros (??) "#He₁ #He₂ !# %Φ %vs HΓ₁ HΦ /=".
    iApply (ewp_bind ([AppRCtx _])); first done.
    iApply ("He₁" with "HΓ₁").
    iIntros (v) "[Hτ HΓ₂] /=". ewp_pure_steps.
    rewrite -subst_map_insert.
    iApply ("He₂" with "[Hτ HΓ₂]"); first solve_env.
    iIntros (w) "[Hκ HΓ₃]". iApply "HΦ". iFrame.
    by iApply env_sem_typed_insert.
  Qed.

  Lemma sem_typed_seq Γ₁ Γ₂ Γ₃ e₁ e₂ τ ρ κ: 
    Γ₁ ⊨ e₁ : ρ : τ ⊨ Γ₂ -∗
    Γ₂ ⊨ e₂ : ρ : κ ⊨ Γ₃ -∗
    Γ₁ ⊨ (e₁ ;; e₂) : ρ : κ ⊨ Γ₃.
  Proof.
    iIntros "#He₁ #He₂ !# %Φ %vs HΓ₁ HΦ /=".
    iApply (ewp_bind ([AppRCtx _])); first done.
    iApply ("He₁" with "HΓ₁").
    iIntros (v) "[Hτ HΓ₂] /=". ewp_pure_steps.
    iApply ("He₂" with "HΓ₂").
    iIntros (w) "[Hκ HΓ₃]". iApply "HΦ". iFrame.
  Qed.

  Lemma sem_typed_pair Γ₁ Γ₂ Γ₃ e₁ e₂ τ ρ κ: 
    Γ₂ ⊨ e₁ : ρ : τ ⊨ Γ₃ -∗
    Γ₁ ⊨ e₂ : ρ : κ ⊨ Γ₂ -∗
    Γ₁ ⊨ (e₁,e₂) : ρ : (τ × κ) ⊨ Γ₃.
  Proof.
    iIntros "#He₁ #He₂ !# %Φ %vs HΓ₁ HΦ //=".
    iApply (ewp_bind ([PairRCtx (subst_map vs e₁)])); first done.
    iApply ("He₂" with "HΓ₁").
    iIntros (v) "[Hτv HΓ₂] //=".
    iApply (ewp_bind ([PairLCtx v])); first done.
    iApply ("He₁" with "HΓ₂").
    iIntros (w) "[Hκw HΓ₃] //=". ewp_pure_steps.
    iApply "HΦ". iFrame. iExists w, v. iFrame. by iPureIntro.
  Qed.
  
  Lemma sem_typed_pair_elim Γ₁ Γ₂ Γ₃ x₁ x₂ e₁ e₂ τ ρ κ ι: 
    x₁ ∉ (env_dom Γ₂) → x₂ ∉ (env_dom Γ₂) →
    x₁ ∉ (env_dom Γ₃) → x₂ ∉ (env_dom Γ₃) →
    x₁ ≠ x₂ →
    Γ₁ ⊨ e₁ : ρ : (τ × κ) ⊨ Γ₂ -∗
    (x₁, τ) :: (x₂, κ) :: Γ₂ ⊨ e₂ : ρ : ι ⊨ Γ₃ -∗
    Γ₁ ⊨ (let: (x₁, x₂) := e₁ in e₂) : ρ : ι ⊨ Γ₃.
  Proof.
    iIntros (?????) "#He₁ #He₂ !# %Φ %vs HΓ₁ HΦ //=".
    ewp_pure_steps.
    set ex1x2 := (λ: x₁ x₂, subst_map (binder_delete x₂ 
                                      (binder_delete x₁ vs)) e₂)%V. 
    iApply (ewp_bind ([AppLCtx ex1x2; AppRCtx pair_elim])); first done.
    iApply ("He₁" with "HΓ₁").
    iIntros (v) "[Hτκv HΓ₂] //=". 
    unfold pair_elim. ewp_pure_steps.
    iDestruct "Hτκv" as "(%v₁ & %v₂ & -> & Hτ & Hκ)".
    unfold ex1x2. ewp_pure_steps. 
    destruct (decide _) as [[]|[]]; [|split; [done|congruence]].
    rewrite delete_commute -subst_map_insert -delete_insert_ne; last congruence.
    rewrite -subst_map_insert.
    iApply ("He₂" with "[Hτ Hκ HΓ₂]").
    - iExists v₁. iFrame. iSplitL "".
      { rewrite lookup_insert_ne; last done. by rewrite lookup_insert. }
      iExists v₂. iFrame; iSplitL ""; [by rewrite lookup_insert|].
      by do 2 (rewrite -env_sem_typed_insert; last done).
    - iIntros (v) "[Hιv HΓ₃]". iApply "HΦ". iFrame.
      rewrite -(env_sem_typed_insert _ _ x₂ v₂); last done.
      by rewrite -(env_sem_typed_insert _ _ x₁ v₁).
  Qed.
  
  Lemma sem_typed_left_inj Γ₁ Γ₂ e τ ρ κ: 
    Γ₁ ⊨ e : ρ : τ ⊨ Γ₂ -∗
    Γ₁ ⊨ InjL e : ρ : (τ + κ) ⊨ Γ₂.
  Proof.
    iIntros "#He !# %Φ %vs HΓ₁ HΦ //=".
    iApply (ewp_bind [InjLCtx]); first done.
    iApply ("He" with "HΓ₁").
    iIntros (v) "[Hv HΓ₂] //=".
    ewp_pure_steps. iApply "HΦ".
    iFrame. iExists v. iLeft. by iFrame.
  Qed.

  Lemma sem_typed_right_inj Γ₁ Γ₂ e τ ρ κ: 
    Γ₁ ⊨ e : ρ : κ ⊨ Γ₂ -∗
    Γ₁ ⊨ InjR e : ρ : (τ + κ) ⊨ Γ₂.
  Proof.
    iIntros "#He !# %Φ %vs HΓ₁ HΦ //=".
    iApply (ewp_bind [InjRCtx]); first done.
    iApply ("He" with "HΓ₁").
    iIntros (v) "[Hv HΓ₂] //=".
    ewp_pure_steps. iApply "HΦ".
    iFrame. iExists v. iRight. by iFrame.
  Qed.

  Lemma sem_typed_match Γ₁ Γ₂ Γ₃ e₁ x e₂ e₃ τ ρ κ ι: 
    x ∉ env_dom Γ₂ →
    x ∉ env_dom Γ₃ →
    Γ₁ ⊨ e₁ : ρ : (τ + κ) ⊨ Γ₂ -∗
    (x, τ) :: Γ₂ ⊨ e₂ : ρ : ι ⊨ Γ₃ -∗
    (x, κ) :: Γ₂ ⊨ e₃ : ρ : ι ⊨ Γ₃ -∗
    Γ₁ ⊨ match: e₁ with InjL x => e₂ | InjR x => e₃ end : ρ : ι ⊨ Γ₃.
  Proof.
    iIntros (??) "#He₁ #He₂ #He₃ !# %Φ %vs HΓ₁ HΦ //=".
    iApply (ewp_bind [CaseCtx _ _]); first done.
    iApply ("He₁" with "HΓ₁").
    iIntros (v) "[(%w & [(-> & Hτ)|(-> & Hκ)]) HΓ₂] //="; 
      ewp_pure_steps; rewrite -subst_map_insert.
    - iApply ("He₂" with "[HΓ₂ Hτ] [HΦ]"); first solve_env.
        iIntros (v) "[Hτι HΓ₃] //=". iApply "HΦ"; solve_env. 
    - iApply ("He₃" with "[HΓ₂ Hκ] [HΦ]"); first solve_env.
        iIntros (v) "[Hτι HΓ₃] //=". iApply "HΦ"; solve_env.
  Qed.

  Lemma sem_typed_none Γ₁ τ: 
    ⊢ Γ₁ ⊨ NONE : ⟨⟩ : Option τ ⊨ Γ₁.
  Proof.
    iIntros. iApply sem_typed_left_inj. iApply sem_typed_unit. 
  Qed.

  Lemma sem_typed_some Γ₁ Γ₂ e ρ τ: 
    Γ₁ ⊨ e : ρ : τ ⊨ Γ₂ -∗ 
    Γ₁ ⊨ SOME e : ρ : Option τ ⊨ Γ₂.
  Proof.
    iIntros "He". iApply sem_typed_right_inj. iApply "He".
  Qed.

  Lemma sem_typed_match_option Γ₁ Γ₂ Γ₃ e₁ x e₂ e₃ τ ρ κ ι: 
    x ∉ env_dom Γ₂ →
    x ∉ env_dom Γ₃ →
    Γ₁ ⊨ e₁ : ρ : (τ + κ) ⊨ Γ₂ -∗
    Γ₂ ⊨ e₂ : ρ : ι ⊨ Γ₃ -∗
    (x, κ) :: Γ₂ ⊨ e₃ : ρ : ι ⊨ Γ₃ -∗
    Γ₁ ⊨ match: e₁ with NONE => e₂ | SOME x => e₃ end : ρ : ι ⊨ Γ₃.
  Proof.
    iIntros (??) "#He₁ #He₂ #He₃ !# %Φ %vs HΓ₁ HΦ //=".
    iApply (ewp_bind [CaseCtx _ _]); first done.
    iApply ("He₁" with "HΓ₁").
    iIntros (v) "[(%w & [(-> & Hτ)|(-> & Hκ)]) HΓ₂] //="; ewp_pure_steps.
    - iApply ("He₂" with "HΓ₂ HΦ").
    - rewrite -subst_map_insert.
      iApply ("He₃" with "[HΓ₂ Hκ] [HΦ]"); first solve_env.
        iIntros (v) "[Hτι HΓ₃] //=". iApply "HΦ"; solve_env.
  Qed.

  Lemma sem_typed_bin_op Γ₁ Γ₂ Γ₃ e₁ e₂ op τ κ ι ρ: 
    typed_bin_op op τ κ ι →
    Γ₂ ⊨ e₁ : ρ : τ ⊨ Γ₃ -∗
    Γ₁ ⊨ e₂ : ρ : κ ⊨ Γ₂ -∗
    Γ₁ ⊨ BinOp op e₁ e₂ : ρ : ι ⊨ Γ₃.
  Proof.
    iIntros (Hop) "#He₁ #He₂ !# %Φ %vs HΓ₁ HΦ //=".
    iApply (ewp_bind [BinOpRCtx _ _]); first done.
    iApply ("He₂" with "HΓ₁").
    iIntros (v) "[Hv HΓ₂] //=". 
    iApply (ewp_bind [BinOpLCtx _ _]); first done.
    iApply ("He₁" with "HΓ₂").
    iIntros (w) "[Hw HΓ₃] //=". 
    destruct op; inversion_clear Hop;
      iDestruct "Hv" as "(%n1 & ->)";
      iDestruct "Hw" as "(%n2 & ->)";
      ewp_pure_steps; try done; iApply "HΦ"; eauto.
  Qed.
  
  Lemma sem_typed_if Γ₁ Γ₂ Γ₃ e₁ e₂ e₃ ρ τ: 
    Γ₁ ⊨ e₁ : ρ : 𝔹 ⊨ Γ₂ -∗
    Γ₂ ⊨ e₂ : ρ : τ ⊨ Γ₃ -∗
    Γ₂ ⊨ e₃ : ρ : τ ⊨ Γ₃ -∗
    Γ₁ ⊨ (if: e₁ then e₂ else e₃) : ρ : τ ⊨ Γ₃.
  Proof.
    iIntros "#He₁ #He₂ #He₃ !# %Φ %vs HΓ₁ HΦ //=".
    iApply (ewp_bind [IfCtx (subst_map vs e₂) (subst_map vs e₃)]) ;first done.
    iApply ("He₁" with "HΓ₁").
    iIntros (v) "((%b & ->) & HΓ₂) //=".
    destruct b; ewp_pure_steps.
    - iApply ("He₂" with "HΓ₂"). iFrame.
    - iApply ("He₃" with "HΓ₂"). iFrame.
  Qed.
  
  (* Type abstraction and application *)
  Lemma sem_typed_TLam Γ₁ Γ₂ ρ e C : 
    (∀ α, Γ₁ ⊨ e : ρ : C α ⊨ []) -∗
    Γ₁ ++ Γ₂ ⊨ (Λ: e) : ⟨⟩ : (∀T: α , { ρ } , C α)%T ⊨ Γ₂.
  Proof.
    iIntros "#He !# %Φ %vs HΓ₁₂ HΦ //=".
    iDestruct (env_sem_typed_app with "HΓ₁₂") as "[HΓ₁ HΓ₂]".
    ewp_pure_steps. iApply "HΦ". 
    iIntros "{$HΓ₂} %α //=". ewp_pure_steps.
    iApply ("He" with "HΓ₁ []"). 
    iIntros (w) "[HC _] {$HC}".
  Qed.

  Lemma sem_typed_TApp Γ₁ Γ₂ e ρ τ C : 
    Γ₁ ⊨ e : ρ : (∀T: α , { ρ } , C α) ⊨ Γ₂ -∗
    Γ₁ ⊨ e <_> : ρ : C τ ⊨ Γ₂. 
  Proof.
    iIntros "#He !# %Φ %vs HΓ₁ HΦ /=".
    iApply (ewp_bind [AppLCtx _]); first done.
    iApply ("He" with "HΓ₁").
    iIntros "%w [Hw HΓ₂] //=".
    iApply (ewp_mono with "[Hw]").
    { iApply "Hw". }
    iIntros (u) "HC !>". iApply "HΦ". iFrame.
  Qed.

  (* Signature abstraction and application *)
  Lemma sem_typed_SLam Γ₁ Γ₂ e C : 
    (∀ θ, Γ₁ ⊨ e : θ : C θ ⊨ []) -∗
    Γ₁ ++ Γ₂ ⊨ (Λ: e) : ⟨⟩ : (∀S: θ , C θ)%T ⊨ Γ₂.
  Proof.
    iIntros "#He !# %Φ %vs HΓ₁₂ HΦ /=".
    iDestruct (env_sem_typed_app with "HΓ₁₂") as "[HΓ₁ HΓ₂]".
    ewp_pure_steps.
    iApply "HΦ". iFrame.
    iIntros (ρ). ewp_pure_steps.
    iApply ("He" with "HΓ₁ []").
    iIntros (v) "[HC _] {$HC}".
  Qed.

  Lemma sem_typed_SApp Γ₁ Γ₂ e ρ C : 
    Γ₁ ⊨ e : ρ : (∀S: θ , C θ) ⊨ Γ₂ -∗
    Γ₁ ⊨ e <_> : ρ : C ρ ⊨ Γ₂. 
  Proof.
    iIntros "#He !# %Φ %vs HΓ₁ HΦ /=".
    iApply (ewp_bind [AppLCtx _]); first done.
    iApply ("He" with "HΓ₁ [HΦ]").
    iIntros (v) "[HC HΓ₂] /=".
    iApply (ewp_mono with "HC").
    iIntros (w) "HCρ !>". iApply "HΦ". iFrame.
  Qed.

  (* Existential type packing and unpacking *)
  Lemma sem_typed_pack Γ₁ Γ₂ ρ e C τ :
    Γ₁ ⊨ e : ρ : C τ ⊨ Γ₂ -∗
    Γ₁ ⊨ (pack: e) : ρ : (∃: α, C α) ⊨ Γ₂. 
  Proof.
    iIntros "#He %Φ %vs !# HΓ₁ HΦ //=".
    iApply (ewp_bind [AppRCtx _]); first done.
    iApply ("He" with "HΓ₁").
    iIntros (v) "[Hτv HΓ₂] //=".
    unfold exist_pack. ewp_pure_steps.
    iApply "HΦ". iFrame. by iExists τ. 
  Qed.

  Lemma sem_typed_unpack Γ₁ Γ₂ Γ₃ x ρ e₁ e₂ κ C :
    x ∉ env_dom Γ₂ → x ∉ env_dom Γ₃ →
    Γ₁ ⊨ e₁ : ρ : (∃: α, C α) ⊨ Γ₂ -∗
    (∀ τ, (x, C τ) :: Γ₂ ⊨ e₂ : ρ : κ ⊨ Γ₃) -∗
    Γ₁ ⊨ (unpack: x := e₁ in e₂) : ρ : κ ⊨ Γ₃.
  Proof.
    iIntros (??) "#He₁ #He₂ %Φ %vs !# HΓ₁ HΦ //=".
    iApply (ewp_bind [AppRCtx _]); first done.
    iApply ("He₁" with "HΓ₁").
    iIntros (w) "[(%τ & Hτw) HΓ₂] //=". unfold exist_unpack.
    ewp_pure_steps. rewrite -subst_map_insert.
    iApply ("He₂" with "[HΓ₂ Hτw]"); first solve_env.
    iIntros (u) "[Hκ HΓ₃]". iApply "HΦ"; solve_env.
  Qed.

  (* Recursive type rules *)
  Lemma sem_typed_fold Γ₁ Γ₂ e ρ C `{NonExpansive C}:
    Γ₁ ⊨ e : ρ : (C (μ: α, C α)) ⊨ Γ₂ -∗
    Γ₁ ⊨ (fold: e) : ρ : (μ: α, C α) ⊨ Γ₂.
  Proof.
    iIntros "#He %Φ %vs !# HΓ₁ HΦ //=".
    iApply (ewp_bind [AppRCtx _]); first done. 
    iApply ("He" with "HΓ₁").
    iIntros "%w [HC HΓ₂] //=". 
    unfold rec_fold. ewp_pure_steps. iApply "HΦ".
    iFrame. by iApply sem_ty_rec_unfold. 
  Qed.

  Lemma sem_typed_unfold Γ₁ Γ₂ e ρ C `{NonExpansive C}:
    Γ₁ ⊨ e : ρ : (μ: α, C α) ⊨ Γ₂ -∗
    Γ₁ ⊨ (unfold: e) : ρ : (C (μ: α, C α)) ⊨ Γ₂.
  Proof.
    iIntros "#He %Φ %vs !# HΓ₁ HΦ //=".
    iApply (ewp_bind [AppRCtx _]); first done. 
    iApply ("He" with "HΓ₁").
    iIntros "%w [Hμ HΓ₂] //=". 
    rewrite sem_ty_rec_unfold. 
    unfold rec_unfold. ewp_pure_steps. 
    iApply "HΦ". iFrame.
  Qed.

  (* List type rules *)
  Lemma sem_typed_nil Γ τ: 
    ⊢ Γ ⊨ NIL : ⟨⟩ : List τ ⊨ Γ.
  Proof.
    iIntros "!# %Φ %vs HΓ HΦ //=". 
    ewp_pure_steps. unfold sem_ty_list. iApply "HΦ".
    rewrite sem_ty_rec_unfold. iIntros "{$HΓ} !>".
    unfold ListF. iExists #(). by iLeft.
  Qed.
  
  Lemma sem_typed_cons Γ₁ Γ₂ Γ₃ e₁ e₂ ρ τ: 
    Γ₂ ⊨ e₁ : ρ : τ ⊨ Γ₃-∗
    Γ₁ ⊨ e₂ : ρ : List τ ⊨ Γ₂-∗
    Γ₁ ⊨ CONS e₁ e₂ : ρ : List τ ⊨ Γ₃.
  Proof.
    iIntros "#He₁ #He₂ !# %Φ %vs HΓ₁ HΦ //=". 
    iApply (ewp_bind [InjRCtx; PairRCtx _]); first done.
    iApply ("He₂" with "HΓ₁").
    iIntros (l) "[Hl HΓ₂] //=".
    iApply (ewp_bind [InjRCtx; PairLCtx _]); first done.
    iApply ("He₁" with "HΓ₂").
    iIntros (x) "[Hx HΓ₃] //=". ewp_pure_steps.
    iApply "HΦ".
    unfold sem_ty_list. rewrite !sem_ty_rec_unfold.
    iIntros "{$HΓ₃} !>". iExists (x,l)%V. iRight. iSplit; first done.
    iExists x, l. iFrame; iSplit; first done.
    by rewrite sem_ty_rec_unfold. 
  Qed.
  
  Lemma sem_typed_match_list Γ₁ Γ₂ Γ₃ x xs e₁ e₂ e₃ ρ τ κ :
    x ∉ (env_dom Γ₂) -> xs ∉ (env_dom Γ₂) ->
    x ∉ (env_dom Γ₃) -> xs ∉ (env_dom Γ₃) ->
    x ≠ xs ->
    Γ₁ ⊨ e₁ : ρ : List τ ⊨ Γ₂ -∗
    Γ₂ ⊨ e₂ : ρ : κ ⊨ Γ₃ -∗
    (x, τ) :: (xs, List τ) :: Γ₂ ⊨ e₃ : ρ : κ ⊨ Γ₃ -∗
    Γ₁ ⊨ list-match: e₁ with 
            CONS x => xs => e₃ 
          | NIL => e₂
         end : ρ : κ ⊨ Γ₃.
  Proof.
    iIntros (?????) "#He₁ #He₂ #He₃ !# %Φ %vs HΓ₁ HΦ //=".
    iApply (ewp_bind [CaseCtx _ _]); first done. 
    iApply (sem_typed_unfold with "He₁ HΓ₁ [HΦ]"). simpl.
    iIntros (v₁) "[Hl HΓ₂]". 
    iDestruct "Hl" as "(%v' & [[-> ->]|(-> & (%w₁ & %w₂ & -> & Hτ & Hμ))])"; 
    ewp_pure_steps.
    { iApply ("He₂" with "[$HΓ₂]"). iFrame. }
    rewrite lookup_delete. simpl.
    rewrite decide_False; [|by intros [_ []]].
    rewrite decide_True; last done. ewp_pure_steps.
    rewrite decide_True; [|split; congruence].
    rewrite delete_commute -subst_map_insert delete_commute.
    rewrite insert_delete_insert. rewrite subst_map_insert.
    rewrite subst_subst_ne; [|congruence]. rewrite delete_commute.
    rewrite -subst_map_insert -delete_insert_ne; try congruence.
    rewrite -subst_map_insert. 
    iApply ("He₃" with "[Hμ Hτ HΓ₂]"); first solve_env.
    { rewrite env_sem_typed_insert; last done; solve_env. }
    iIntros (u) "[Hκ HΓ₃]". iApply "HΦ". iFrame.
    rewrite -(env_sem_typed_insert _ _ x w₁); last done.
    by rewrite -(env_sem_typed_insert _ _ xs w₂).
  Qed.

  (* Reference rules *)
  
  Lemma sem_typed_alloc Γ₁ Γ₂ e ρ τ: 
    Γ₁ ⊨ e : ρ : τ ⊨ Γ₂ -∗
    Γ₁ ⊨ ref e : ρ : Ref τ ⊨ Γ₂.
  Proof.
    iIntros "#He !# %Φ %vs HΓ₁ HΦ //=".
    iApply (ewp_bind [AllocCtx]); first done. simpl.
    iApply ("He" with "HΓ₁").
    iIntros (v) "[Hτ HΓ₂]".
    iApply ewp_alloc. iIntros "!> %l Hl !>". iApply "HΦ"; solve_env.
  Qed.
  
  Lemma sem_typed_load Γ x τ: 
    ⊢ ((x, Ref τ) :: Γ ⊨ !x : ⟨⟩ : τ ⊨ (x, Ref Moved) :: Γ).
  Proof.
    iIntros "%Φ %vs !# //= [%v (%Hrw & (%w & -> & (%l & Hl & Hτ)) & HΓ)] HΦ".
    rewrite Hrw. iApply (ewp_load with "Hl").
    iIntros "!> Hl !>". iApply "HΦ". solve_env.
  Qed.
  
  Lemma sem_typed_load_copy Γ x τ: 
    copy_ty τ →
    ⊢ ((x, Ref τ) :: Γ ⊨ !x : ⟨⟩ : τ ⊨ (x, Ref τ) :: Γ).
  Proof.
    iIntros (Hcpy) "%Φ %vs !# //= [%v (%Hrw & (%w & -> & (%l & Hl & Hτ)) & HΓ)] HΦ".
    rewrite Hrw. iApply (ewp_load with "Hl").
    rewrite Hcpy. iDestruct "Hτ" as "#Hτ".
    iIntros "!> Hl !>". iApply "HΦ". solve_env.
  Qed.

  Lemma sem_typed_store Γ₁ Γ₂ x e ρ τ κ ι: 
    (x, Ref τ) :: Γ₁ ⊨ e : ρ : ι ⊨ (x, Ref κ) :: Γ₂ -∗
    (x, Ref τ) :: Γ₁ ⊨ (x <- e) : ρ : () ⊨ (x, Ref ι) :: Γ₂.
  Proof.
    iIntros "#He !# %Φ %vs //= HΓ₁' HΦ //=".
    iApply (ewp_bind [StoreRCtx _]); first done. simpl.
    iApply ("He" with "HΓ₁'").
    iIntros (w) "[Hι [%v (%Hrw & (%l & -> & (% & Hl & Hκ)) & HΓ₂)]] /=". 
    rewrite Hrw. iApply (ewp_store with "Hl"). 
    iIntros "!> Hl !>". iApply "HΦ"; solve_env. 
  Qed.
  
  (* Effect handling rules *)
  
  Lemma sem_typed_do Γ₁ Γ₂ e ι κ: 
    Γ₁ ⊨ e : (ι ⇒ κ) : ι ⊨ Γ₂ -∗
    Γ₁ ⊨ (do: e) : (ι ⇒ κ) : κ ⊨ Γ₂.
  Proof.
    iIntros "#He !# %Φ %vs HΓ₁ HΦ //=". 
    iApply (ewp_bind [DoCtx OS]); first done.
    iApply ("He" with "HΓ₁").
    iIntros (v) "[Hι HΓ₂] //=".
    iApply ewp_do_os. rewrite upcl_sem_sig_eff.
    iExists v. iFrame. iSplitR; first done.
    iIntros (b) "Hκ". iApply "HΦ". iFrame.
  Qed.

  (* Limitation: 
     In the typing rule for the effect branch, the continuation
     has the additional information that when called it returns
     a value of type τ' and that env_sem_typed Γ₂ vs holds.
     But because the type signature of the handler is simply:
     ι ⊸ (k -{ ρ }-∘ τ' -{ ρ }-∘ τ 
     this extra env_sem_typed Γ₂ vs is ignored and cannot be
     used inside the handler, so we have some loss of information.
   *)
  Lemma sem_typed_shallow_try Γ₁ Γ₂ Γ₃ Γ' w k e h r ι κ τ τ' ρ': 
    w ∉ env_dom Γ₂ → w ∉ env_dom Γ' → k ∉ env_dom Γ' →
    w ∉ env_dom Γ₃ → k ∉ env_dom Γ₃ → w ≠ k →
    let ρ := (ι ⇒ κ)%R in
    Γ₁ ⊨ e : ρ : τ' ⊨ Γ₂ -∗
    (w, ι) :: (k, κ -{ ρ }-∘ τ') :: Γ' ⊨ h : ρ' : τ ⊨ Γ₃ -∗
    (w, τ') :: Γ₂ ++ Γ' ⊨ r : ρ' : τ ⊨ Γ₃ -∗
    Γ₁ ++ Γ' ⊨ (shallow-try: e with effect (λ: w k, h) | return (λ: w, r) end) : ρ' : τ ⊨ Γ₃.
  Proof.
    iIntros (??????) "%ρ #He #Hh #Hr !# %Φ %vs HΓ₁' HΦ //=".
    iDestruct (env_sem_typed_app with "HΓ₁'") as "[HΓ₁ HΓ']".
    ewp_pure_steps.
    iApply (ewp_try_with _ _ _ (λ v, τ' v ∗ env_sem_typed Γ₂ vs) 
                    with "[HΓ₁] [HΓ' HΦ]"). 
    { iApply ("He" with "HΓ₁"). iIntros "* [Hτ' HΓ₂] {$Hτ' $HΓ₂}". }
    iSplit; [|iSplit; iIntros (v c)];
    last (iIntros "?"; by rewrite upcl_bottom).
    - iIntros (v) "[Hv HΓ₂] //=". ewp_pure_steps.
      rewrite -subst_map_insert.
      iApply ("Hr" with "[HΓ₂ HΓ' Hv]"). 
      { iExists v. rewrite env_sem_typed_app. solve_env. }
      + iIntros (u) "[Hw HΓ₃] //=". iApply "HΦ". solve_env.
    - rewrite upcl_sem_sig_eff.
      iIntros "(%a & -> & Ha & Hκb) //=". ewp_pure_steps.
      rewrite decide_True; [|split; first done; by injection].
      rewrite subst_subst_ne; last done.
      rewrite -subst_map_insert -delete_insert_ne; last done.
      rewrite -subst_map_insert.
      iApply ("Hh" with "[HΓ' Hκb Ha]"); first solve_env.
      + iSplitR "HΓ'"; [|by (do 2 (rewrite -env_sem_typed_insert; try done))].
        iIntros (b) "Hb". 
        iApply (ewp_mono with "[Hb Hκb]"); [by iApply "Hκb"|].
        iIntros (?) "[? _] !> //=". 
      + iIntros (u) "[Hu HΓ₃]". iApply "HΦ". iFrame.
        rewrite -(env_sem_typed_insert _ _ w a); last done.
        by rewrite -(env_sem_typed_insert _ _ k c).
  Qed.
  
  Lemma sem_typed_deep_try Γ₁ Γ' Γ₂ Γ₃ e w k h r ρ' ι κ τ τ':
    w ∉ env_dom Γ₂ → w ∉ env_dom Γ' → w ∉ env_dom Γ₃ →
    k ∉ env_dom Γ' → k ∉ env_dom Γ₃ → w ≠ k → copy_env Γ' →
    let ρ := (ι ⇒ κ)%R in
    Γ₁ ⊨ e : ρ : τ ⊨ Γ₂ -∗
    (w, ι) :: (k, κ -{ ρ' }-∘ τ') :: Γ' ⊨ h : ρ' : τ' ⊨ Γ₃ -∗
    (w, τ) :: Γ₂ ++ Γ' ⊨ r : ρ' : τ' ⊨ Γ₃ -∗
    Γ₁ ++ Γ' ⊨ (deep-try: e with effect (λ: w k, h) | return (λ: w, r) end) : ρ' : τ' ⊨ Γ₃.
  Proof.
    iIntros (?????? Hcpy) "%ρ #He #Hh #Hr !# %Φ %vs HΓ₁' HΦ //=".
    iDestruct (env_sem_typed_app with "HΓ₁'") as "[HΓ₁ HΓ']".
    rewrite Hcpy. iDestruct "HΓ'" as "#HΓ'".
    ewp_pure_steps. iApply (ewp_mono with "[HΓ₁] [HΦ]").
    2: { simpl. iIntros "* H !>". iApply "HΦ". iApply "H". }
    iApply (ewp_deep_try_with _ _ _ (λ v, τ v ∗ env_sem_typed Γ₂ vs) 
                         with "[HΓ₁] []").
    { iApply ("He" with "HΓ₁"). iIntros "* H {$H}". }
    iLöb as "IH". rewrite !deep_handler_unfold.
    iSplit; [|iSplit; iIntros (v c)];
    last (iIntros "?"; by rewrite upcl_bottom).
    - iIntros (v) "[Hv HΓ₂] //=". ewp_pure_steps.
      rewrite -subst_map_insert. 
      iApply ("Hr" with "[Hv HΓ₂ HΓ']").
      { iExists v. rewrite env_sem_typed_app. solve_env. }
      + iIntros (?) "[Hτ' HΓ₃] {$Hτ'}"; solve_env.
    - rewrite upcl_sem_sig_eff.
      iIntros "(%a & -> & Ha & Hκb)". ewp_pure_steps.
      rewrite decide_True; [|split; first done; by injection].
      rewrite subst_subst_ne; last done.
      rewrite -subst_map_insert -delete_insert_ne; last done.
      rewrite -subst_map_insert.
      iApply ("Hh" with "[Ha HΓ' Hκb]").
      + solve_env. 
        iSplitL "Hκb"; [|by (do 2 (rewrite -env_sem_typed_insert; try done))].
        iIntros (b) "Hb". iApply (ewp_mono with "[Hb Hκb] []").
        { iApply ("Hκb" with "Hb []"). rewrite !deep_handler_unfold. iApply "IH". }
        iIntros "* [Hτ' _] !> {$Hτ'}". 
      + iIntros (u) "[Hτ' HΓ₃] {$Hτ'}".
        rewrite -(env_sem_typed_insert _ _ w a); last done.
        by rewrite -(env_sem_typed_insert _ _ k c).
    Qed.

  Lemma sem_typed_mapcont Γ₁ Γ' Γ₂ e e₁ e₂ e₃ w r ρ' ι κ τ τ':
    w ∉ env_dom Γ₂ → w ∉ env_dom Γ' → r ∉ env_dom Γ' → 
    let ρ := (ι ⇒ κ)%R in
    Γ₁ ⊨ e : ρ : τ ⊨ Γ₂ -∗
    (w, ι) :: Γ' ⊨ e₁ : ρ' : τ' + κ ⊨ Γ' -∗
    (r, τ') :: Γ' ⊨ e₂ : ρ' : τ' ⊨ Γ' -∗
    (w, τ) :: Γ₂ ++ Γ' ⊨ e₃ : ρ' : τ' ⊨ Γ' -∗
    Γ₁ ++ Γ' ⊨ (mapcont-try: e with  map (λ: w, e₁) 
                                   | cont (λ: r, e₂) 
                                   | return (λ: w, e₃) end) : ρ' : τ' ⊨ Γ'.
  Proof. 
    iIntros (???) "%ρ #He #He₁ #He₂ #He₃ !# %Φ %vs HΓ₁Γ' HΦ /=".
    rewrite env_sem_typed_app. iDestruct "HΓ₁Γ'" as "[HΓ₁ HΓ']".
    ewp_pure_steps.
    rewrite (delete_commute _ "c" "m")
            (delete_commute _ "w" "m")
            (delete_commute _ "k" "m")
            lookup_delete /=
            (delete_commute _ "k" "w")
            (delete_commute _ "m" "w")
            !lookup_delete /=
            (delete_commute _ "k" "c")
            (delete_commute _ "m" "c")
            (delete_commute _ "w" "c")
            (delete_commute _ "w" "c")
            lookup_delete /=
            (delete_commute _ "m" "k")
            (delete_commute _ "w" "k")
            (delete_commute _ "w" "k")
            (delete_commute _ "c" "k")
            lookup_delete /=.
    iApply (ewp_mono with "[HΓ₁ HΓ'] [HΦ]"). 
    2: { simpl. iIntros "* H !>". iApply "HΦ". iApply "H". }
    iApply (ewp_deep_try_with _ _ _ (λ v, τ v ∗ env_sem_typed Γ₂ vs) with "[HΓ₁] [HΓ']").
    { iApply ("He" with "HΓ₁"). iIntros "* H {$H}". }
    iLöb as "IH". rewrite !deep_handler_unfold.
    iSplit; [|iSplit; iIntros (v c)];
    last (iIntros "?"; by rewrite upcl_bottom).
    - iIntros (v) "[Hv HΓ₂] //=". ewp_pure_steps.
      rewrite -subst_map_insert. 
      iApply ("He₃" with "[Hv HΓ₂ HΓ']"); last solve_env.
      iExists v. rewrite env_sem_typed_app. solve_env.
    - rewrite upcl_sem_sig_eff.
      iIntros "(%a & -> & Ha & Hκb)". ewp_pure_steps.
      rewrite -subst_map_insert /=.
      iApply ("He₁" with "[Ha HΓ']"); first solve_env.
      + iIntros (v') "[(%v & [(-> & Hτ')|(-> & Hκ)]) HΓ']"; 
          ewp_pure_steps; first solve_env.
        ewp_bind_rule. simpl.
        iApply (ewp_mono with "[Hκb Hκ HΓ']").
        { iApply ("Hκb" with "Hκ"). iNext. 
          rewrite !deep_handler_unfold. iApply "IH"; solve_env. }
        iIntros (u) "[Hτ' HΓ'] !> /=".
        ewp_pure_steps. rewrite -subst_map_insert.
        iApply ("He₂" with "[Hτ' HΓ']"); solve_env.
  Qed.

  Lemma sem_typed_mapcont_alt Γ₁ Γ' Γ₂ Γ₃ e e₁ e₂ e₃ w k r ρ' ι ι' κ τ τ':
    w ∉ env_dom Γ₂ → w ∉ env_dom Γ' → w ∉ env_dom Γ₃ → k ∉ env_dom Γ₃ → r ∉ env_dom Γ' → 
    w ≠ k → copy_env Γ₃ →
    let ρ := (ι ⇒ κ)%R in
    Γ₁ ⊨ e : ρ : τ ⊨ Γ₂ -∗
    (w, ι) :: Γ' ++ Γ₃ ⊨ e₁ : ρ' : ι' ⊨ Γ' -∗
    (w, ι') :: (k, κ -{ ρ' }-∘ τ') :: Γ₃ ⊨ e₂ : ρ' : τ' ⊨ [] -∗
    (w, τ) :: Γ₂ ++ Γ' ++ Γ₃ ⊨ e₃ : ρ' : τ' ⊨ [] -∗
    Γ₁ ++ Γ' ++ Γ₃ ⊨ (mapcont-try-alt: e with map (λ: w, e₁)
                                            | cont (λ: w k, e₂)
                                            | return (λ: w, e₃) end) : ρ' : τ' ⊨ [].
  Proof. 
    iIntros (?????? Hcpy) "%ρ #He #He₁ #He₂ #He₃ !# %Φ %vs HΓ₁Γ'Γ₃ HΦ /=".
    rewrite !env_sem_typed_app. iDestruct "HΓ₁Γ'Γ₃" as "(HΓ₁ & HΓ' & HΓ₃)".
    rewrite Hcpy. iDestruct "HΓ₃" as "#HΓ₃".
    ewp_pure_steps.
    rewrite (delete_commute _ "w" "c")
            (delete_commute _ "k" "c")
            lookup_delete /= 
            (delete_commute _ "w" "m")
            (delete_commute _ "k" "m")
            (delete_commute _ "c" "m")
            !lookup_delete /= 
            (delete_commute _ "k" "w")
            (delete_commute _ "c" "w")
            (delete_commute _ "m" "w")
            lookup_delete /= 
            (delete_commute _ "c" "k")
            (delete_commute _ "m" "k")
            (delete_commute _ "w" "k")
            lookup_delete /=.
    iApply (ewp_mono with "[HΓ₁ HΓ'] [HΦ]"). 
    2: { simpl. iIntros "* H !>". iApply "HΦ". iApply "H". }
    ewp_pure_steps.
    iApply (ewp_deep_try_with _ _ _ (λ v, τ v ∗ env_sem_typed Γ₂ vs) with "[HΓ₁] [HΓ']").
    { iApply ("He" with "HΓ₁"). iIntros "* H {$H}". }
    iLöb as "IH". rewrite {2}deep_handler_unfold.
    iSplit; [|iSplit; iIntros (v c)];
    last (iIntros "?"; by rewrite upcl_bottom).
    - iIntros (v) "[Hv HΓ₂] //=". ewp_pure_steps.
      rewrite -subst_map_insert. 
      iApply ("He₃" with "[Hv HΓ₂ HΓ']").
      { iExists v. rewrite !env_sem_typed_app; solve_env. }
      solve_env.
    - rewrite upcl_sem_sig_eff.
      iIntros "(%a & -> & Ha & Hκb)". ewp_pure_steps.
      rewrite -subst_map_insert /=.
      iApply ("He₁" with "[Ha HΓ']").
      + iExists a. rewrite env_sem_typed_app. solve_env.
      + iIntros (v') "[Hι' HΓ']"; ewp_pure_steps. 
        rewrite decide_True; [|split; first done; by injection].
        rewrite subst_subst_ne; last done.
        rewrite -subst_map_insert -delete_insert_ne; last done.
        rewrite -subst_map_insert.
        iApply ("He₂" with "[Hι' Hκb HΓ']"); simpl.
        * solve_env.
          iSplitL "HΓ' Hκb"; last (do 2 (rewrite env_sem_typed_insert; try done)).
          iIntros (u) "Hκ /=".
          iApply (ewp_mono with "[Hκb Hκ HΓ']").
          { iApply ("Hκb" with "Hκ"). iNext. iApply "IH". solve_env. }
          iIntros (?) "[Hτ' _] {$Hτ'} !> //".
        * solve_env.
  Qed.

End compatibility.
