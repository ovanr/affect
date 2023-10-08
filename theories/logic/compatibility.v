
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
From affine_tes.logic Require Import tactics.
From affine_tes.logic Require Import sem_types.
From affine_tes.logic Require Import sem_env.
From affine_tes.logic Require Import sem_sub_typing.
From affine_tes.logic Require Import sem_operators.
From affine_tes.logic Require Import reasoning.


Open Scope bi_scope.
Open Scope stdpp_scope.
Open Scope ieff_scope.
  
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
    iIntros (Φ vs) "!# /= [%v (%Hrw & Hτ & HΓ₁)] HΦ /=". 
    rewrite Hrw. iApply ewp_value. iApply "HΦ". iFrame.
  Qed.

  Lemma sem_typed_closure f x e τ ρ κ :
    match f with BNamed f => BNamed f ≠ x | BAnnon => True end →
    (x, τ) ::? (f, τ -{ ρ }-> κ) ::? [] ⊨ e : ρ : κ ⊨ [] -∗ 
    ⊨ᵥ (rec: f x := e) : (τ -{ ρ }-> κ).
  Proof.
      iIntros (?) "#He !#". iLöb as "IH".
      iIntros "%v !# %ws _ Hτ /=". 
      rewrite env_dom_nil env_sem_typed_empty /=.
      ewp_pure_steps. destruct x as [|x]; destruct f as [|f]; simpl.
      - rewrite - {3} [e]subst_map_empty. 
        iApply "He"; first done.
        iIntros (w) "[$ _]".
      - rewrite -subst_map_singleton.
        iApply ("He" with "[Hτ] []"); first solve_env.
        iIntros (w) "[$ _]".
      - rewrite -subst_map_singleton.
        iApply ("He" with "[Hτ] []"); first solve_env.
        iIntros (w) "[$ _]".
      - rewrite -(subst_map_singleton f) -subst_map_singleton subst_map_union.
        iApply ("He" with "[Hτ]"); [|iIntros (?) "[$ _]"].
        rewrite -insert_union_singleton_r; [solve_env|apply lookup_singleton_ne];
        intros ?; simplify_eq.
  Qed.

  Lemma sem_typed_Tclosure e τ ρ :
    (∀ α, ⊨ e : ρ : τ α) -∗ 
    ⊨ᵥ (Λ: e) : (∀T: α, { ρ }, τ α).
  Proof.
    iIntros "#He !# %u !#". ewp_pure_steps.
    rewrite - {2} [e]subst_map_empty.
    iSpecialize ("He" $! u (τ u) ∅).
    iApply "He"; first done. iIntros (?) "[$ _]".
  Qed.

  (* Signature abstraction and application *)
  Lemma sem_typed_Sclosure e C : 
    (∀ θ, ⊨ e : θ : C θ) -∗
    ⊨ᵥ (Λ: e) : (∀S: θ , C θ)%T.
  Proof.
    iIntros "#He !# %ρ /=".
    ewp_pure_steps. rewrite - {2} [e]subst_map_empty. 
    iApply (ewp_mono with "[He]").
    { iApply "He"; [done|iIntros (?) "[H _]"; iApply "H"].  }
    iIntros (v) "$ //".
  Qed.

  Lemma sem_typed_closure_to_unrestricted x e τ ρ κ Γ₁ Γ₂ :
    ⊨ᵥ (λ*λ: env_dom Γ₁, x, e) : (τ -{ ρ ; Γ₁ ; Γ₂ }-∘ κ) -∗
    ⊨ᵥ (λ*λ: env_dom Γ₁, x, e) : (τ -{ ρ ; Γ₁ ; Γ₂ }-> κ).
  Proof. 
    iIntros "#He !# %w !# %vs HΓ₁ Hτ". 
    iSpecialize ("He" $! w vs).
    iApply ("He" with "HΓ₁ Hτ").
  Qed.

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

  Lemma sem_typed_swap_fourth Γ₁ Γ₂ x y z z' e ρ τ₁ τ₂ τ₃ τ₄ κ :
    ((z', τ₄) :: (x, τ₁) :: (y, τ₂) :: (z, τ₃) :: Γ₁ ⊨ e : ρ : κ ⊨ Γ₂) -∗ 
    ((x, τ₁) :: (y, τ₂) :: (z, τ₃) :: (z', τ₄) :: Γ₁ ⊨ e : ρ : κ ⊨ Γ₂).
  Proof.
    iIntros "He".
    iApply sem_typed_sub_env; [|iApply "He"].
    do 2 (eapply env_le_trans; [apply env_le_swap_fourth|]).
    apply env_le_swap_fourth.
  Qed.

  Lemma sem_typed_contraction Γ₁ Γ₂ x e ρ τ κ :
    copy_ty τ →
    (x, τ) :: (x, τ) :: Γ₁ ⊨ e : ρ : κ ⊨ Γ₂ -∗ 
    (x, τ) :: Γ₁ ⊨ e : ρ : κ ⊨ Γ₂.
  Proof.
    iIntros (?) "He".
    iApply sem_typed_sub_env; 
      [by apply env_le_copy_contraction|iApply "He"].
  Qed.

  Lemma sem_typed_weaken Γ₁ Γ₂ x e ρ τ κ :
    (Γ₁ ⊨ e : ρ : κ ⊨ Γ₂) -∗ ((x, τ) :: Γ₁ ⊨ e : ρ : κ ⊨ Γ₂).
  Proof.
    iIntros "He".
    iApply sem_typed_sub_env; [apply env_le_weaken|iApply "He"].
  Qed.

  (* λ-calculus rules *)

  Lemma sem_typed_afun_mult Γ₁ Γ₂ Δ₁ Δ₂ x e τ ρ κ: 
    x ∉ (env_dom Γ₁) → x ∉ (env_dom Δ₁) → x ∉ (env_dom Γ₂) →
    env_dom Δ₂ ⊆ env_dom Δ₁ →
    env_dom Γ₁ ## env_dom Δ₁ →
    (x,τ) ::? Δ₁ ++ Γ₁ ⊨ e : ρ : κ ⊨ Δ₂ -∗
    Γ₁ ++ Γ₂ ⊨ (λ*λ: env_dom Δ₁, x, e) : ⟨⟩ : (τ -{ ρ ; Δ₁ ; Δ₂ }-∘ κ) ⊨ Γ₂.
  Proof.
    iIntros (?????) "#He !# %Φ %vs HΓ₁₂ HΦ //=".
    iDestruct (env_sem_typed_app with "HΓ₁₂") as "[HΓ₁ HΓ₂]".
    rewrite subst_map_ctx_lambda /=. 
    destruct Δ₁ as [|[z ι] Δ₁'].
    - rewrite env_dom_nil delete_list_nil. simpl. 
      replace Δ₂ with ([] : env Σ) 
          by (symmetry; apply (map_eq_nil fst); by apply list_nil_subseteq). 
      ewp_pure_steps. iApply "HΦ". iFrame.
      iIntros (w ws) "_ Hτ". rewrite env_dom_nil /=.
      ewp_pure_steps. rewrite subst'_subst_map_insert.
      iApply ("He" with "[Hτ HΓ₁] []").
      { destruct x; solve_env. }
      iIntros (u) "[$ _]".
    - rewrite env_dom_cons delete_list_cons. iSimpl.
      ewp_pure_steps. iApply "HΦ". iFrame.
      iIntros (u ws) "HΔ₁ Hτ". 
      set Δ₁ := (z, ι) :: Δ₁'.
      set e' := subst_map _ e.
      iApply (ewp_bind [AppLCtx _]); first done.
      ewp_bottom.
      iApply (ewp_app_mult with "[HΔ₁]"); first done. iIntros "HΔ₁".
      simpl. ewp_pure_steps.
      rewrite /e' env_dom_cons subst_map_union -binder_delete_union subst'_subst_map_insert -(env_dom_cons _ ι).
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
        rewrite -(env_sem_typed_delete_union Δ₂ Δ₁); last done. 
        by rewrite -(env_sem_typed_difference_delete Δ₂ Δ₁).
      + iIntros (w) "[$ HΔ₂Γ₁] /=". 
        assert (x ∉ env_dom Δ₂).
        { intros ?. apply H0. 
          destruct (elem_of_subseteq (env_dom Δ₂) (env_dom Δ₁)) as [H' _]. 
          by apply H'. }
        rewrite -env_sem_typed_insert; last done.
        rewrite -(env_sem_typed_delete_union Δ₂ Δ₁); last done. 
        rewrite -(env_sem_typed_difference_delete Δ₂ Δ₁); last done. iFrame. 
  Qed.

  Lemma sem_typed_afun Γ₁ Γ₂ x e τ ρ κ: 
    x ∉ (env_dom Γ₁) → x ∉ (env_dom Γ₂) →
    (x,τ) ::? Γ₁ ⊨ e : ρ : κ ⊨ [] -∗
    Γ₁ ++ Γ₂ ⊨ (λ: x, e) : ⟨⟩ : (τ -{ ρ }-∘ κ) ⊨ Γ₂.
  Proof.
    intros ??.
    rewrite [(λ: x, _)%E](@ctx_lambda_env_dom_nil Σ).
    iApply (sem_typed_afun_mult _ _ [] []); solve_sidecond.
  Qed.

  Lemma sem_typed_lambdas_norm Γ Γ' Δ₁ Δ₂ f x ρ e τ κ :
    env_dom Δ₂ ⊆ env_dom Δ₁ →
    x ∉ env_dom Δ₁ → f ∉ env_dom Δ₁ → f ≠ x →
    Γ ⊨ e : ρ : (τ -{ ρ }-> (() -{ ρ ; Δ₁; Δ₂ }-∘ κ)) ⊨ Γ' -∗
    Γ ⊨ (lambdas_norm f x (env_dom Δ₁) e) : ρ : (τ -{ ρ ; Δ₁; Δ₂ }-> κ) ⊨ Γ'.
  Proof.
    iIntros (Hdis Hx Hf Hfx) "#He %Φ %vs !# HΓ HΦ". 
    rewrite /lambdas_norm /=. 
    iApply (ewp_bind [AppRCtx _]); first done.
    iApply ("He" with "HΓ"). iIntros (w) "[#Hτuκ HΓ'] /=".
    ewp_pure_steps. 
    rewrite -subst_map_singleton subst_map_ctx_lambda delete_list_singleton_ne; last done.
    rewrite /= subst_map_app_mult /= lookup_delete lookup_delete_ne; last done.
    rewrite lookup_insert. 
    replace (map (subst_map (delete x {[f := w]})) (map Var (env_dom Δ₁))) with
            (map Var (env_dom Δ₁)).
    2: { clear - Δ₁ x f w Hx Hf Hfx. 
         induction Δ₁ as [|[z ι] Δ₁']; first done. rewrite env_dom_cons /=.
         rewrite env_dom_cons in Hx Hf.
         edestruct (not_elem_of_cons (env_dom Δ₁') x)  as [[] _]; first done.
         edestruct (not_elem_of_cons (env_dom Δ₁') f)  as [[] _]; first done.
         rewrite lookup_delete_ne; last done. rewrite lookup_singleton_ne; last done.
         by rewrite -IHΔ₁'. }
    destruct Δ₁ as [|[z ι] Δ₁'] eqn:HΔ₁eq.
    - rewrite env_dom_nil /=. ewp_pure_steps.
      iApply "HΦ". iIntros "{$HΓ'} %u %us !# _ Hτ /=".
      rewrite env_dom_nil /=. ewp_pure_steps. rewrite decide_True; last done.
      iApply (ewp_bind [AppLCtx _]); first done.
      iApply (ewp_mono with "[Hτuκ Hτ]"); [by iApply "Hτuκ"|].
      iIntros (?) "[Hu _] !> /=". by iApply "Hu".
      Unshelve. apply empty.
    - rewrite {1}env_dom_cons env_dom_nil /=. ewp_pure_steps. iApply "HΦ".
      iIntros "{$HΓ'} %u %us !# HΔ₁ Hτ". iApply (ewp_bind [AppLCtx _]); first done.
      iApply (ewp_app_mult with "HΔ₁"). iIntros "HΔ₁".
      simpl. ewp_pure_steps. rewrite -subst_map_insert subst_map_app_mult /=.
      rewrite lookup_insert map_map_subst_map -HΔ₁eq. 
      rewrite -HΔ₁eq in Hx Hf Hdis.
      set uus := (<[x:=u]> (us ∖ delete (env_dom Δ₁) us)).
      iDestruct (subst_map_var Δ₁ uus with "[HΔ₁]") as "[%uus' %Hrwuus']".
      { rewrite -env_sem_typed_insert; last done.
        by rewrite env_sem_typed_difference_delete. }
      rewrite Hrwuus' app_mult_cons. 
      replace ([ #() : expr ]) with (map Val [ #() : val ]) by done.
      rewrite -map_app. iApply ewp_bind_app_mult.
      iApply (ewp_mono with "[Hτuκ Hτ] [HΔ₁]"); [by iApply "Hτuκ"|].
      iIntros (q) "[Hq _] !> /=". rewrite map_app /= -app_mult_cons -Hrwuus'.
      iSpecialize ("Hq" $! #() uus with "[HΔ₁] []"); try done.
      { rewrite -env_sem_typed_insert; last done.
        by rewrite env_sem_typed_difference_delete. }
      iApply (ewp_mono with "Hq").
      assert (x ∉ env_dom Δ₂).
      { intros ?. apply Hx. by eapply (elem_of_subseteq (env_dom Δ₂)); done. }
      iIntros (?) "[$ HΔ₁] !>". rewrite /uus.
      { rewrite -env_sem_typed_insert; last done. 
        by rewrite -env_sem_typed_difference_delete. }
      Unshelve. apply empty.
  Qed.

  Lemma sem_typed_ufun_mult Γ₁ Γ₂ Δ₁ Δ₂ f x e τ ρ κ:
    x ∉ (env_dom Γ₁) → f ∉ (env_dom Γ₁) → f ∉ (env_dom Δ₁) → x ∉ (env_dom Δ₁) →
    env_dom Δ₂ ⊆ env_dom Δ₁ →
    env_dom Γ₁ ## env_dom Δ₁ →
    x ≠ f →
    copy_env Γ₁ →
    (x, τ) :: (f, τ -{ ρ ; Δ₁ ; Δ₂ }-> κ) :: Δ₁ ++ Γ₁ ⊨ e : ρ : κ ⊨ Δ₂ -∗
    Γ₁ ++ Γ₂ ⊨ (rec*: f , env_dom Δ₁, x,  e) : ρ : (τ -{ ρ ; Δ₁ ; Δ₂ }-> κ) ⊨ Γ₂.
  Proof.
    iIntros (??????? HcpyΓ₁) "#He !# %Φ %vs HΓ₁₂ HΦ".
    iDestruct (env_sem_typed_app with "HΓ₁₂") as "[HΓ₁ HΓ₂]".
    iApply (ewp_mono _ _ (λ v, (τ -{ ρ; Δ₁; Δ₂ }-> κ) v ∗ ⟦ Γ₂ ⟧ vs) with "[HΓ₁ HΓ₂] [HΦ]");
      last (iIntros (?) "[Hτκ HΓ₂] !>"; iApply "HΦ"; iFrame). 
    iApply (ewp_frame_r with "[HΓ₁] HΓ₂").
    iApply (sem_typed_lambdas_norm Γ₁ [] Δ₁ Δ₂ f x ρ _ τ κ with "[] HΓ₁"); 
      try done; last (iIntros (?) "[$ _] $! //").
    iIntros "!# %Φ' %vs' HΓ₁ HΦ'".
    rewrite HcpyΓ₁. iDestruct "HΓ₁" as "#HΓ₁".
    simpl. ewp_pure_steps. iApply "HΦ'". iLöb as "IH".
    iSplitL; last done.
    iIntros (w ws) "!# _ Hτ". rewrite env_dom_nil /=. ewp_pure_steps. 
    rewrite delete_commute -subst_map_insert -delete_insert_ne; last done.
    rewrite -subst_map_insert /= !subst_map_ctx_lambda.
    destruct Δ₁ as [|[z ι] Δ₁'] eqn:HeqΔ.
    - replace Δ₂ with ([] : env Σ) by 
        (symmetry; apply (map_eq_nil fst); by apply list_nil_subseteq). 
      rewrite !env_dom_nil /= !delete_list_nil insert_commute; last done.
      rewrite lookup_insert lookup_delete. ewp_pure_steps.
      iSplitL; last done.
      iIntros (??) "_ -> /=". rewrite env_dom_nil /=.
      ewp_pure_steps. iApply (ewp_bind [AppRCtx _]); first done.
      replace ([] : list string) with (env_dom ([] : env Σ)) by done.
      set f' := (rec: f x <> :=
                  let: f := lambdas_norm f x (env_dom []) f in
                  subst_map (delete f (delete f (delete x vs'))) e)%V.
      rewrite -(subst_map_empty (lambdas_norm _ _ _ _ )).
      iApply (sem_typed_lambdas_norm [] [] [] []  with "[] []"); 
        [done|done|done|done| |done|].
      { rewrite /f'. iIntros (Φ'' ?) "!# _ HΦ'' /=". ewp_pure_steps.
        iApply "HΦ''". iDestruct "IH" as "[$ _]". }
      iIntros (u) "[#Hτκ _] /=". ewp_pure_steps. 
      rewrite -subst_map_insert insert_insert.
      iApply ("He" with "[Hτ]"); last (iIntros (?) "[$ $] //").
      solve_env. by do 2 (rewrite -env_sem_typed_insert; last done). 
    - rewrite {4}env_dom_cons. iSimpl. ewp_pure_steps. iSplitL; last done.
      rewrite !lookup_delete_not_elem; try done.
      rewrite insert_commute; last done. rewrite lookup_insert lookup_delete.
      rewrite !delete_list_commute delete_idemp delete_insert_delete.
      iIntros (u us) "HΔ₁ -> /=". 
      iApply (ewp_bind [AppLCtx _]); first done.
      iApply (ewp_app_mult with "HΔ₁"). iIntros "HΔ₁ /=".
      ewp_pure_steps. iApply (ewp_bind [AppRCtx _]); first done.
      set f' := (rec: f x :=
                    λ*λ: env_dom ((z, ι)%core :: Δ₁'), <>,
                    (let: f := lambdas_norm f x (env_dom ((z, ι)%core :: Δ₁')) f in
                    subst_map
                      (delete (env_dom ((z, ι)%core :: Δ₁')) (delete f (delete x vs'))) e))%V.
      replace (lambdas_norm f x (env_dom ((z,ι) :: Δ₁')) f') with
              (subst_map us (lambdas_norm f x (env_dom ((z,ι) :: Δ₁')) f')) by done.
      iApply (sem_typed_lambdas_norm _ _ ((z,ι) :: Δ₁') Δ₂ with "[] HΔ₁"); try done.
      { iIntros (Φ'' ?) "!# HΔ₁ HΦ'' /=". rewrite /f'. ewp_pure_steps.
        iApply "HΦ''". iSplitR "HΔ₁"; last done.
        iDestruct "IH" as "[$ _]". }
      iIntros (?) "[Hτκ HΔ₁] /=". ewp_pure_steps.
      rewrite -subst_map_insert subst_map_union.
      iApply ("He" with "[Hτ Hτκ HΔ₁]"). 
      + iExists w. iFrame. iSplit.
        { iPureIntro. apply lookup_union_Some_l.
          rewrite delete_insert_ne; last done.
          rewrite lookup_delete_not_elem; last done.
          apply lookup_insert. }
        iExists v. iFrame. iSplit.
        { iPureIntro. rewrite lookup_union_r; [apply lookup_insert|].
          by rewrite -delete_list_commute lookup_delete. }
        rewrite app_comm_cons env_sem_typed_app. iSplitL "HΔ₁".
        { rewrite -env_sem_typed_delete_union; last done.
          rewrite -env_sem_typed_insert; last done.
          by rewrite -env_sem_typed_difference_delete. }
        iApply env_sem_typed_union.
        rewrite -env_sem_typed_delete_disjoint; last done.
        rewrite -env_sem_typed_delete; last done.
        by rewrite -env_sem_typed_insert. 
      + iIntros (?) "[$ HΔ₂]".
        rewrite -env_sem_typed_delete_union; last done.
        assert (f ∉ env_dom Δ₂).
        { intros ?. apply H1. by eapply (elem_of_subseteq (env_dom Δ₂)); done. }
        rewrite -env_sem_typed_insert; last done.
        by iApply env_sem_typed_difference_delete.
  Qed.

  Lemma sem_typed_ufun Γ₁ Γ₂ f x e τ ρ κ:
    x ∉ (env_dom Γ₁) → f ∉ (env_dom Γ₁) → match f with BNamed f => BNamed f ≠ x | BAnnon => True end →
    copy_env Γ₁ →
    (x, τ) ::? (f, τ -{ ρ }-> κ) ::? Γ₁ ⊨ e : ρ : κ ⊨ [] -∗
    Γ₁ ++ Γ₂ ⊨ (rec: f x :=  e) : ⟨⟩ : (τ -{ ρ }-> κ) ⊨ Γ₂.
  Proof.
    iIntros (??? HcpyΓ₁) "#He !# %Φ %vs HΓ₁₂ HΦ //=".
    ewp_pure_steps.
    rewrite env_sem_typed_app. iApply "HΦ". 
    iDestruct "HΓ₁₂" as "[HΓ₁ $]".
    rewrite HcpyΓ₁. iDestruct "HΓ₁" as "#HΓ₁".
    iLöb as "IH".
    iIntros (w ws) "!# _ Hτ". rewrite env_dom_nil /=. 
    ewp_pure_steps. destruct f; destruct x; simpl.
    - iApply ("He" with "HΓ₁ []").
      iIntros (v) "[Hκ _] {$Hκ}".
    - rewrite -subst_map_insert. 
      iApply ("He" with "[HΓ₁ Hτ] []"); first solve_env. 
      iIntros (v) "//= [$ _]".
    - rewrite -subst_map_insert.
      iApply ("He" with "[HΓ₁ Hτ] []"); first solve_env.
      iIntros (v) "//= [$ _]".
    - assert (s ≠ s0) by (intros ?; simplify_eq).
      rewrite subst_subst_ne; last done.
      rewrite -subst_map_insert.
      rewrite -delete_insert_ne; last done. 
      rewrite -subst_map_insert.
      iApply ("He" with "[Hτ] []"); first solve_env.
      + by do 2 (rewrite -env_sem_typed_insert; last done).
      + iIntros (v) "[$ _]". 
  Qed.

  Lemma sem_typed_ufun_poly_rec Γ₁ Γ₂ f x e τ ρ κ:
    x ∉ (env_dom Γ₁) → f ∉ (env_dom Γ₁) → match x with BNamed x => BNamed x ≠ f | BAnnon => True end →
    copy_env Γ₁ →
    (∀ ι, (x, τ ι) ::? (f, ∀T: α,, τ α -{ ρ α }-> κ α) ::? Γ₁ ⊨ e : ρ ι : κ ι ⊨ []) -∗
    Γ₁ ++ Γ₂ ⊨ (rec: f <> := λ: x, e) : ⟨⟩ : (∀T: α,, τ α -{ ρ α }-> κ α) ⊨ Γ₂.
  Proof.
    iIntros (??? HcpyΓ₁) "#He !# %Φ %vs HΓ₁₂ HΦ //=".
    ewp_pure_steps.
    rewrite env_sem_typed_app. iApply "HΦ". 
    iDestruct "HΓ₁₂" as "[HΓ₁ $]".
    rewrite HcpyΓ₁. iDestruct "HΓ₁" as "#HΓ₁".
    iLöb as "IH".
    iIntros (α) "!#". ewp_pure_steps.
    destruct f; destruct x; simpl; 
    ewp_pure_steps; iIntros (v ?) "!# _ Hτ";
    rewrite env_dom_nil /=; ewp_pure_steps.
    - iApply ("He" with "HΓ₁ []").
      iIntros (?) "[$ _]".
    - rewrite -subst_map_insert. 
      iApply ("He" with "[HΓ₁ Hτ] []"); first solve_env. 
      iIntros (?) "//= [$ _]".
    - rewrite -subst_map_insert.
      iApply ("He" with "[HΓ₁ Hτ] []"); first solve_env.
      iIntros (?) "//= [$ _]".
    - assert (s ≠ s0) by (intros ?; simplify_eq).
      rewrite decide_True; last auto.
      rewrite subst_subst_ne; last done.
      rewrite -subst_map_insert.
      rewrite -delete_insert_ne; last done. 
      rewrite -subst_map_insert.
      iApply ("He" with "[Hτ] []"); first solve_env.
      + by do 2 (rewrite -env_sem_typed_insert; last done).
      + iIntros (?) "[$ _]". 
  Qed.

  Lemma sem_typed_sufun_mult Γ₁ Γ₂ Δ₁ Δ₂ x e τ ρ κ:
    x ∉ (env_dom Γ₁) → x ∉ (env_dom Δ₁) → x ∉ (env_dom Γ₂) →
    env_dom Δ₂ ⊆ env_dom Δ₁ →
    env_dom Γ₁ ## env_dom Δ₁ →
    (x, τ) ::? Δ₁ ++ Γ₁ ⊨ e : ρ : κ ⊨ Δ₂ ++ Γ₁ -∗
    Γ₁ ++ Γ₂ ⊨ (λ*λ: env_dom Δ₁, x, e) : ⟨⟩ : (τ >-{ ρ ; Δ₁ ; Δ₂ }-∘ κ) ⊨ Γ₂.
  Proof.
    iIntros (?????) "#He !# %Φ %vs HΓ₁₂ HΦ /=".
    iDestruct (env_sem_typed_app with "HΓ₁₂") as "[HΓ₁ HΓ₂]".
    iApply (ewp_mono _ _ (λ v, (τ >-{ ρ; Δ₁; Δ₂ }-∘ κ) v ∗ env_sem_typed Γ₂ vs) 
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
      ewp_bottom.
      set Δ₁ := (z, ι) :: Δ₁'.
      set e' := subst_map (binder_delete x (delete (z :: env_dom Δ₁') vs)) e.
      iApply (ewp_app_mult with "[HΔ₁]"); first done. iIntros "HΔ₁".
      simpl. ewp_pure_steps.
      rewrite /e' env_dom_cons subst_map_union -binder_delete_union subst'_subst_map_insert -(env_dom_cons _ ι).
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

  Lemma sem_typed_sufun Γ₁ Γ₂ x e τ ρ κ:
    x ∉ (env_dom Γ₁) → x ∉ (env_dom Γ₂) →
    (x, τ) ::? Γ₁ ⊨ e : ρ : κ ⊨ Γ₁ -∗
    Γ₁ ++ Γ₂ ⊨ (λ: x, e) : ⟨⟩ : (τ >-{ ρ }-∘ κ) ⊨ Γ₂.
  Proof.
    intros ??.
    rewrite [(λ: x, _)%E](@ctx_lambda_env_dom_nil Σ).
    iApply (sem_typed_sufun_mult _ _ [] []); solve_sidecond.
  Qed.

  Lemma sem_typed_app_mult Γ₁ Γ₂ Γ₃ Δ₁ Δ₂ e₁ e₂ τ ρ κ: 
    Γ₂ ⊨ e₁ : ρ : (τ -{ ρ ; Δ₁ ; Δ₂ }-∘ κ) ⊨ Γ₃ -∗
    Γ₁ ⊨ e₂ : ρ : τ ⊨ Δ₁ ++ Γ₂ -∗
    Γ₁ ⊨ (e₁ <_ map Var (env_dom Δ₁) _> e₂) : ρ : κ ⊨ Δ₂ ++ Γ₃.
  Proof.
    iIntros "#He₁ #He₂ !# %Φ %vs HΓ₁ HΦ //=".
    rewrite subst_map_app_mult map_map.
    iApply (ewp_bind [AppRCtx _]); first done.
    iApply ("He₂" with "HΓ₁").
    iIntros (v) "[Hτ HΔ₁Γ₂]". 
    iDestruct (env_sem_typed_app with "HΔ₁Γ₂") as "[HΔ₁ HΓ₂]".
    replace (λ (x : string), subst_map vs x) with (subst_map vs ∘ Var) by done.
    iDestruct (subst_map_var with "HΔ₁") as "[%ws %Hrw]". rewrite Hrw /=.
    assert (Hfold : ∀ e, (e <_ map Val ws _> v)%E = (e <_ map Val (ws ++ [v]) _>)%E).
    { clear - ws v. induction ws; first done. simpl. intros e. by rewrite IHws. }
    rewrite Hfold.
    iApply ewp_bind_app_mult. 
    iApply ("He₁" with "HΓ₂"). simpl.
    iIntros (w) "[Hτκw HΓ₃] //=". rewrite -Hfold -Hrw.
    iApply (ewp_mono with "[Hτκw HΔ₁ Hτ]").
    { iApply ("Hτκw" $! v vs with "HΔ₁ Hτ"). }
    iIntros (u) "[Hκ HΔ₂] !>". iApply "HΦ". rewrite env_sem_typed_app. iFrame.
  Qed.
  
  Lemma sem_typed_app Γ₁ Γ₂ Γ₃ e₁ e₂ τ ρ κ: 
    Γ₂ ⊨ e₁ : ρ : (τ -{ ρ }-∘ κ) ⊨ Γ₃ -∗
    Γ₁ ⊨ e₂ : ρ : τ ⊨ Γ₂ -∗
    Γ₁ ⊨ (e₁ e₂) : ρ : κ ⊨ Γ₃.
  Proof.
    rewrite {2} [e₁](@app_mult_env_dom_nil Σ) - {2} (app_nil_l Γ₃).
    iApply sem_typed_app_mult.
  Qed.

  Lemma sem_typed_suapp_mult Γ₁ Γ₂ Δ₁ Δ₂ f e₂ τ ρ κ: 
    Γ₁ ⊨ e₂ : ρ : τ ⊨ (f, τ >-{ ρ ; Δ₁ ; Δ₂ }-∘ κ) :: Δ₁ ++ Γ₂ -∗
    Γ₁ ⊨ (f <_ map Var (env_dom Δ₁) _> e₂) : ρ : κ ⊨ (f, τ >-{ ρ ; Δ₁ ; Δ₂  }-∘ κ) :: Δ₂ ++ Γ₂. 
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

  Lemma sem_typed_suapp Γ₁ Γ₂ f e₂ τ ρ κ: 
    Γ₁ ⊨ e₂ : ρ : τ ⊨ (f, τ >-{ ρ }-∘ κ) :: Γ₂ -∗
    Γ₁ ⊨ (f e₂) : ρ : κ ⊨ (f, τ >-{ ρ }-∘ κ) :: Γ₂. 
  Proof.
    rewrite [Var f](@app_mult_env_dom_nil Σ) - {2} (app_nil_l Γ₂).
    iApply sem_typed_suapp_mult.
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

  Lemma sem_typed_match Γ₁ Γ₂ Γ₃ e₁ x y e₂ e₃ τ ρ κ ι: 
    x ∉ env_dom Γ₂ → x ∉ env_dom Γ₃ → y ∉ env_dom Γ₂ → y ∉ env_dom Γ₃ →
    Γ₁ ⊨ e₁ : ρ : (τ + κ) ⊨ Γ₂ -∗
    (x, τ) ::? Γ₂ ⊨ e₂ : ρ : ι ⊨ Γ₃ -∗
    (y, κ) ::? Γ₂ ⊨ e₃ : ρ : ι ⊨ Γ₃ -∗
    Γ₁ ⊨ match: e₁ with InjL x => e₂ | InjR y => e₃ end : ρ : ι ⊨ Γ₃.
  Proof.
    iIntros (????) "#He₁ #He₂ #He₃ !# %Φ %vs HΓ₁ HΦ //=".
    iApply (ewp_bind [CaseCtx _ _]); first done.
    iApply ("He₁" with "HΓ₁"). simpl.
    iIntros (v) "[(%w & [(-> & Hτ)|(-> & Hκ)]) HΓ₂] //="; 
      ewp_pure_steps.
    - destruct x; simpl.
      + iApply ("He₂" with "[HΓ₂ Hτ] [HΦ]"); [solve_env|eauto].
      + rewrite -subst_map_insert.
        iApply ("He₂" with "[HΓ₂ Hτ] [HΦ]"); [solve_env|].
        iIntros (?) "[Hι HΓ₃]". iApply "HΦ". solve_env.
    - destruct y; simpl.
      + iApply ("He₃" with "[HΓ₂ Hκ] [HΦ]"); [solve_env|eauto].
      + rewrite -subst_map_insert.
        iApply ("He₃" with "[HΓ₂ Hκ] [HΦ]"); [solve_env|].
        iIntros (?) "[Hι HΓ₃]". iApply "HΦ". solve_env.
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
    copy_env Γ₁ →
    (∀ α, Γ₁ ⊨ e : ρ : C α ⊨ []) -∗
    Γ₁ ++ Γ₂ ⊨ (Λ: e) : ⟨⟩ : (∀T: α , { ρ } , C α)%T ⊨ Γ₂.
  Proof.
    iIntros (Hcpy) "#He !# %Φ %vs HΓ₁₂ HΦ //=".
    iDestruct (env_sem_typed_app with "HΓ₁₂") as "[HΓ₁ HΓ₂]".
    rewrite Hcpy. iDestruct "HΓ₁" as "#HΓ₁".
    ewp_pure_steps. iApply "HΦ". 
    iIntros "{$HΓ₂} %α //= !#". ewp_pure_steps.
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
    Γ₁ ⊨ e : ρ : (C (μT: α, C α)) ⊨ Γ₂ -∗
    Γ₁ ⊨ (fold: e) : ρ : (μT: α, C α) ⊨ Γ₂.
  Proof.
    iIntros "#He %Φ %vs !# HΓ₁ HΦ //=".
    iApply (ewp_bind [AppRCtx _]); first done. 
    iApply ("He" with "HΓ₁").
    iIntros "%w [HC HΓ₂] //=". 
    unfold rec_fold. ewp_pure_steps. iApply "HΦ".
    iFrame. by iApply sem_ty_rec_unfold. 
  Qed.

  Lemma sem_typed_unfold Γ₁ Γ₂ e ρ C `{NonExpansive C}:
    Γ₁ ⊨ e : ρ : (μT: α, C α) ⊨ Γ₂ -∗
    Γ₁ ⊨ (unfold: e) : ρ : (C (μT: α, C α)) ⊨ Γ₂.
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
  
  Lemma sem_typed_alloc_cpy Γ₁ Γ₂ e ρ τ: 
    Γ₁ ⊨ e : ρ : τ ⊨ Γ₂ -∗
    Γ₁ ⊨ ref e : ρ : Refᶜ  τ ⊨ Γ₂.
  Proof.
    iIntros "#He !# %Φ %vs HΓ₁ HΦ //=".
    iApply (ewp_bind [AllocCtx]); first done. simpl.
    iApply ("He" with "HΓ₁").
    iIntros (v) "[Hτ HΓ₂]".
    iApply ewp_alloc. iIntros "!> %l Hl". 
    iApply "HΦ". iFrame.
    iMod (inv_alloc (tyN.@l) _
       (∃ w, l ↦ w ∗ τ w)%I with "[Hl Hτ]") as "#Hinv".
    { iExists v. by iFrame. }
    iModIntro. iExists l. by auto.
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

  Lemma sem_typed_replace_cpy Γ₁ Γ₂ Γ₃ e₁ e₂ ρ τ: 
    Γ₂ ⊨ e₁ : ρ : Refᶜ τ ⊨ Γ₃ -∗
    Γ₁ ⊨ e₂ : ρ : τ ⊨ Γ₂ -∗
    Γ₁ ⊨ (e₁ <!- e₂) : ρ : τ ⊨ Γ₃.
  Proof.
    iIntros "#He₁ #He₂ %Φ %vs !# /= HΓ₁ HΦ /=".
    iApply (ewp_bind [ReplaceRCtx _]); first done. simpl.
    iApply ("He₂" with "HΓ₁").
    iIntros (w) "[Hτ HΓ₂]". 
    iApply (ewp_bind [ReplaceLCtx _]); first done. simpl.
    iApply ("He₁" with "HΓ₂").
    iIntros (u) "[(%l & -> & Hinv) HΓ₃]".
    iApply (ewp_atomic _ (⊤ ∖ ↑tyN.@l)).
    iMod (inv_acc _ (tyN.@l) with "Hinv") as "[(%u & >Hl & Hu) Hclose]"; first done.
    iModIntro. iApply (ewp_replace with "Hl"). 
    iIntros "!> Hl !>".  
    iMod ("Hclose" with "[Hl Hτ]").
    { iExists w. iFrame. } 
    iIntros "!>". iApply "HΦ"; solve_env.
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
  
  Lemma sem_typed_perform Γ₁ Γ₂ e τ (A B : sem_ty Σ → sem_sig Σ → sem_ty Σ) 
    `{ NonExpansive2 A, NonExpansive2 B } :
    let ρ := (∀μTS: θ, α, A α θ ⇒ B α θ)%R in
    Γ₁ ⊨ e : ρ : A τ ρ ⊨ Γ₂ -∗
    Γ₁ ⊨ (perform: e) : ρ : B τ ρ ⊨ Γ₂.
  Proof.
    iIntros "#He !# %Φ %vs HΓ₁ HΦ //=". rewrite /rec_perform.
    iApply (ewp_bind [AppRCtx _; DoCtx OS]); first done.
    iApply ("He" with "HΓ₁").
    iIntros (v) "[Hι HΓ₂] //=".
    iApply (ewp_bind [AppRCtx _]); first done.
    iApply ewp_do_os. rewrite upcl_sem_sig_rec_eff /=.
    iExists τ, v. iFrame. iSplitR; first done.
    iIntros (b) "Hκ". ewp_pure_steps. iApply "HΦ". iFrame.
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
  Lemma sem_typed_shallow_try Γ₁ Γ₂ Γ₃ Γ' w k e h r A B τ τ' ρ' `{NonExpansive2 A, NonExpansive2 B}:
    w ∉ env_dom Γ₂ → w ∉ env_dom Γ' → k ∉ env_dom Γ' →
    w ∉ env_dom Γ₃ → k ∉ env_dom Γ₃ → w ≠ k →
    let ρ := (∀μTS: θ, α, A α θ  ⇒ B α θ)%R in
    Γ₁ ⊨ e : ρ : τ' ⊨ Γ₂ -∗
    (∀ α, (w, A α ρ) :: (k, B α ρ -{ ρ }-∘ τ') :: Γ' ⊨ h : ρ' : τ ⊨ Γ₃) -∗
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
    - rewrite upcl_sem_sig_rec_eff.
      iIntros "(%α & %a & -> & Ha & Hκb) //=". ewp_pure_steps.
      rewrite decide_True; [|split; first done; by injection].
      rewrite subst_subst_ne; last done.
      rewrite -subst_map_insert -delete_insert_ne; last done.
      rewrite -subst_map_insert.
      iApply ("Hh" with "[HΓ' Hκb Ha]"); first solve_env.
      + iSplitR "HΓ'"; [|by (do 2 (rewrite -env_sem_typed_insert; try done))].
        iIntros (b ws) "_ Hκ". rewrite env_dom_nil /=. 
        iApply (ewp_mono with "[Hκ Hκb]"); [by iApply "Hκb"|].
        iIntros (?) "[Hτ' _] !> //=". iFrame.
      + iIntros (u) "[Hu HΓ₃]". iApply "HΦ". iFrame.
        rewrite -(env_sem_typed_insert _ _ w v); last done.
        by rewrite -(env_sem_typed_insert _ _ k c).
  Qed.
  
  Lemma sem_typed_deep_try Γ₁ Γ' Γ₂ Γ₃ e w k h r ρ' A B τ τ' `{NonExpansive2 A, NonExpansive2 B}:
    w ∉ env_dom Γ₂ → w ∉ env_dom Γ' → w ∉ env_dom Γ₃ →
    k ∉ env_dom Γ' → k ∉ env_dom Γ₃ → w ≠ k → copy_env Γ' →
    let ρ := (∀μTS: θ , α, A α θ ⇒ B α θ)%R in
    Γ₁ ⊨ e : ρ : τ ⊨ Γ₂ -∗
    (∀ α, (w, A α ρ) :: (k, B α ρ -{ ρ' }-∘ τ') :: Γ' ⊨ h : ρ' : τ' ⊨ Γ₃) -∗
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
    - rewrite upcl_sem_sig_rec_eff.
      iIntros "(%α & %a & -> & Ha & Hκb)". ewp_pure_steps.
      rewrite decide_True; [|split; first done; by injection].
      rewrite subst_subst_ne; last done.
      rewrite -subst_map_insert -delete_insert_ne; last done.
      rewrite -subst_map_insert.
      iApply ("Hh" with "[Ha HΓ' Hκb]").
      + solve_env. 
        iSplitL "Hκb"; [|by (do 2 (rewrite -env_sem_typed_insert; try done))].
        iIntros (b ws) "_ Hb". iApply (ewp_mono with "[Hb Hκb] []").
        { iApply ("Hκb" with "Hb []"). rewrite !deep_handler_unfold. iApply "IH". }
        iIntros "* [Hτ' _] !> {$Hτ'}". 
      + iIntros (u) "[Hτ' HΓ₃] {$Hτ'}".
        rewrite -(env_sem_typed_insert _ _ w v); last done.
        by rewrite -(env_sem_typed_insert _ _ k c).
    Qed.

  Lemma sem_typed_deep_try_alt Γ₁ Δ Γ₂ Γ₃ e w k h r ρ' A B τ τ' `{NonExpansive2 A, NonExpansive2 B}:
    w ∉ env_dom Γ₂ → w ∉ env_dom Δ → w ∉ env_dom Γ₃ →
    k ∉ env_dom Δ → k ∉ env_dom Γ₃ → w ≠ k →
    env_dom Γ₃ ⊆ env_dom Δ →
    let ρ := (∀μTS: θ, α, A α θ ⇒ B α θ)%R in
    Γ₁ ⊨ e : ρ : τ ⊨ Γ₂ -∗
    (∀ α, [(w, A α ρ) ; (k, B α ρ -{ ρ' ; Δ ; Γ₃ }-∘ τ')] ⊨ h : ρ' : (() -{ ρ' ; Δ ; Γ₃ }-∘ τ') ⊨ []) -∗
    (w, τ) :: Γ₂ ⊨ r : ρ' : (() -{ ρ' ; Δ ; Γ₃ }-∘ τ') ⊨ [] -∗
    Γ₁ ++ Δ ⊨ (deep-try-alt: e  thread (env_dom Δ) with  
                                effect k => w => h 
                              | return w => r end) : ρ' : τ' ⊨ Γ₃. 
  Proof.
    iIntros (???????) "#He #Hh #Hr %Φ !# %vs HΓ₁Δ HΦ /=".
    iDestruct (env_sem_typed_app with "HΓ₁Δ") as "[HΓ₁ HΔ]".
    rewrite subst_map_app_mult.
    iDestruct (subst_map_var with "HΔ") as "[%ws %Hrw]". 
    rewrite map_map app_mult_cons.
    replace (λ x: string, subst_map vs x) with (subst_map vs ∘ Var) by done.
    rewrite Hrw. 
    assert (Hcons : ∀ xs, map Val xs ++ [ Val #() ] = map Val (xs ++ [ #() ])).
    { intros xs. induction xs; first done. simpl. by rewrite IHxs. }
    rewrite Hcons. iApply ewp_bind_app_mult.
    iApply (ewp_mono _ _ (λ v, (() -{ ρ'; Δ; Γ₃ }-∘ τ') v) with "[HΓ₁] [HΔ HΦ]").
    2: { iIntros "% Hv !>". rewrite -Hcons -Hrw -app_mult_cons.
         iApply (ewp_mono with "[Hv HΔ]"); [by iApply ("Hv" with "HΔ")|].
         iIntros (?) "[Hτ' HΓ₃] !>". iApply "HΦ". iFrame. }
    iSimpl. ewp_pure_steps. 
    iApply (ewp_deep_try_with _ _ _ (λ v, τ v ∗ env_sem_typed Γ₂ vs) with "[HΓ₁] []").
    { iApply ("He" with "HΓ₁"). iIntros "* H {$H}". }
    iLöb as "IH". rewrite {2}deep_handler_unfold.
    iSplit; [|iSplit; iIntros (v c)];
    last (iIntros "?"; by rewrite upcl_bottom).
    - iIntros (v) "[Hτ HΓ₂] //=". ewp_pure_steps.
      rewrite -subst_map_insert. 
      iApply ("Hr" with "[Hτ HΓ₂]"); first solve_env.
      iIntros (?) "[$ _] /=".
    - rewrite upcl_sem_sig_rec_eff.
      iIntros "(%α & %a & -> & Ha & Hκb)". ewp_pure_steps. 
      do 2 (rewrite decide_True; [|split; first done; by injection]). iSimpl.
      rewrite !/lambdas_norm lookup_delete.
      rewrite decide_False; last tauto. iSimpl.
      rewrite decide_False; last done. iSimpl.
      rewrite decide_True; last done. ewp_pure_steps.
      rewrite delete_idemp delete_commute -subst_map_insert -delete_insert_ne; last done.
      rewrite -subst_map_singleton !subst_map_ctx_lambda delete_list_singleton_ne; last done.
      iSimpl. rewrite delete_singleton_ne; last done. rewrite subst_map_app_mult. iSimpl.
      rewrite lookup_insert lookup_singleton_ne; last done. rewrite map_map. 
      replace (map (λ x: string, subst_map {[k := c]} x) (env_dom Δ)) with
              (map Var (env_dom Δ)).
      2: { clear - k c Δ H2. induction Δ as [|[] ]; first done. rewrite env_dom_cons /=.
           rewrite env_dom_cons in H2. edestruct (not_elem_of_cons (env_dom Δ)) as [[] _]; first done.
           rewrite lookup_singleton_ne; last done. by rewrite IHΔ. }
      destruct Δ as [|[x κ'] Δ'] eqn:HΔeq.
      + rewrite !env_dom_nil. iSimpl. ewp_pure_steps. 
        replace Γ₃ with ([] : env Σ) by 
          (symmetry; apply (map_eq_nil fst); by apply list_nil_subseteq). 
        rewrite -subst_map_insert.
        iApply ("Hh" with "[Ha Hκb]"); 
          last (iIntros (?) "[Hτ' _]"; ewp_pure_steps; iFrame; iIntros "_"; ewp_pure_steps; iFrame).
        solve_env. iIntros (u us) "_ Hκ". rewrite env_dom_nil /=. ewp_pure_steps.
        rewrite decide_True; last done.
        iApply (ewp_bind [AppLCtx _]); first done.
        iApply (ewp_mono with "[Hκ Hκb]"); [iApply ("Hκb" with "Hκ")|].
        { iNext. rewrite delete_commute. by iApply "IH". }
        iIntros (?) "H !> /=". by iApply "H".
      + rewrite {5}env_dom_cons. iSimpl. ewp_pure_steps.
        rewrite -subst_map_insert.
        iApply ("Hh" with "[Ha Hκb]"); [|iIntros (u) "[$ _]"].
        iExists v. iFrame. iSplit.
        { iPureIntro. rewrite insert_commute; last done. apply lookup_insert. }
        set k' := (λλ*λ: x, env_dom Δ', w, ((c w) <_ map Var (env_dom ((x, κ')%core :: Δ')) _>) #())%V.
        iExists k'. iSplit; [iPureIntro; apply lookup_insert|].
        iSplitL "Hκb"; last done.
        iIntros (u us) "HΔ Hκ". rewrite /k'.
        iApply (ewp_bind [AppLCtx _]); first done.
        iApply (ewp_app_mult with "HΔ"). iIntros "HΔ". iSimpl.
        ewp_pure_steps. rewrite -subst_map_insert -HΔeq subst_map_app_mult. iSimpl.
        rewrite lookup_insert. 
        set uus := (<[w:=u]> (us ∖ delete (env_dom Δ) us)).
        rewrite map_map. replace (λ x0 : string, (subst_map uus x0)) with (subst_map uus ∘ Var) by done. 
        iDestruct (subst_map_var Δ uus with "[HΔ]") as "(%uus' & %Hrwuus')". 
        { rewrite /uus. rewrite -env_sem_typed_insert; last (by rewrite HΔeq).
          by rewrite -env_sem_typed_difference_delete. }
        rewrite Hrwuus'. 
        rewrite (app_mult_cons (c u)).
        rewrite Hcons.
        iApply ewp_bind_app_mult.
        iApply (ewp_mono with "[Hκb Hκ]").
        { iApply ("Hκb" with "Hκ"). iNext.  iApply "IH". }
        iIntros (u') "Hu' !> /=". rewrite -Hcons -app_mult_cons -Hrwuus'.
        iSpecialize ("Hu'" $! #() uus).
        rewrite /uus -env_sem_typed_insert; last (by rewrite HΔeq).
        rewrite -env_sem_typed_difference_delete; last done. 
        iApply (ewp_mono with "[HΔ Hu']").
        { by iApply ("Hu'" with "HΔ"). }
        iIntros (?) "[$ HΓ₃] !>". 
        rewrite -(env_sem_typed_insert _ _ w); last done.
        by rewrite -env_sem_typed_difference_delete; last (rewrite HΔeq).
  Qed.

End compatibility.
