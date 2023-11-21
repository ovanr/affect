
(* compatibility.v *)

(* 
  The compatibility lemmas are what one gets when the syntactic typing judgment
  is replaced with a semantic typing judgment.
*)

From iris.proofmode Require Import base tactics.
From iris.base_logic.lib Require Import iprop invariants.

(* Hazel Reasoning *)
From hazel.program_logic Require Import weakest_precondition 
                                        tactics 
                                        shallow_handler_reasoning 
                                        deep_handler_reasoning 
                                        state_reasoning.

(* Local imports *)
From haffel.lib Require Import base.
From haffel.lang Require Import hazel.
From haffel.lang Require Import subst_map.
From haffel.logic Require Import iEff.
From haffel.logic Require Import sem_def.
From haffel.logic Require Import tactics.
From haffel.logic Require Import sem_types.
From haffel.logic Require Import sem_env.
From haffel.logic Require Import sem_sub_typing.
From haffel.logic Require Import sem_operators.


Open Scope bi_scope.
Open Scope stdpp_scope.
Open Scope ieff_scope.
  
(* Semantic typing rules. *)

Section compatibility.

  Context `{!heapGS Σ}.
  
  Lemma sem_typed_val Γ τ v : 
    ⊨ᵥ v : τ -∗ Γ ⊨ v : ⊥ : τ ⊨ Γ.
  Proof.
    iIntros "#Hv !# %vs HΓ /=".
    iApply ewp_value. iFrame.
    rewrite /sem_val_typed /tc_opaque.
    iApply "Hv".
  Qed.

  (* Base rules *)
  
  Lemma sem_typed_unit Γ : 
    ⊢ Γ ⊨ #() : ⊥ : () ⊨ Γ.
  Proof.
    iIntros (vs) "!# HΓ₁ //=". iApply ewp_value. by iFrame.
  Qed.
  
  Lemma sem_typed_bool Γ (b : bool) : 
    ⊢ Γ ⊨ #b : ⊥ : 𝔹 ⊨ Γ.
  Proof.
    iIntros (vs) "!# HΓ₁ //=". iApply ewp_value. 
    iSplitR; first (iExists b); done.
  Qed.
  
  Lemma sem_typed_int Γ (i : Z) : 
    ⊢ Γ ⊨ #i : ⊥ : ℤ ⊨ Γ.
  Proof.
    iIntros (vs) "!# HΓ₁ //=". iApply ewp_value. 
    iSplitR; first (iExists i); done.
  Qed.
  
  Lemma sem_typed_var Γ x τ : 
    ⊢ (x, τ) :: Γ ⊨ x : ⊥ : τ ⊨ Γ.
  Proof.
    iIntros (vs) "!# /= [%v (%Hrw & Hτ & HΓ₁)] /=". 
    rewrite Hrw. iApply ewp_value. iFrame.
  Qed.

  Lemma sem_typed_void_in_env Γ₁ Γ₂ e x τ : 
    ⊢ (x, Void) :: Γ₁ ⊨ e : ⊥ : τ ⊨ Γ₂.
  Proof.
    iIntros (vs) "!# /= [%v (%Hrw & [] & _)] /=". 
  Qed.

  Lemma sem_typed_closure f x e τ σ κ :
    match f with BNamed f => BNamed f ≠ x | BAnon => True end →
    (x, τ) ::? (f, τ -{ σ }-> κ) ::? [] ⊨ e : σ : κ ⊨ [] -∗ 
    ⊨ᵥ (rec: f x := e) : (τ -{ σ }-> κ).
  Proof.
      iIntros (?) "#He !#". iLöb as "IH".
      iIntros "%v !# Hτ /=". 
      ewp_pure_steps. destruct x as [|x]; destruct f as [|f]; simpl.
      - rewrite - {3} [e]subst_map_empty. 
        iApply (ewp_pers_mono with "[He]"); first (by iApply "He").
        iIntros "!# % [$ _] //=". 
      - rewrite -subst_map_singleton.
        iApply ewp_pers_mono; [iApply "He"; solve_env|solve_env].
        iIntros "!# % [$ _] //=".
      - rewrite -subst_map_singleton.
        iApply (ewp_pers_mono with "[Hτ]"); [iApply "He"; solve_env|solve_env].
        iIntros "!# % [$ _] //=".
      - rewrite -(subst_map_singleton f) -subst_map_singleton subst_map_union.
        iApply (ewp_pers_mono with "[Hτ]"); [iApply "He"|iIntros "!# % [$ _] //="].
        rewrite -insert_union_singleton_r; [solve_env|apply lookup_singleton_ne];
        intros ?; simplify_eq.
  Qed.

  Lemma sem_typed_Tclosure e τ :
    (∀ α, ⊨ e : ⊥ : τ α) -∗ 
    ⊨ᵥ (Λ: e) : (∀T: α, τ α).
  Proof.
    iIntros "#He !# %u !#". ewp_pure_steps.
    rewrite - {2} [e]subst_map_empty.
    iSpecialize ("He" $! u).
    iApply (ewp_pers_mono with "[He]"); [iApply "He"|]; first done. 
    iIntros "!# % [$ _] //=".
  Qed.

  (* Signature abstraction and application *)
  Lemma sem_typed_Sclosure e C : 
    (∀ θ, ⊨ e : ⊥ : C θ) -∗
    ⊨ᵥ (Λ: e) : (∀S: θ , C θ)%T.
  Proof.
    iIntros "#He !# %σ !# /=".
    ewp_pure_steps. rewrite - {2} [e]subst_map_empty. 
    iApply (ewp_pers_mono with "[He]"); [by iApply "He"|].
    iIntros "!# % [$ _] //=". 
  Qed.

  Lemma sem_typed_closure_to_unrestricted x e τ σ κ :
    ⊨ᵥ (λ: x, e) : (τ -{ σ }-∘ κ) -∗
    ⊨ᵥ (λ: x, e) : (τ -{ σ }-> κ).
  Proof. 
    iIntros "#He !# %w !# Hτ". 
    iSpecialize ("He" $! w).
    iApply ("He" with "Hτ").
  Qed.

  (* Subsumption rule *)
  
  Lemma sem_typed_sub Γ₁ Γ₁' Γ₂ Γ₂' e σ σ' τ τ':
    Γ₁  ≤E Γ₁' -∗
    Γ₂' ≤E Γ₂ -∗
    σ'  ≤S σ -∗ 
    τ'  ≤T τ -∗
    Γ₁' ⊨ e : σ' : τ' ⊨ Γ₂' -∗ Γ₁ ⊨ e : σ : τ ⊨ Γ₂.
  Proof.
    iIntros "#HΓ₁le #HΓ₂le #Hσle #Hτle #He !# %vs HΓ₁ //=".
    iDestruct ("HΓ₁le" with "HΓ₁") as "HΓ₁'".
    iApply ewp_os_prot_mono; [iApply "Hσle"|].
    iApply (ewp_pers_mono with "[HΓ₁']"); first (by iApply "He").
    iIntros "!# % [Hτ HΓ₂] //= !>".
    iSplitL "Hτ"; [by iApply "Hτle"|by iApply "HΓ₂le"].
  Qed. 
  
  (* Convenient Subsumption rules *)
  Lemma sem_typed_sub_ty τ' τ Γ₁ Γ₂ e σ :
  τ' ≤T τ -∗
  (Γ₁ ⊨ e : σ : τ' ⊨ Γ₂) -∗ Γ₁ ⊨ e : σ : τ ⊨ Γ₂.
  Proof.
    iIntros "#Hτ".
    iApply (sem_typed_sub Γ₁ Γ₁ Γ₂ Γ₂ _ σ σ);
      (iApply sig_le_refl || iApply env_le_refl || done). 
  Qed.

  Lemma sem_typed_sub_sig σ σ' Γ₁ Γ₂ e τ :
    σ' ≤S σ -∗
    (Γ₁ ⊨ e : σ' : τ ⊨ Γ₂) -∗ Γ₁ ⊨ e : σ : τ ⊨ Γ₂.
  Proof.
    iIntros "#Hσ".
    iApply (sem_typed_sub Γ₁ Γ₁ Γ₂ Γ₂ _ σ σ' τ τ);
      (iApply env_le_refl || iApply ty_le_refl || done).
  Qed.

  Lemma sem_typed_sub_nil Γ₁ Γ₂ e τ σ :
    (Γ₁ ⊨ e : ⊥ : τ ⊨ Γ₂) -∗ Γ₁ ⊨ e : σ : τ ⊨ Γ₂.
  Proof. iApply sem_typed_sub_sig. iApply sig_le_nil. Qed.
  
  Lemma sem_typed_sub_env Γ₁ Γ₁' Γ₂ e σ τ :
    Γ₁ ≤E Γ₁' -∗
    (Γ₁' ⊨ e : σ : τ ⊨ Γ₂) -∗ Γ₁ ⊨ e : σ : τ ⊨ Γ₂.
  Proof.
    iIntros "#HΓ₁".
    iApply (sem_typed_sub Γ₁ Γ₁' Γ₂ Γ₂ _ σ σ τ τ);
      (iApply sig_le_refl || iApply env_le_refl || iApply ty_le_refl || done).
  Qed.

  Lemma sem_typed_sub_env_final Γ₁ Γ₂ Γ₂' e σ τ :
    Γ₂' ≤E Γ₂ -∗
    (Γ₁ ⊨ e : σ : τ ⊨ Γ₂') -∗ Γ₁ ⊨ e : σ : τ ⊨ Γ₂.
  Proof.
    iIntros "#HΓ₂".
    iApply (sem_typed_sub Γ₁ Γ₁ Γ₂ Γ₂' _ σ σ τ τ);
      (iApply sig_le_refl || iApply env_le_refl || iApply ty_le_refl || done).
  Qed.

  Lemma sem_typed_swap_second Γ₁ Γ₂ x y e σ τ₁ τ₂ κ :
    ((y, τ₂) :: (x, τ₁) :: Γ₁ ⊨ e : σ : κ ⊨ Γ₂) -∗ 
    ((x, τ₁) :: (y, τ₂) :: Γ₁ ⊨ e : σ : κ ⊨ Γ₂).
  Proof.
    iIntros "He".
    iApply sem_typed_sub_env; [iApply env_le_swap_second|iApply "He"].
  Qed.

  Lemma sem_typed_swap_third Γ₁ Γ₂ x y z e σ τ₁ τ₂ τ₃ κ :
    ((z, τ₃) :: (x, τ₁) :: (y, τ₂) :: Γ₁ ⊨ e : σ : κ ⊨ Γ₂) -∗ 
    ((x, τ₁) :: (y, τ₂) :: (z, τ₃) :: Γ₁ ⊨ e : σ : κ ⊨ Γ₂).
  Proof.
    iIntros "He".
    iApply sem_typed_sub_env; [|iApply "He"].
    iApply env_le_trans; iApply env_le_swap_third.
  Qed.

  Lemma sem_typed_swap_fourth Γ₁ Γ₂ x y z z' e σ τ₁ τ₂ τ₃ τ₄ κ :
    ((z', τ₄) :: (x, τ₁) :: (y, τ₂) :: (z, τ₃) :: Γ₁ ⊨ e : σ : κ ⊨ Γ₂) -∗ 
    ((x, τ₁) :: (y, τ₂) :: (z, τ₃) :: (z', τ₄) :: Γ₁ ⊨ e : σ : κ ⊨ Γ₂).
  Proof.
    iIntros "He".
    iApply sem_typed_sub_env; [|iApply "He"].
    do 2 (iApply env_le_trans; [iApply env_le_swap_fourth|]).
    iApply env_le_swap_fourth.
  Qed.

  Lemma sem_typed_swap_env_singl Γ₁ Γ₂ x e σ τ κ :
    (Γ₁ ++ [(x, τ)] ⊨ e : σ : κ ⊨ Γ₂) -∗ 
    ((x, τ) :: Γ₁ ⊨ e : σ : κ ⊨ Γ₂). 
  Proof.
    iIntros "He".
    iApply sem_typed_sub_env; [|iApply "He"].
    iApply env_le_swap_env_singl.
  Qed.

  Lemma sem_typed_contraction Γ₁ Γ₂ x e σ τ κ :
    copy_ty τ -∗
    (x, τ) :: (x, τ) :: Γ₁ ⊨ e : σ : κ ⊨ Γ₂ -∗ 
    (x, τ) :: Γ₁ ⊨ e : σ : κ ⊨ Γ₂.
  Proof.
    iIntros "#τ He".
    iApply sem_typed_sub_env; 
      [by iApply env_le_copy_contraction|iApply "He"].
  Qed.

  Lemma sem_typed_weaken Γ₁ Γ₂ x e σ τ κ :
    (Γ₁ ⊨ e : σ : κ ⊨ Γ₂) -∗ ((x, τ) :: Γ₁ ⊨ e : σ : κ ⊨ Γ₂).
  Proof.
    iIntros "He".
    iApply sem_typed_sub_env; [iApply env_le_weaken|iApply "He"].
  Qed.

  Lemma sem_typed_frame Γ₁ e σ x τ κ Γ₂:
    Γ₁ ⊨ e : σ : κ ⊨ Γ₂ -∗
    (x, τ) :: Γ₁ ⊨ e : σ : κ ⊨ (x, τ) :: Γ₂.
  Proof.
    iIntros "#He %vs !# (%v & %Hrw & Hτ & HΓ₁)".
    iApply (ewp_mono with "[HΓ₁]"); first (by iApply "He").
    iIntros (w) "[Hκ HΓ₂]". solve_env.
  Qed.

  Lemma sem_typed_frame_env Γ₁ Γ' e σ τ Γ₂ :
    Γ₁ ⊨ e : σ : τ ⊨ Γ₂ -∗
    Γ' ++ Γ₁ ⊨ e : σ : τ ⊨ Γ' ++ Γ₂.
  Proof.
    iIntros "#He %vs !# HΓ'Γ₁".
    iDestruct (env_sem_typed_app with "HΓ'Γ₁") as "[HΓ' HΓ₁]".
    iInduction Γ' as [|[x κ]] "IH".
    { simpl. by iApply "He". }
    iDestruct "HΓ'" as "(%v & %Hrw & Hκ & HΓ'')".
    iApply (ewp_mono with "[HΓ'' HΓ₁]").
    { iApply ("IH" with "HΓ'' HΓ₁"). }
    iIntros (w) "[$ HΓ] !>". solve_env.
  Qed.

  (* λ-calculus rules *)

  Lemma sem_typed_afun Γ₁ Γ₂ x e τ σ κ: 
    x ∉ (env_dom Γ₁) → x ∉ (env_dom Γ₂) →
    (x,τ) ::? Γ₁ ⊨ e : σ : κ ⊨ [] -∗
    Γ₁ ++ Γ₂ ⊨ (λ: x, e) : ⊥ : (τ -{ σ }-∘ κ) ⊨ Γ₂.
  Proof.
    iIntros (??) "#He !# %vs HΓ₁₂ //=".
    iDestruct (env_sem_typed_app with "HΓ₁₂") as "[HΓ₁ HΓ₂]".
    ewp_pure_steps. iFrame.
    iIntros (w) "Hτ". 
    ewp_pure_steps. rewrite subst'_subst_map_insert.
    iApply (ewp_pers_mono with "[Hτ HΓ₁]"); [iApply "He"|iIntros "!# % [$ _] //="].
    destruct x; solve_env. 
  Qed.

  Lemma sem_typed_ufun Γ₁ Γ₂ f x e τ σ κ:
    x ∉ (env_dom Γ₁) → f ∉ (env_dom Γ₁) → 
    match f with BNamed f => BNamed f ≠ x | BAnon => True end →
    copy_env Γ₁ -∗
    (x, τ) ::? (f, τ -{ σ }-> κ) ::? Γ₁ ⊨ e : σ : κ ⊨ [] -∗
    Γ₁ ++ Γ₂ ⊨ (rec: f x := e) : ⊥ : (τ -{ σ }-> κ) ⊨ Γ₂.
  Proof.
    iIntros (???) "#HcpyΓ₁ #He !# %vs HΓ₁₂ //=".
    ewp_pure_steps.
    rewrite env_sem_typed_app. iDestruct "HΓ₁₂" as "[HΓ₁' $]".
    iDestruct ("HcpyΓ₁" with "HΓ₁'") as "#HΓ₁".
    iLöb as "IH".
    iIntros "!# %w Hτ". 
    ewp_pure_steps. destruct f; destruct x; simpl.
    - iApply ewp_pers_mono; [by iApply "He"|iIntros "!# % [$ _] //="].
    - rewrite -subst_map_insert. 
      iApply (ewp_pers_mono with "[Hτ]"); 
        [iApply "He"; solve_env|iIntros "!# % [$ _] //="].
    - rewrite -subst_map_insert.
      iApply (ewp_pers_mono with "[Hτ]"); 
        [iApply "He"; solve_env|iIntros "!# % [$ _] //="].
      by iApply "IH".
    - assert (s ≠ s0) by (intros ?; simplify_eq).
      rewrite subst_subst_ne; last done.
      rewrite -subst_map_insert.
      rewrite -delete_insert_ne; last done. 
      rewrite -subst_map_insert.
      iApply (ewp_pers_mono with "[Hτ]"); 
        [iApply "He"; solve_env|iIntros "!# % [$ _] //="].
      { by iApply "IH". }
      by do 2 (rewrite -env_sem_typed_insert; last done).
  Qed.

  Lemma sem_typed_ufun_poly_rec Γ₁ Γ₂ f x e τ σ κ:
    x ∉ (env_dom Γ₁) → f ∉ (env_dom Γ₁) → 
    match x with BNamed x => BNamed x ≠ f | BAnon => True end →
    copy_env Γ₁ -∗
    (∀ ι, (x, τ ι) ::? (f, ∀T: α, τ α -{ σ α }-> κ α) ::? Γ₁ ⊨ e : σ ι : κ ι ⊨ []) -∗
    Γ₁ ++ Γ₂ ⊨ (rec: f <> := λ: x, e) : ⊥ : (∀T: α, τ α -{ σ α }-> κ α) ⊨ Γ₂.
  Proof.
    iIntros (???) "#HcpyΓ₁ #He !# %vs HΓ₁₂ //=".
    ewp_pure_steps. rewrite env_sem_typed_app. 
    iDestruct "HΓ₁₂" as "[HΓ₁' $]".
    iDestruct ("HcpyΓ₁" with "HΓ₁'") as "#HΓ₁".
    iLöb as "IH".
    iIntros (α) "!#". ewp_pure_steps.
    destruct f; destruct x; simpl; 
    ewp_pure_steps; iIntros (v) "!# Hτ"; ewp_pure_steps.
    - iApply ewp_pers_mono; first (by iApply "He").  
      iIntros "!# % [$ _] //=".
    - rewrite -subst_map_insert. 
      iApply (ewp_pers_mono with "[Hτ]"); first (iApply "He"; solve_env).  
      iIntros "!# % [$ _] //=".
    - rewrite -subst_map_insert.
      iApply (ewp_pers_mono with "[Hτ]"); first (iApply "He"; solve_env; by iApply "IH") .
      iIntros "!# % [$ _] //=".
    - assert (s ≠ s0) by (intros ?; simplify_eq).
      rewrite decide_True; last auto.
      rewrite subst_subst_ne; last done.
      rewrite -subst_map_insert.
      rewrite -delete_insert_ne; last done. 
      rewrite -subst_map_insert.
      iApply (ewp_pers_mono with "[Hτ]"); first (iApply "He"; solve_env).  
      + by iApply "IH". 
      + by do 2 (rewrite -env_sem_typed_insert; last done).
      + iIntros "!# % [$ _] //=".
  Qed.

  Lemma sem_typed_let Γ₁ Γ₂ Γ₃ x e₁ e₂ τ σ κ: 
    x ∉ (env_dom Γ₂) → x ∉ (env_dom Γ₃) →
    Γ₁ ⊨ e₁ : σ : τ ⊨ Γ₂ -∗
    (x, τ) :: Γ₂ ⊨ e₂ : σ : κ ⊨ Γ₃ -∗
    Γ₁ ⊨ (let: x := e₁ in e₂) : σ : κ ⊨ Γ₃.
  Proof.
    iIntros (??) "#He₁ #He₂ !# %vs HΓ₁ /=".
    iApply (ewp_bind ([AppRCtx _])); first done. simpl.
    iApply (ewp_pers_mono with "[HΓ₁]"); first (by iApply "He₁").
    iIntros "!# % [Hτ HΓ₂] !> /=". ewp_pure_steps.
    rewrite -subst_map_insert.
    iApply (ewp_pers_mono with "[Hτ HΓ₂]"); first (iApply "He₂"; solve_env).
    iIntros "!# % [Hτκ HΓ₃] !> /=".
    solve_env.
  Qed.

  Lemma sem_typed_app Γ₁ Γ₂ Γ₃ e₁ e₂ τ σ κ: 
    Γ₂ ⊨ e₁ : σ : (τ -{ σ }-∘ κ) ⊨ Γ₃ -∗
    Γ₁ ⊨ e₂ : σ : τ ⊨ Γ₂ -∗
    Γ₁ ⊨ (e₁ e₂) : σ : κ ⊨ Γ₃.
  Proof.
    iIntros "#He₁ #He₂ !# %vs HΓ₁ /=".
    iApply (ewp_bind [AppRCtx _]); first done.
    iApply (ewp_pers_mono with "[HΓ₁]"); first (by iApply "He₂").
    iIntros "!# % [Hτ HΓ₂] !> /=".
    iApply (ewp_bind [AppLCtx _]); first done.
    iApply (ewp_mono with "[HΓ₂]"); first (by iApply "He₁").
    iIntros "% [Hτκ HΓ₃'] !> /=".
    iApply (ewp_mono with "[Hτ Hτκ]"); first (by iApply "Hτκ").
    iIntros "% $ !> //=".
  Qed.

  Lemma sem_typed_seq Γ₁ Γ₂ Γ₃ e₁ e₂ τ σ κ: 
    Γ₁ ⊨ e₁ : σ : τ ⊨ Γ₂ -∗
    Γ₂ ⊨ e₂ : σ : κ ⊨ Γ₃ -∗
    Γ₁ ⊨ (e₁ ;; e₂) : σ : κ ⊨ Γ₃.
  Proof.
    iIntros "#He₁ #He₂ !# %vs HΓ₁ /=".
    iApply (ewp_bind ([AppRCtx _])); first done. simpl.
    iApply (ewp_pers_mono with "[HΓ₁]"); first (by iApply "He₁").
    iIntros "!# % [Hτ HΓ₂] !> /=". ewp_pure_steps.
    iApply (ewp_pers_mono with "[Hτ HΓ₂]"); first (by iApply "He₂").
    iIntros "!# % [Hτκ HΓ₃] !> /=". iFrame.
  Qed.

  Lemma sem_typed_pair Γ₁ Γ₂ Γ₃ e₁ e₂ τ σ κ: 
    Γ₂ ⊨ e₁ : σ : τ ⊨ Γ₃ -∗
    Γ₁ ⊨ e₂ : σ : κ ⊨ Γ₂ -∗
    Γ₁ ⊨ (e₁,e₂) : σ : (τ × κ) ⊨ Γ₃.
  Proof.
    iIntros "#He₁ #He₂ !# %vs HΓ₁ //=".
    iApply (ewp_bind ([PairRCtx (subst_map vs e₁)])); first done.
    iApply (ewp_mono with "[HΓ₁]"); first (by iApply "He₂").
    iIntros "% [Hτ HΓ₂] !> /=".
    iApply (ewp_bind ([PairLCtx v])); first done.
    iApply (ewp_mono with "[HΓ₂]"); first (by iApply "He₁").
    iIntros (w) "[Hκw HΓ₃] //= !>". ewp_pure_steps.
    solve_env.
  Qed.
  

  Lemma sem_typed_pair_elim Γ₁ Γ₂ Γ₃ x₁ x₂ e₁ e₂ τ σ κ ι: 
    x₁ ∉ (env_dom Γ₂) → x₂ ∉ (env_dom Γ₂) →
    x₁ ∉ (env_dom Γ₃) → x₂ ∉ (env_dom Γ₃) →
    x₁ ≠ x₂ →
    Γ₁ ⊨ e₁ : σ : (τ × κ) ⊨ Γ₂ -∗
    (x₁, τ) :: (x₂, κ) :: Γ₂ ⊨ e₂ : σ : ι ⊨ Γ₃ -∗
    Γ₁ ⊨ (let: (x₁, x₂) := e₁ in e₂) : σ : ι ⊨ Γ₃.
  Proof.
    iIntros (?????) "#He₁ #He₂ !# %vs HΓ₁ //=". ewp_pure_steps.
    set ex1x2 := (λ: x₁ x₂, subst_map (binder_delete x₂ 
                                      (binder_delete x₁ vs)) e₂)%V. 
    iApply (ewp_bind ([AppLCtx ex1x2; AppRCtx pair_elim])); first done.
    iApply (ewp_pers_mono with "[HΓ₁]"); first (by iApply "He₁").
    iIntros "!# % [Hτκv HΓ₂] //= !>". 
    unfold pair_elim. ewp_pure_steps.
    iDestruct "Hτκv" as "(%v₁ & %v₂ & -> & Hτ & Hκ)".
    unfold ex1x2. ewp_pure_steps. 
    destruct (decide _) as [[]|[]]; [|split; [done|congruence]].
    rewrite delete_commute -subst_map_insert -delete_insert_ne; last congruence.
    rewrite -subst_map_insert.
    iApply (ewp_pers_mono with "[Hτ Hκ HΓ₂]"); first (iApply "He₂").
    - iExists v₁. iFrame. iSplitL "".
      { rewrite lookup_insert_ne; last done. by rewrite lookup_insert. }
      iExists v₂. iFrame; iSplitL ""; [by rewrite lookup_insert|].
      by do 2 (rewrite -env_sem_typed_insert; last done).
    - iIntros "!# % [Hιv HΓ₃]". iFrame.
      rewrite -(env_sem_typed_insert _ _ x₂ v₂); last done.
      by rewrite -(env_sem_typed_insert _ _ x₁ v₁).
  Qed.
  
  Lemma sem_typed_left_inj Γ₁ Γ₂ e τ σ κ: 
    Γ₁ ⊨ e : σ : τ ⊨ Γ₂ -∗
    Γ₁ ⊨ InjL e : σ : (τ + κ) ⊨ Γ₂.
  Proof.
    iIntros "#He !# %vs HΓ₁ //=".
    iApply (ewp_bind [InjLCtx]); first done.
    iApply (ewp_pers_mono with "[HΓ₁]"); first (by iApply "He").
    iIntros "!# % [Hτ HΓ₂] /= !>". ewp_pure_steps.
    iFrame. iExists v. iLeft. by iFrame.
  Qed.

  Lemma sem_typed_right_inj Γ₁ Γ₂ e τ σ κ: 
    Γ₁ ⊨ e : σ : κ ⊨ Γ₂ -∗
    Γ₁ ⊨ InjR e : σ : (τ + κ) ⊨ Γ₂.
  Proof.
    iIntros "#He !# %vs HΓ₁ //=".
    iApply (ewp_bind [InjRCtx]); first done.
    iApply (ewp_pers_mono with "[HΓ₁]"); first (by iApply "He").
    iIntros "!# % [Hκ HΓ₂] /= !>". ewp_pure_steps.
    iFrame. iExists v. iRight. by iFrame.
  Qed.

  Lemma sem_typed_match Γ₁ Γ₂ Γ₃ e₁ x y e₂ e₃ τ σ κ ι: 
    x ∉ env_dom Γ₂ → x ∉ env_dom Γ₃ → y ∉ env_dom Γ₂ → y ∉ env_dom Γ₃ →
    Γ₁ ⊨ e₁ : σ : (τ + κ) ⊨ Γ₂ -∗
    (x, τ) ::? Γ₂ ⊨ e₂ : σ : ι ⊨ Γ₃ -∗
    (y, κ) ::? Γ₂ ⊨ e₃ : σ : ι ⊨ Γ₃ -∗
    Γ₁ ⊨ match: e₁ with InjL x => e₂ | InjR y => e₃ end : σ : ι ⊨ Γ₃.
  Proof.
    iIntros (????) "#He₁ #He₂ #He₃ !# %vs HΓ₁ //=".
    iApply (ewp_bind [CaseCtx _ _]); first done.
    iApply (ewp_pers_mono with "[HΓ₁]"); first (by iApply "He₁").
    iIntros "!# %v [(%w & [(-> & Hτ)|(-> & Hκ)]) HΓ₂] //= !>"; ewp_pure_steps.
    - destruct x; simpl.
      + iApply (ewp_pers_mono with "[HΓ₂ Hτ]"); [by iApply "He₂"|eauto].
      + rewrite -subst_map_insert.
        iApply (ewp_pers_mono with "[HΓ₂ Hτ]"); first (iApply "He₂"; solve_env).
        iIntros "!# % [$ HΓ₃] //=". solve_env.
    - destruct y; simpl.
      + iApply (ewp_pers_mono with "[HΓ₂ Hκ]"); [iApply "He₃"; solve_env|eauto].
      + rewrite -subst_map_insert.
        iApply (ewp_pers_mono with "[HΓ₂ Hκ]"); [iApply "He₃"; solve_env|].
        iIntros "!# % [$ HΓ₃] //=". solve_env.
  Qed.

  Lemma sem_typed_none Γ₁ τ: 
    ⊢ Γ₁ ⊨ NONE : ⊥ : Option τ ⊨ Γ₁.
  Proof.
    iIntros. iApply sem_typed_left_inj. iApply sem_typed_unit. 
  Qed.

  Lemma sem_typed_some Γ₁ Γ₂ e σ τ: 
    Γ₁ ⊨ e : σ : τ ⊨ Γ₂ -∗ 
    Γ₁ ⊨ SOME e : σ : Option τ ⊨ Γ₂.
  Proof.
    iIntros "He". iApply sem_typed_right_inj. iApply "He".
  Qed.

  Lemma sem_typed_match_option Γ₁ Γ₂ Γ₃ e₁ x e₂ e₃ σ κ ι: 
    x ∉ env_dom Γ₂ → x ∉ env_dom Γ₃ →
    Γ₁ ⊨ e₁ : σ : Option κ ⊨ Γ₂ -∗
    Γ₂ ⊨ e₂ : σ : ι ⊨ Γ₃ -∗
    (x, κ) :: Γ₂ ⊨ e₃ : σ : ι ⊨ Γ₃ -∗
    Γ₁ ⊨ match: e₁ with NONE => e₂ | SOME x => e₃ end : σ : ι ⊨ Γ₃.
  Proof.
    iIntros (??) "#He₁ #He₂ #He₃ !# %vs HΓ₁ //=".
    iApply (ewp_bind [CaseCtx _ _]); first done.
    iApply (ewp_pers_mono with "[HΓ₁]"); first (by iApply "He₁").
    iIntros "!# %v [(%w & [(-> & _)|(-> & Hκ)]) HΓ₂] !> //="; ewp_pure_steps.
    - iApply (ewp_pers_mono with "[HΓ₂]"); [iApply "He₂"; solve_env|eauto].
    - rewrite -subst_map_insert.
      iApply (ewp_pers_mono with "[HΓ₂ Hκ]"); [iApply "He₃"; solve_env|].
      iIntros "!# % [$ HΓ₃] //=". solve_env.
  Qed.

  Lemma sem_typed_bin_op Γ₁ Γ₂ Γ₃ e₁ e₂ op τ κ ι σ: 
    typed_bin_op op τ κ ι →
    Γ₂ ⊨ e₁ : σ : τ ⊨ Γ₃ -∗
    Γ₁ ⊨ e₂ : σ : κ ⊨ Γ₂ -∗
    Γ₁ ⊨ BinOp op e₁ e₂ : σ : ι ⊨ Γ₃.
  Proof.
    iIntros (Hop) "#He₁ #He₂ !# %vs HΓ₁ //=".
    iApply (ewp_bind [BinOpRCtx _ _]); first done.
    iApply (ewp_mono with "[HΓ₁]"); [iApply "He₂"; solve_env|eauto].
    iIntros "%v [Hκ HΓ₂] //= !>". 
    iApply (ewp_bind [BinOpLCtx _ _]); first done.
    iApply (ewp_mono with "[HΓ₂]"); [iApply "He₁"; solve_env|eauto].
    iIntros "%w [Hτ HΓ₂] //= !>".
    destruct op; inversion_clear Hop;
      iDestruct "Hτ" as "(%n1 & ->)";
      iDestruct "Hκ" as "(%n2 & ->)";
      ewp_pure_steps; try done; eauto.
  Qed.
  
  Lemma sem_typed_if Γ₁ Γ₂ Γ₃ e₁ e₂ e₃ σ τ: 
    Γ₁ ⊨ e₁ : σ : 𝔹 ⊨ Γ₂ -∗
    Γ₂ ⊨ e₂ : σ : τ ⊨ Γ₃ -∗
    Γ₂ ⊨ e₃ : σ : τ ⊨ Γ₃ -∗
    Γ₁ ⊨ (if: e₁ then e₂ else e₃) : σ : τ ⊨ Γ₃.
  Proof.
    iIntros "#He₁ #He₂ #He₃ !# %vs HΓ₁ //=".
    iApply (ewp_bind [IfCtx (subst_map vs e₂) (subst_map vs e₃)]) ;first done.
    iApply (ewp_pers_mono with "[HΓ₁]"); [iApply "He₁"; solve_env|eauto].
    iIntros "!# %v ((%b & ->) & HΓ₂) //= !>".
    destruct b; ewp_pure_steps.
    - iApply (ewp_pers_mono with "[HΓ₂]"); [iApply "He₂"; solve_env|eauto].
    - iApply (ewp_pers_mono with "[HΓ₂]"); [iApply "He₃"; solve_env|eauto].
  Qed.
  
  (* Type abstraction and application *)
  Lemma sem_typed_TLam Γ₁ Γ₂ e C : 
    copy_env Γ₁ -∗
    (∀ α, Γ₁ ⊨ e : ⊥ : C α ⊨ []) -∗
    Γ₁ ++ Γ₂ ⊨ (Λ: e) : ⊥ : (∀T: α , C α)%T ⊨ Γ₂.
  Proof.
    iIntros "#Hcpy #He !# %vs HΓ₁₂ //=".
    iDestruct (env_sem_typed_app with "HΓ₁₂") as "[HΓ₁ HΓ₂]".
    iDestruct ("Hcpy" with "HΓ₁") as "#HΓ₁'".
    ewp_pure_steps. iIntros "{$HΓ₂} %α //= !#". ewp_pure_steps.
    iApply ewp_pers_mono; [iApply "He"; solve_env|].
    iIntros "!# %w [$ _] //=".
  Qed.

  Lemma sem_typed_TApp Γ₁ Γ₂ e σ τ C :
    Γ₁ ⊨ e : σ : (∀T: α , C α) ⊨ Γ₂ -∗
    Γ₁ ⊨ e <_> : σ : C τ ⊨ Γ₂. 
  Proof.
    iIntros "#He !# %vs HΓ₁ /=".
    iApply (ewp_bind [AppLCtx _]); first done.
    iApply (ewp_mono with "[HΓ₁]"); [iApply "He"; solve_env|].
    iIntros "%w [Hw HΓ₂] //= !>".
    iApply ewp_os_prot_mono; [iApply sig_le_nil|].
    iApply (ewp_mono with "[Hw]"); [iApply "Hw"|].
    iIntros "% HC !>". iFrame "#∗".
  Qed.

  (* Signature abstraction and application *)
  Lemma sem_typed_SLam Γ₁ Γ₂ e C : 
    copy_env Γ₁ -∗
    (∀ θ, Γ₁ ⊨ e : ⊥ : C θ ⊨ []) -∗
    Γ₁ ++ Γ₂ ⊨ (Λ: e) : ⊥ : (∀S: θ , C θ)%T ⊨ Γ₂.
  Proof.
    iIntros "#Hcpy #He !# %vs HΓ₁₂ /=".
    iDestruct (env_sem_typed_app with "HΓ₁₂") as "[HΓ₁ HΓ₂]".
    ewp_pure_steps. iFrame.
    iDestruct ("Hcpy" with "HΓ₁") as "#HΓ₁'".
    iIntros (σ). ewp_pure_steps. iIntros "!#".
    ewp_pure_steps.
    iApply ewp_pers_mono; [by iApply "He"|].
    iIntros "!# % [$ _] //=".
  Qed.

  Lemma sem_typed_SApp Γ₁ Γ₂ e σ σ' C : 
    Γ₁ ⊨ e : σ : (∀S: θ , C θ) ⊨ Γ₂ -∗
    Γ₁ ⊨ e <_> : σ : C σ' ⊨ Γ₂. 
  Proof.
    iIntros "#He !# %vs HΓ₁ /=".
    iApply (ewp_bind [AppLCtx _]); first done.
    iApply (ewp_pers_mono with "[HΓ₁]"); [by iApply "He"|].
    iIntros "!# %v [HC HΓ₂] /= !>".
    iApply ewp_os_prot_mono; [iApply sig_le_nil|].
    iApply (ewp_mono with "[HC]"); [iApply ("HC" $! σ')|].
    iIntros "%w HCσ !>". iFrame "∗#".
  Qed.

  (* Existential type packing and unpacking *)
  Lemma sem_typed_pack Γ₁ Γ₂ σ e C τ :
    Γ₁ ⊨ e : σ : C τ ⊨ Γ₂ -∗
    Γ₁ ⊨ (pack: e) : σ : (∃: α, C α) ⊨ Γ₂. 
  Proof.
    iIntros "#He %vs !# HΓ₁ //=".
    iApply (ewp_bind [AppRCtx _]); first done.
    iApply (ewp_pers_mono with "[HΓ₁]"); [by iApply "He"|].
    iIntros "!# %v [Hτv HΓ₂] //= !>".
    unfold exist_pack. ewp_pure_steps. iFrame.
    by iExists τ. 
  Qed.

  Lemma sem_typed_unpack Γ₁ Γ₂ Γ₃ x σ e₁ e₂ κ C :
    x ∉ env_dom Γ₂ → x ∉ env_dom Γ₃ →
    Γ₁ ⊨ e₁ : σ : (∃: α, C α) ⊨ Γ₂ -∗
    (∀ τ, (x, C τ) :: Γ₂ ⊨ e₂ : σ : κ ⊨ Γ₃) -∗
    Γ₁ ⊨ (unpack: x := e₁ in e₂) : σ : κ ⊨ Γ₃.
  Proof.
    iIntros (??) "#He₁ #He₂ %vs !# HΓ₁ //=".
    iApply (ewp_bind [AppRCtx _]); first done.
    iApply (ewp_pers_mono with "[HΓ₁]"); [by iApply "He₁"|].
    iIntros "!# %w [(%τ & Hτw) HΓ₂] //= !>". unfold exist_unpack.
    ewp_pure_steps. rewrite -subst_map_insert.
    iApply (ewp_pers_mono with "[HΓ₂ Hτw]"); [iApply "He₂";solve_env|].
    iIntros "!# %u [Hκ HΓ₃]". solve_env.
  Qed.

  (* Recursive type rules *)
  Lemma sem_typed_fold Γ₁ Γ₂ e σ C `{NonExpansive C}:
    Γ₁ ⊨ e : σ : (C (μT: α, C α)) ⊨ Γ₂ -∗
    Γ₁ ⊨ (fold: e) : σ : (μT: α, C α) ⊨ Γ₂.
  Proof.
    iIntros "#He %vs !# HΓ₁ //=".
    iApply (ewp_bind [AppRCtx _]); first done.
    iApply (ewp_pers_mono with "[HΓ₁]"); [by iApply "He"|].
    iIntros "!# %w [HC HΓ₂] //= !>".
    unfold rec_fold. ewp_pure_steps. 
    iFrame. by iApply sem_ty_rec_unfold. 
  Qed.

  Lemma sem_typed_unfold Γ₁ Γ₂ e σ C `{NonExpansive C}:
    Γ₁ ⊨ e : σ : (μT: α, C α) ⊨ Γ₂ -∗
    Γ₁ ⊨ (unfold: e) : σ : (C (μT: α, C α)) ⊨ Γ₂.
  Proof.
    iIntros "#He %vs !# HΓ₁ //=".
    iApply (ewp_bind [AppRCtx _]); first done. 
    iApply (ewp_pers_mono with "[HΓ₁]"); [by iApply "He"|].
    iIntros "!# %w [Hμ HΓ₂] //= !>". 
    rewrite sem_ty_rec_unfold. 
    unfold rec_unfold. ewp_pure_steps. 
    iFrame.
  Qed.

  (* List type rules *)
  Lemma sem_typed_nil Γ τ: 
    ⊢ Γ ⊨ NIL : ⊥ : List τ ⊨ Γ.
  Proof.
    iIntros "!# %vs HΓ //=". 
    ewp_pure_steps. unfold sem_ty_list. 
    rewrite sem_ty_rec_unfold. iIntros "{$HΓ} !>".
    unfold ListF. iExists #(). by iLeft.
  Qed.
  
  Lemma sem_typed_cons Γ₁ Γ₂ Γ₃ e₁ e₂ σ τ:
    Γ₂ ⊨ e₁ : σ : τ ⊨ Γ₃-∗
    Γ₁ ⊨ e₂ : σ : List τ ⊨ Γ₂-∗
    Γ₁ ⊨ CONS e₁ e₂ : σ : List τ ⊨ Γ₃.
  Proof.
    iIntros "#He₁ #He₂ !# %vs HΓ₁ //=". 
    iApply (ewp_bind [InjRCtx; PairRCtx _]); first done.
    iApply (ewp_mono with "[HΓ₁]"); [by iApply "He₂"|].
    iIntros "%l [Hl HΓ₂] //= !>".
    iApply (ewp_bind [InjRCtx; PairLCtx _]); first done.
    iApply (ewp_mono with "[HΓ₂]"); [by iApply "He₁"|].
    iIntros "%x [Hx HΓ₃] //= !>". ewp_pure_steps.
    unfold sem_ty_list. rewrite !sem_ty_rec_unfold.
    iIntros "{$HΓ₃} !>". iExists (x,l)%V. iRight. iSplit; first done.
    iExists x, l. iFrame; iSplit; first done.
    by rewrite sem_ty_rec_unfold. 
  Qed.

  Lemma sem_typed_match_list Γ₁ Γ₂ Γ₃ x xs e₁ e₂ e₃ σ τ κ :
    x ∉ (env_dom Γ₂) -> xs ∉ (env_dom Γ₂) ->
    x ∉ (env_dom Γ₃) -> xs ∉ (env_dom Γ₃) ->
    x ≠ xs ->
    Γ₁ ⊨ e₁ : σ : List τ ⊨ Γ₂ -∗
    Γ₂ ⊨ e₂ : σ : κ ⊨ Γ₃ -∗
    (x, τ) :: (xs, List τ) :: Γ₂ ⊨ e₃ : σ : κ ⊨ Γ₃ -∗
    Γ₁ ⊨ list-match: e₁ with 
            CONS x => xs => e₃ 
          | NIL => e₂
         end : σ : κ ⊨ Γ₃.
  Proof.
    iIntros (?????) "#He₁ #He₂ #He₃ !# %vs HΓ₁ //=".
    iApply (ewp_bind [CaseCtx _ _]); first done. simpl.
    iApply (ewp_pers_mono with "[HΓ₁]");
      [iApply (sem_typed_unfold with "He₁ HΓ₁")|].
    iIntros "!# %v₁ [Hl HΓ₂] !>". 
    iDestruct "Hl" as "(%v' & [[-> ->]|(-> & (%w₁ & %w₂ & -> & Hτ & Hμ))])"; 
    ewp_pure_steps.
    { iApply (ewp_pers_mono with "[HΓ₂]"); 
        [iApply ("He₂" with "[$HΓ₂]")|eauto]. }
    rewrite lookup_delete. simpl.
    rewrite decide_False; [|by intros [_ []]].
    rewrite decide_True; last done. ewp_pure_steps.
    rewrite decide_True; [|split; congruence].
    rewrite delete_commute -subst_map_insert delete_commute.
    rewrite insert_delete_insert. rewrite subst_map_insert.
    rewrite subst_subst_ne; [|congruence]. rewrite delete_commute.
    rewrite -subst_map_insert -delete_insert_ne; try congruence.
    rewrite -subst_map_insert. 
    iApply (ewp_pers_mono with "[Hμ Hτ HΓ₂]"); [iApply "He₃"; solve_env|].
    { rewrite env_sem_typed_insert; last done; solve_env. }
    iIntros "!# %u [Hκ HΓ₃]". iFrame.
    rewrite -(env_sem_typed_insert _ _ x w₁); last done.
    by rewrite -(env_sem_typed_insert _ _ xs w₂).
  Qed.

  (* Reference rules *)
  
  Lemma sem_typed_alloc Γ₁ Γ₂ e σ τ: 
    Γ₁ ⊨ e : σ : τ ⊨ Γ₂ -∗
    Γ₁ ⊨ ref e : σ : Ref τ ⊨ Γ₂.
  Proof.
    iIntros "#He !# %vs HΓ₁ //=".
    iApply (ewp_bind [AllocCtx]); first done. simpl.
    iApply (ewp_pers_mono with "[HΓ₁]"); [by iApply "He"|].
    iIntros "!# %v [Hτ HΓ₂] !>".
    iApply ewp_alloc. iIntros "!> %l Hl !>". solve_env.
  Qed.
  
  Lemma sem_typed_load Γ x τ: 
    ⊢ ((x, Ref τ) :: Γ ⊨ !x : ⊥ : τ ⊨ (x, Ref Moved) :: Γ).
  Proof.
    iIntros "%vs !# //= [%v (%Hrw & (%w & -> & (%l & Hl & Hτ)) & HΓ)]".
    rewrite Hrw. iApply (ewp_load with "Hl").
    iIntros "!> Hl !>". solve_env.
  Qed.
  
  Lemma sem_typed_load_copy Γ x τ: 
    copy_ty τ -∗
    ((x, Ref τ) :: Γ ⊨ !x : ⊥ : τ ⊨ (x, Ref τ) :: Γ).
  Proof.
    iIntros "#Hcpy %vs !# //= [%v (%Hrw & (%w & -> & (%l & Hl & Hτ)) & HΓ)]".
    rewrite Hrw. iApply (ewp_load with "Hl").
    iDestruct ("Hcpy" with "Hτ") as "#Hτ'".
    iIntros "!> Hl !>". solve_env.
  Qed.

  Lemma sem_typed_store Γ₁ Γ₂ x e σ τ κ ι: 
    (x, Ref τ) :: Γ₁ ⊨ e : σ : ι ⊨ (x, Ref κ) :: Γ₂ -∗
    (x, Ref τ) :: Γ₁ ⊨ (x <- e) : σ : () ⊨ (x, Ref ι) :: Γ₂.
  Proof.
    iIntros "#He !# %vs //= HΓ₁' //=".
    iApply (ewp_bind [StoreRCtx _]); first done. simpl.
    iApply (ewp_pers_mono with "[HΓ₁']"); [iApply "He"; solve_env|].
    iIntros "!# %w [Hι [%v (%Hrw & (%l & -> & (% & Hl & Hκ)) & HΓ₂)]] /=". 
    rewrite Hrw. iApply (ewp_store with "Hl"). 
    iIntros "!> !> Hl !>". solve_env. 
  Qed.

  Lemma sem_typed_alloc_cpy Γ₁ Γ₂ e σ τ: 
    Γ₁ ⊨ e : σ : τ ⊨ Γ₂ -∗
    Γ₁ ⊨ ref e : σ : Refᶜ  τ ⊨ Γ₂.
  Proof.
    iIntros "#He !# %vs HΓ₁ //=".
    iApply (ewp_bind [AllocCtx]); first done. simpl.
    iApply (ewp_pers_mono with "[HΓ₁]"); [by iApply "He"|].
    iIntros "!# %v [Hτ HΓ₂] !>".
    iApply ewp_alloc. iIntros "!> %l Hl". iFrame.
    iMod (inv_alloc (tyN.@l) _
       (∃ w, l ↦ w ∗ τ w)%I with "[Hl Hτ]") as "#Hinv".
    { iExists v. by iFrame. }
    iModIntro. iExists l. by auto.
  Qed.

  Lemma sem_typed_load_cpy Γ₁ Γ₂ e σ τ: 
    copy_ty τ -∗
    Γ₁ ⊨ e : σ : Refᶜ τ ⊨ Γ₂ -∗
    Γ₁ ⊨ !e : σ : τ ⊨ Γ₂.
  Proof.
    iIntros "#Hcpy #He %vs !# //= HΓ₁".
    iApply (ewp_bind [LoadCtx]); first done.
    iApply (ewp_pers_mono with "[HΓ₁]"); [by iApply "He"|].
    iIntros "!# %v [(%l & -> & Hinv) HΓ₂] /= !>".
    iApply (ewp_atomic _ (⊤ ∖ ↑tyN.@l)).
    iMod (inv_acc _ (tyN.@l) with "Hinv") as "[(%u & >Hl & Hτ) Hclose]"; first done.
    iModIntro. iApply (ewp_load with "Hl").
    iIntros "!> Hl !>". 
    iDestruct ("Hcpy" with "Hτ") as "#Hτ'".
    iMod ("Hclose" with "[Hl]"); solve_env.
  Qed.

  Lemma sem_typed_store_cpy Γ₁ Γ₂ Γ₃ e₁ e₂ σ τ: 
    Γ₂ ⊨ e₁ : σ : Refᶜ τ ⊨ Γ₃ -∗
    Γ₁ ⊨ e₂ : σ : τ ⊨ Γ₂ -∗
    Γ₁ ⊨ (e₁ <- e₂) : σ : () ⊨ Γ₃.
  Proof.
    iIntros "#He₁ #He₂ %vs !# /= HΓ₁ /=".
    iApply (ewp_bind [StoreRCtx _]); first done. simpl.
    iApply (ewp_mono with "[HΓ₁]"); [by iApply "He₂"|].
    iIntros "%w [Hτ HΓ₂] !>". 
    iApply (ewp_bind [StoreLCtx _]); first done. simpl.
    iApply (ewp_mono with "[HΓ₂]"); [by iApply "He₁"|].
    iIntros "%u [(%l & -> & Hinv) HΓ₃] !>".
    iApply (ewp_atomic _ (⊤ ∖ ↑tyN.@l)).
    iMod (inv_acc _ (tyN.@l) with "Hinv") as "[(%u & >Hl & _) Hclose]"; first done.
    iModIntro. iApply (ewp_store with "Hl"). 
    iIntros "!> Hl !>".  
    iMod ("Hclose" with "[Hl Hτ]"); solve_env.
  Qed.

  Lemma sem_typed_replace_cpy Γ₁ Γ₂ Γ₃ e₁ e₂ σ τ: 
    Γ₂ ⊨ e₁ : σ : Refᶜ τ ⊨ Γ₃ -∗
    Γ₁ ⊨ e₂ : σ : τ ⊨ Γ₂ -∗
    Γ₁ ⊨ (e₁ <!- e₂) : σ : τ ⊨ Γ₃.
  Proof.
    iIntros "#He₁ #He₂ %vs !# /= HΓ₁ /=".
    iApply (ewp_bind [ReplaceRCtx _]); first done. simpl.
    iApply (ewp_mono with "[HΓ₁]"); [by iApply "He₂"|].
    iIntros "%w [Hτ HΓ₂] !>". 
    iApply (ewp_bind [ReplaceLCtx _]); first done. simpl.
    iApply (ewp_mono with "[HΓ₂]"); [by iApply "He₁"|].
    iIntros "%u [(%l & -> & Hinv) HΓ₃] !>".
    iApply (ewp_atomic _ (⊤ ∖ ↑tyN.@l)).
    iMod (inv_acc _ (tyN.@l) with "Hinv") as "[(%u & >Hl & Hu) Hclose]"; first done.
    iModIntro. iApply (ewp_replace with "Hl"). 
    iIntros "!> Hl !>".  
    iMod ("Hclose" with "[Hl Hτ]").
    { iExists w. iFrame. } 
    iIntros "!>". iFrame.
  Qed.
  
  (* Effect handling rules *)
  
  Lemma sem_typed_perform Γ₁ Γ₂ e τ (A B : sem_sig Σ → sem_ty Σ → sem_ty Σ) 
    `{ NonExpansive2 A, NonExpansive2 B } :
    let σ := (μ∀TS: θ, α, A θ α ⇒ B θ α)%S in
    Γ₁ ⊨ e : σ : A σ τ ⊨ Γ₂ -∗
    Γ₁ ⊨ (perform: e) : σ : B σ τ ⊨ Γ₂.
  Proof.
    iIntros (σ) "#He !# %vs HΓ₁ //=". rewrite /rec_perform.
    iApply (ewp_bind [AppRCtx _; DoCtx OS]); first done.
    iApply (ewp_mono with "[HΓ₁]"); [by iApply "He"|].
    iIntros "%v [Hι HΓ₂] //= !>". ewp_pure_steps.
    iApply ewp_do_os. rewrite upcl_sem_sig_rec_eff /=.
    iExists τ, v. iFrame. iSplitR; first done.
    iIntros "%b Hκ". ewp_pure_steps. iFrame "∗#".
  Qed.

  Lemma sem_typed_shallow_try Γ₁ Γ₂ Γ₃ Γ' x k e h r A B τ τ' σ' `{NonExpansive2 A, NonExpansive2 B }:
    x ∉ env_dom Γ₂ → x ∉ env_dom Γ' → x ∉ env_dom Γ₃ → k ∉ env_dom Γ₃ → k ∉ env_dom Γ' → x ≠ k →
    let σ := (μ∀TS: θ, α, A θ α ⇒ B θ α)%S in
    Γ₁ ⊨ e : σ : τ ⊨ Γ₂ -∗
    (∀ α, (x, A σ α) :: (k, B σ α -{ σ }-∘ τ) :: Γ' ⊨ h : σ' : τ' ⊨ Γ₃) -∗
    (x, τ) :: Γ₂ ++ Γ' ⊨ r : σ' : τ' ⊨ Γ₃ -∗
    Γ₁ ++ Γ' ⊨ (shallow-try: e with
                  effect  (λ: x k, h)
                | return  (λ: x, r) end) : σ' : τ' ⊨ Γ₃.
  Proof.
    iIntros (??????) "%σ #He #Hh #Hr !# %vs HΓ₁Γ'".
    iDestruct (env_sem_typed_app with "HΓ₁Γ'") as "[HΓ₁ HΓ']". simpl. 
    iSpecialize ("He" with "HΓ₁"). iRevert "He".
    iLöb as "IH" forall (e). iIntros "He".
    iApply (ewp_try_with _ _ _ (λ v, τ v ∗ ⟦ Γ₂ ⟧ vs)%I with "[He] [HΓ']"). 
    { ewp_pure_steps. by iApply "He". }
    iSplit; [|iSplit; iIntros (v c)].
    - iIntros (v) "[Hv HΓ₂] //=". ewp_pure_steps.
      rewrite -subst_map_insert. 
      iApply (ewp_pers_mono with "[HΓ₂ HΓ' Hv]"); [iApply "Hr"|].
      { rewrite app_comm_cons env_sem_typed_app. iSplitR "HΓ'"; solve_env. }
      iIntros "!# % [$ HΓ₃] !>". solve_env.
    - rewrite upcl_sem_sig_rec_eff.
      iIntros "(%α & %a & <- & Ha & Hκb) //=". ewp_pure_steps.
      solve_dec.
      rewrite subst_subst_ne; last done. rewrite -subst_map_insert. 
      rewrite -delete_insert_ne; last done. rewrite -subst_map_insert.
      iApply (ewp_mono with "[HΓ' Hκb Ha]"); [iApply "Hh"; solve_env; iSplitL "Hκb"|].
      + iIntros "%b Hκ /=".
        iApply (ewp_mono with "[Hκ Hκb]"); [by iApply "Hκb"|].
        iIntros "% [Hτ' _] !> //=".
      + by (do 2 (rewrite -env_sem_typed_insert; try done)).
      + iIntros "%u [$ HΓ₃] !>".
        by do 2 (rewrite -env_sem_typed_insert; last done).
    - iIntros "/= (% & [] & ?)".
  Qed.

  Lemma sem_typed_deep_try Γ₁ Γ₂ Γ' Γ₃ x k e h r A B τ τ' σ' `{NonExpansive2 A, NonExpansive2 B}:
    x ∉ env_dom Γ₂ → x ∉ env_dom Γ' → k ∉ env_dom Γ' →
    x ∉ env_dom Γ₃ → k ∉ env_dom Γ₃ → x ≠ k → 
    let σ := (μ∀TS: θ, α, A θ α ⇒ B θ α)%S in
    copy_env Γ' -∗
    Γ₁ ⊨ e : σ : τ ⊨ Γ₂ -∗
    (∀ α, (x, A σ α) :: (k, B σ α -{ σ' }-∘ τ') :: Γ' ⊨ h : σ' : τ' ⊨ Γ₃) -∗
    (x, τ) :: Γ₂ ++ Γ' ⊨ r : σ' : τ' ⊨ Γ₃ -∗
    Γ₁ ++ Γ' ⊨ (deep-try: e with
                  effect  (λ: x k, h) 
                | return  (λ: x, r) end) : σ' : τ' ⊨ Γ₃.
  Proof.
    iIntros (??????) "%σ #Hcpy #He #Hh #Hr !# %vs HΓ₁Γ' //=".
    iDestruct (env_sem_typed_app with "HΓ₁Γ'") as "[HΓ₁ HΓ'']".
    iDestruct ("Hcpy" with "HΓ''") as "#HΓ'". ewp_pure_steps. 
    iApply (ewp_deep_try_with _ _ _ (λ v, τ v ∗ env_sem_typed Γ₂ vs) with "[HΓ₁] []").
    { by iApply "He". }
    iLöb as "IH". rewrite {2}deep_handler_unfold.
    iSplit; [|iSplit; iIntros (v c)].
    - iIntros (v) "[Hv HΓ₂] //=". ewp_pure_steps.
      rewrite -subst_map_insert.
      iApply (ewp_pers_mono with "[HΓ₂ HΓ' Hv]"); [iApply "Hr"|].
      { iExists v. rewrite env_sem_typed_app; solve_env. }
      iIntros "!# % [Hτ HΓ₃]"; solve_env.
    - rewrite upcl_sem_sig_rec_eff.
      iIntros "(%α & %a & <- & Ha & Hκb) //=". ewp_pure_steps.
      rewrite decide_True; [|split; first done; by injection].
      rewrite subst_subst_ne; last done.
      rewrite -subst_map_insert -delete_insert_ne; last done.
      rewrite -subst_map_insert.
      iApply (ewp_mono with "[HΓ' Hκb Ha]"); [iApply "Hh"; solve_env; iSplitR "HΓ'"|].
      + iIntros (b) "Hκ /=".
        iApply (ewp_mono with "[Hκ Hκb]"); [iApply ("Hκb" with "Hκ IH")|].
        iIntros "% [Hτ' _] !> //=".
      + by (do 2 (rewrite -env_sem_typed_insert; try done)).
      + iIntros "%u [$ HΓ₃] !>".
        rewrite -(env_sem_typed_insert _ _ x a); last done.
        by rewrite -(env_sem_typed_insert _ _ k c).
    - simpl. iIntros "(% & [] & ?)".
  Qed.

End compatibility.
