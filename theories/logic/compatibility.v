
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
From haffel.lang Require Import haffel.
From haffel.logic Require Import sem_def.
From haffel.logic Require Import sem_types.
From haffel.logic Require Import sem_judgement.
From haffel.logic Require Import tactics.
From haffel.logic Require Import sem_sig.
From haffel.logic Require Import sem_row.
From haffel.logic Require Import sem_env.
From haffel.logic Require Import copyable.
From haffel.logic Require Import sem_judgement.
From haffel.logic Require Import sem_operators.
From haffel.logic Require Import ewpw.

Open Scope bi_scope.
Open Scope stdpp_scope.
Open Scope ieff_scope.
  
(* Semantic typing rules. *)

Section compatibility.

  Context `{!heapGS Σ}.

  Lemma sem_typed_val τ Γ v : 
    ⊨ᵥ v : τ -∗ Γ ⊨ v : ⟨⟩ : τ ⊨ Γ.
  Proof.
    iIntros "#Hv !# %vs HΓ /=". 
    iApply ewpw_bot.
    iApply ewp_value. iFrame.
    rewrite /sem_val_typed /tc_opaque.
    iApply "Hv".
  Qed.

  (* Base rules *)
  
  Lemma sem_typed_unit Γ : 
    ⊢ Γ ⊨ #() : ⟨⟩ : () ⊨ Γ.
  Proof.
    iIntros (vs) "!# HΓ₁ //=". 
    iApply ewpw_bot.
    iApply ewp_value. by iFrame.
  Qed.
  
  Lemma sem_typed_bool Γ (b : bool) : 
    ⊢ Γ ⊨ #b : ⟨⟩ : 𝔹 ⊨ Γ.
  Proof.
    iIntros (vs) "!# HΓ₁ //=". 
    iApply ewpw_bot.
    iApply ewp_value. 
    iSplitR; first (iExists b); done.
  Qed.
  
  Lemma sem_typed_int Γ (i : Z) : 
    ⊢ Γ ⊨ #i : ⟨⟩ : ℤ ⊨ Γ.
  Proof.
    iIntros (vs) "!# HΓ₁ //=". 
    iApply ewpw_bot.
    iApply ewp_value. 
    iSplitR; first (iExists i); done.
  Qed.
  
  Lemma sem_typed_string Γ (s : string) : 
    ⊢ Γ ⊨ #(LitStr s) : ⟨⟩ : Str ⊨ Γ.
  Proof.
    iIntros (vs) "!# HΓ₁ //=". 
    iApply ewpw_bot.
    iApply ewp_value. 
    iSplitR; first (iExists s); done.
  Qed.

  Lemma sem_typed_var τ Γ x : 
    ⊢ (x, τ) :: Γ ⊨ x : ⟨⟩ : τ ⊨ Γ.
  Proof.
    iIntros (vs) "!# /= [%v (%Hrw & Hτ & HΓ₁)] /=". 
    iApply ewpw_bot.
    rewrite Hrw. iApply ewp_value. iFrame.
  Qed.

  Lemma sem_typed_void_in_env τ Γ₁ Γ₂ e x : 
    ⊢ (x, Void) :: Γ₁ ⊨ e : ⟨⟩ : τ ⊨ Γ₂.
  Proof.
    iIntros (vs) "!# /= [%v (%Hrw & [] & _)] /=". 
  Qed.

  Lemma sem_typed_closure τ ρ κ f x e :
    match f with BNamed f => BNamed f ≠ x | BAnon => True end →
    (x, τ) ::? (f, τ -{ ρ }-> κ) ::? [] ⊨ e : ρ : κ ⊨ [] -∗ 
    ⊨ᵥ (rec: f x := e) : (τ -{ ρ }-> κ).
  Proof.
      iIntros (?) "#He !#". iLöb as "IH".
      iIntros "%v !# Hτ /=".  
      ewpw_pure_steps. destruct x as [|x]; destruct f as [|f]; simpl.
      - rewrite - {3} [e]subst_map_empty.
        iApply (ewpw_mono with "[He]"); first (by iApply "He").
        iIntros "!# % [$ _] //=". 
      - rewrite -subst_map_singleton.
        iApply ewpw_mono; [iApply "He"; solve_env|solve_env].
        iIntros "!# % [$ _] //=".
      - rewrite -subst_map_singleton.
        iApply (ewpw_mono with "[Hτ]"); [iApply "He"; solve_env|solve_env].
        iIntros "!# % [$ _] //=".
      - rewrite -(subst_map_singleton f) -subst_map_singleton subst_map_union.
        iApply (ewpw_mono with "[Hτ]"); [iApply "He"|iIntros "!# % [$ _] //="].
        rewrite -insert_union_singleton_r; [solve_env|apply lookup_singleton_ne];
        intros ?; simplify_eq.
  Qed.

  Lemma sem_typed_Tclosure τ e :
    (∀ α, ⊨ e : ⟨⟩ : τ α) -∗ 
    ⊨ᵥ (Λ: e) : (∀T: α, τ α).
  Proof.
    iIntros "#He !# %u !#". ewpw_pure_steps.
    rewrite - {2} [e]subst_map_empty.
    iSpecialize ("He" $! u).
    iApply (ewpw_mono with "[He]"); [iApply "He"|]; first done. 
    iIntros "!# % [$ _] //=".
  Qed.

  (* Signature abstraction and application *)
  Lemma sem_typed_Rclosure C e : 
    (∀ θ, ⊨ e : ⟨⟩ : C θ) -∗
    ⊨ᵥ (Λ: e) : (∀R: θ , C θ)%T.
  Proof.
    iIntros "#He !# %ρ !# /=".
    ewpw_pure_steps. rewrite - {2} [e]subst_map_empty. 
    iApply (ewpw_mono with "[He]"); [by iApply "He"|].
    iIntros "!# % [$ _] //=". 
  Qed.

  Lemma sem_typed_closure_to_unrestricted τ ρ κ x e :
    ⊨ᵥ (λ: x, e) : (τ -{ ρ }-∘ κ) -∗
    ⊨ᵥ (λ: x, e) : (τ -{ ρ }-> κ).
  Proof. 
    iIntros "#He !# %w !# Hτ". 
    iSpecialize ("He" $! w).
    iApply ("He" with "Hτ").
  Qed.

  (* Subsumption rule *)
  
  Lemma sem_typed_sub Γ₁ Γ₁' Γ₂ Γ₂' e ρ ρ' τ τ':
    Γ₁  ≤E Γ₁' -∗
    Γ₂' ≤E Γ₂ -∗
    ρ'  ≤R ρ -∗ 
    τ'  ≤T τ -∗
    Γ₁' ⊨ e : ρ' : τ' ⊨ Γ₂' -∗ Γ₁ ⊨ e : ρ : τ ⊨ Γ₂.
  Proof.
    iIntros "#HΓ₁le #HΓ₂le #Hρle #Hτle #He !# %vs HΓ₁ //=".
    iDestruct ("HΓ₁le" with "HΓ₁") as "HΓ₁'".
    iApply (ewpw_sub with "Hρle").
    iApply (ewpw_mono with "[HΓ₁']"); first (by iApply "He").
    iIntros "!# % [Hτ HΓ₂] //= !>".
    iSplitL "Hτ"; [by iApply "Hτle"|by iApply "HΓ₂le"].
  Qed. 
  
  (* Convenient Subsumption rules *)
  Lemma sem_typed_sub_ty τ' τ Γ₁ Γ₂ e ρ :
  τ' ≤T τ -∗
  (Γ₁ ⊨ e : ρ : τ' ⊨ Γ₂) -∗ Γ₁ ⊨ e : ρ : τ ⊨ Γ₂.
  Proof.
    iIntros "#Hτ".
    iApply (sem_typed_sub Γ₁ Γ₁ Γ₂ Γ₂ _ ρ ρ);
      (iApply row_le_refl || iApply env_le_refl || done). 
  Qed.

  Lemma sem_typed_sub_row ρ ρ' Γ₁ Γ₂ e τ :
    ρ' ≤R ρ -∗
    (Γ₁ ⊨ e : ρ' : τ ⊨ Γ₂) -∗ Γ₁ ⊨ e : ρ : τ ⊨ Γ₂.
  Proof.
    iIntros "#Hρ".
    iApply (sem_typed_sub Γ₁ Γ₁ Γ₂ Γ₂ _ ρ ρ' τ τ);
      (iApply env_le_refl || iApply ty_le_refl || done).
  Qed.

  Lemma sem_typed_sub_nil Γ₁ Γ₂ e τ ρ :
    (Γ₁ ⊨ e : ⟨⟩ : τ ⊨ Γ₂) -∗ Γ₁ ⊨ e : ρ : τ ⊨ Γ₂.
  Proof. iApply sem_typed_sub_row. iApply row_le_nil. Qed.
  
  Lemma sem_typed_sub_u2aarr Γ₁ Γ₂ e τ κ ρ ρ' :
    (Γ₁ ⊨ e : ρ' : (τ -{ ρ }-> κ) ⊨ Γ₂) -∗ Γ₁ ⊨ e : ρ' : (τ -{ ρ }-∘ κ) ⊨ Γ₂.
  Proof.
    iIntros "#He".
    iApply sem_typed_sub_ty; [iApply ty_le_u2aarr|done].
  Qed.

  Lemma sem_typed_sub_env Γ₁ Γ₁' Γ₂ e ρ τ :
    Γ₁ ≤E Γ₁' -∗
    (Γ₁' ⊨ e : ρ : τ ⊨ Γ₂) -∗ Γ₁ ⊨ e : ρ : τ ⊨ Γ₂.
  Proof.
    iIntros "#HΓ₁".
    iApply (sem_typed_sub Γ₁ Γ₁' Γ₂ Γ₂ _ ρ ρ τ τ);
      (iApply row_le_refl || iApply env_le_refl || iApply ty_le_refl || done).
  Qed.

  Lemma sem_typed_sub_env_final Γ₁ Γ₂ Γ₂' e ρ τ :
    Γ₂' ≤E Γ₂ -∗
    (Γ₁ ⊨ e : ρ : τ ⊨ Γ₂') -∗ Γ₁ ⊨ e : ρ : τ ⊨ Γ₂.
  Proof.
    iIntros "#HΓ₂".
    iApply (sem_typed_sub Γ₁ Γ₁ Γ₂ Γ₂' _ ρ ρ τ τ);
      (iApply row_le_refl || iApply env_le_refl || iApply ty_le_refl || done).
  Qed.

  Lemma sem_typed_swap_second Γ₁ Γ₂ x y e ρ τ₁ τ₂ κ :
    ((y, τ₂) :: (x, τ₁) :: Γ₁ ⊨ e : ρ : κ ⊨ Γ₂) -∗ 
    ((x, τ₁) :: (y, τ₂) :: Γ₁ ⊨ e : ρ : κ ⊨ Γ₂).
  Proof.
    iIntros "He".
    iApply sem_typed_sub_env; [iApply env_le_swap_second|iApply "He"].
  Qed.

  Lemma sem_typed_swap_third Γ₁ Γ₂ x y z e ρ τ₁ τ₂ τ₃ κ :
    ((z, τ₃) :: (x, τ₁) :: (y, τ₂) :: Γ₁ ⊨ e : ρ : κ ⊨ Γ₂) -∗ 
    ((x, τ₁) :: (y, τ₂) :: (z, τ₃) :: Γ₁ ⊨ e : ρ : κ ⊨ Γ₂).
  Proof.
    iIntros "He".
    iApply sem_typed_sub_env; [|iApply "He"].
    iApply env_le_trans; iApply env_le_swap_third.
  Qed.

  Lemma sem_typed_swap_fourth Γ₁ Γ₂ x y z z' e ρ τ₁ τ₂ τ₃ τ₄ κ :
    ((z', τ₄) :: (x, τ₁) :: (y, τ₂) :: (z, τ₃) :: Γ₁ ⊨ e : ρ : κ ⊨ Γ₂) -∗ 
    ((x, τ₁) :: (y, τ₂) :: (z, τ₃) :: (z', τ₄) :: Γ₁ ⊨ e : ρ : κ ⊨ Γ₂).
  Proof.
    iIntros "He".
    iApply sem_typed_sub_env; [|iApply "He"].
    do 2 (iApply env_le_trans; [iApply env_le_swap_fourth|]).
    iApply env_le_swap_fourth.
  Qed.

  Lemma sem_typed_swap_env_singl Γ₁ Γ₂ x e ρ τ κ :
    (Γ₁ ++ [(x, τ)] ⊨ e : ρ : κ ⊨ Γ₂) -∗ 
    ((x, τ) :: Γ₁ ⊨ e : ρ : κ ⊨ Γ₂). 
  Proof.
    iIntros "He".
    iApply sem_typed_sub_env; [|iApply "He"].
    iApply env_le_swap_env_singl.
  Qed.

  Lemma sem_typed_contraction Γ₁ Γ₂ x e ρ τ κ :
    copy_ty τ -∗
    (x, τ) :: (x, τ) :: Γ₁ ⊨ e : ρ : κ ⊨ Γ₂ -∗ 
    (x, τ) :: Γ₁ ⊨ e : ρ : κ ⊨ Γ₂.
  Proof.
    iIntros "#τ He".
    iApply sem_typed_sub_env; 
      [by iApply env_le_copy_contraction|iApply "He"].
  Qed.

  Lemma sem_typed_weaken Γ₁ Γ₂ x e ρ τ κ :
    (Γ₁ ⊨ e : ρ : κ ⊨ Γ₂) -∗ ((x, τ) :: Γ₁ ⊨ e : ρ : κ ⊨ Γ₂).
  Proof.
    iIntros "He".
    iApply sem_typed_sub_env; [iApply env_le_weaken|iApply "He"].
  Qed.

  Lemma sem_typed_weaken_env Γ Γ₁ Γ₂ e ρ τ :
    (Γ₁ ⊨ e : ρ : τ ⊨ Γ₂) -∗ (Γ ++ Γ₁ ⊨ e : ρ : τ ⊨ Γ₂).
  Proof.
    iIntros "#He".
    iInduction Γ as [|[x κ] Γ'] "IH"; simpl.
    { iApply "He". }
    iApply sem_typed_sub_env; [iApply env_le_weaken|iApply "IH"].
  Qed.

  Lemma sem_typed_frame Γ₁ e ρ x τ κ Γ₂ `{! OSRow ρ}:
    Γ₁ ⊨ e : ρ : κ ⊨ Γ₂ -∗
    (x, τ) :: Γ₁ ⊨ e : ρ : κ ⊨ (x, τ) :: Γ₂.
  Proof.
    iIntros "#He %vs !# (%v & %Hrw & Hτ & HΓ₁)".
    iApply (ewpw_mono_os with "[He HΓ₁]").
    { by iApply "He". }
    iIntros (w) "[Hκ HΓ₂]". solve_env.
  Qed.

  Lemma sem_typed_frame_ms Γ₁ e ρ x τ κ Γ₂:
    copy_ty τ -∗
    Γ₁ ⊨ e : ρ : κ ⊨ Γ₂ -∗
    (x, τ) :: Γ₁ ⊨ e : ρ : κ ⊨ (x, τ) :: Γ₂.
  Proof.
    iIntros "#Hcpy #He %vs !# (%v & %Hrw & Hτ & HΓ₁)".
    iDestruct ("Hcpy" with "Hτ") as "#Hτ'".
    iApply (ewpw_mono with "[HΓ₁]"); [by iApply "He"|].
    iIntros "!# %w [Hκ HΓ₂]". solve_env.
  Qed.

  Lemma sem_typed_frame_env Γ₁ Γ' e ρ τ Γ₂ `{! OSRow ρ}:
    Γ₁ ⊨ e : ρ : τ ⊨ Γ₂ -∗
    Γ' ++ Γ₁ ⊨ e : ρ : τ ⊨ Γ' ++ Γ₂.
  Proof.
    iIntros "#He %vs !# HΓ'Γ₁".
    iDestruct (env_sem_typed_app with "HΓ'Γ₁") as "[HΓ' HΓ₁]".
    iInduction Γ' as [|[x κ]] "IH".
    { simpl. by iApply "He". }
    iDestruct "HΓ'" as "(%v & %Hrw & Hκ & HΓ'')".
    iApply (ewpw_mono_os with "[HΓ'' HΓ₁]").
    { iApply ("IH" with "HΓ'' HΓ₁"). }
    iIntros (w) "[$ HΓ] !>". solve_env.
  Qed.

  Lemma sem_typed_frame_env_ms Γ₁ Γ' e ρ τ Γ₂ :
    copy_env Γ' -∗
    Γ₁ ⊨ e : ρ : τ ⊨ Γ₂ -∗
    Γ' ++ Γ₁ ⊨ e : ρ : τ ⊨ Γ' ++ Γ₂.
  Proof.
    iIntros "#HcpyΓ' #He %vs !# HΓ'Γ₁".
    iDestruct (env_sem_typed_app with "HΓ'Γ₁") as "[HΓ' HΓ₁]".
    iDestruct ("HcpyΓ'" with "HΓ'") as "#HΓ''".
    iApply (ewpw_mono _ _ _ (λ v, τ v ∗ ⟦ Γ₂ ⟧ vs) with "[HΓ₁]").
    { by iApply "He". }
    iIntros "!# % [Hτ HΓ₂] !> {$Hτ}".
    rewrite env_sem_typed_app. iFrame "∗#".
  Qed.

  Lemma sem_typed_unit' Γ ρ : 
    ⊢ Γ ⊨ #() : ρ : () ⊨ Γ.
  Proof.
    iApply sem_typed_sub_nil. iApply sem_typed_unit.
  Qed.
  
  Lemma sem_typed_bool' Γ ρ (b : bool) : 
    ⊢ Γ ⊨ #b : ρ : 𝔹 ⊨ Γ.
  Proof.
    iApply sem_typed_sub_nil. iApply sem_typed_bool.
  Qed.
  
  Lemma sem_typed_int' Γ ρ (i : Z) : 
    ⊢ Γ ⊨ #i : ρ : ℤ ⊨ Γ.
  Proof.
    iApply sem_typed_sub_nil. iApply sem_typed_int.
  Qed.
  
  Lemma sem_typed_string' Γ ρ (s : string) : 
    ⊢ Γ ⊨ #(LitStr s) : ρ : Str ⊨ Γ.
  Proof.
    iApply sem_typed_sub_nil. iApply sem_typed_string.
  Qed.

  Lemma sem_typed_var' τ Γ ρ x : 
    ⊢ (x, τ) :: Γ ⊨ x : ρ : τ ⊨ Γ.
  Proof.
    iApply sem_typed_sub_nil. iApply sem_typed_var.
  Qed.

  (* λ-calculus rules *)

  Lemma sem_typed_afun τ ρ Γ₁ Γ₂ x e κ: 
    x ∉ (env_dom Γ₁) → x ∉ (env_dom Γ₂) →
    (x,τ) ::? Γ₁ ⊨ e : ρ : κ ⊨ [] -∗
    Γ₁ ++ Γ₂ ⊨ (λ: x, e) : ⟨⟩ : (τ -{ ρ }-∘ κ) ⊨ Γ₂.
  Proof.
    iIntros (??) "#He !# %vs HΓ₁₂ //=".
    iDestruct (env_sem_typed_app with "HΓ₁₂") as "[HΓ₁ HΓ₂]".
    ewpw_pure_steps. iFrame.
    iIntros (w) "Hτ". 
    ewpw_pure_steps. rewrite subst'_subst_map_insert.
    iApply (ewpw_mono with "[Hτ HΓ₁]"); [iApply "He"|iIntros "!# % [$ _] //="].
    destruct x; solve_env. 
  Qed.

  Lemma sem_typed_ufun τ ρ κ Γ₁ Γ₂ f x e :
    x ∉ (env_dom Γ₁) → f ∉ (env_dom Γ₁) → 
    match f with BNamed f => BNamed f ≠ x | BAnon => True end →
    copy_env Γ₁ -∗
    (x, τ) ::? (f, τ -{ ρ }-> κ) ::? Γ₁ ⊨ e : ρ : κ ⊨ [] -∗
    Γ₁ ++ Γ₂ ⊨ (rec: f x := e) : ⟨⟩ : (τ -{ ρ }-> κ) ⊨ Γ₂.
  Proof.
    iIntros (???) "#HcpyΓ₁ #He !# %vs HΓ₁₂ //=".
    ewpw_pure_steps.
    rewrite env_sem_typed_app. iDestruct "HΓ₁₂" as "[HΓ₁' $]".
    iDestruct ("HcpyΓ₁" with "HΓ₁'") as "#HΓ₁".
    iLöb as "IH".
    iIntros "!# %w Hτ". 
    ewpw_pure_steps. destruct f; destruct x; simpl.
    - iApply ewpw_mono; [by iApply "He"|iIntros "!# % [$ _] //="].
    - rewrite -subst_map_insert. 
      iApply (ewpw_mono with "[Hτ]"); 
        [iApply "He"; solve_env|iIntros "!# % [$ _] //="].
    - rewrite -subst_map_insert.
      iApply (ewpw_mono with "[Hτ]"); 
        [iApply "He"; solve_env|iIntros "!# % [$ _] //="].
      by iApply "IH".
    - assert (s ≠ s0) by (intros ?; simplify_eq).
      rewrite subst_subst_ne; last done.
      rewrite -subst_map_insert.
      rewrite -delete_insert_ne; last done. 
      rewrite -subst_map_insert.
      iApply (ewpw_mono with "[Hτ]"); 
        [iApply "He"; solve_env|iIntros "!# % [$ _] //="].
      { by iApply "IH". }
      by do 2 (rewrite -env_sem_typed_insert; last done).
  Qed.

  Lemma sem_typed_ufun_poly_rec τ ρ κ Γ₁ Γ₂ f x e :
    x ∉ (env_dom Γ₁) → f ∉ (env_dom Γ₁) → 
    match x with BNamed x => BNamed x ≠ f | BAnon => True end →
    copy_env Γ₁ -∗
    (∀ ι, (x, τ ι) ::? (f, ∀T: α, τ α -{ ρ α }-> κ α) ::? Γ₁ ⊨ e : ρ ι : κ ι ⊨ []) -∗
    Γ₁ ++ Γ₂ ⊨ (rec: f <> := λ: x, e) : ⟨⟩ : (∀T: α, τ α -{ ρ α }-> κ α) ⊨ Γ₂.
  Proof.
    iIntros (???) "#HcpyΓ₁ #He !# %vs HΓ₁₂ //=".
    ewpw_pure_steps. rewrite env_sem_typed_app.
    iDestruct "HΓ₁₂" as "[HΓ₁' $]".
    iDestruct ("HcpyΓ₁" with "HΓ₁'") as "#HΓ₁".
    iLöb as "IH".
    iIntros (α) "!#". ewpw_pure_steps.
    destruct f; destruct x; simpl; 
    ewpw_pure_steps; iIntros (v) "!# Hτ"; ewpw_pure_steps.
    - iApply ewpw_mono; first (by iApply "He").  
      iIntros "!# % [$ _] //=".
    - rewrite -subst_map_insert. 
      iApply (ewpw_mono with "[Hτ]"); first (iApply "He"; solve_env).  
      iIntros "!# % [$ _] //=".
    - rewrite -subst_map_insert.
      iApply (ewpw_mono with "[Hτ]"); first (iApply "He"; solve_env; by iApply "IH") .
      iIntros "!# % [$ _] //=".
    - assert (s ≠ s0) by (intros ?; simplify_eq).
      solve_dec.
      rewrite subst_subst_ne; last done.
      rewrite -subst_map_insert.
      rewrite -delete_insert_ne; last done. 
      rewrite -subst_map_insert.
      iApply (ewpw_mono with "[Hτ]"); first (iApply "He"; solve_env).  
      + by iApply "IH". 
      + by do 2 (rewrite -env_sem_typed_insert; last done).
      + iIntros "!# % [$ _] //=".
  Qed.

  Lemma sem_typed_let τ ρ κ Γ₁ Γ₂ Γ₃ x e₁ e₂: 
    x ∉ (env_dom Γ₂) → x ∉ (env_dom Γ₃) →
    Γ₁ ⊨ e₁ : ρ : τ ⊨ Γ₂ -∗
    (x, τ) :: Γ₂ ⊨ e₂ : ρ : κ ⊨ Γ₃ -∗
    Γ₁ ⊨ (let: x := e₁ in e₂) : ρ : κ ⊨ Γ₃.
  Proof.
    iIntros (??) "#He₁ #He₂ !# %vs HΓ₁ /=".
    iApply (ewpw_bind [AppRCtx _]); first done. simpl.
    iApply (ewpw_mono with "[HΓ₁]"); first (by iApply "He₁").
    iIntros "!# % [Hτ HΓ₂] !> /=". ewpw_pure_steps.
    rewrite -subst_map_insert.
    iApply (ewpw_mono with "[Hτ HΓ₂]"); first (iApply "He₂"; solve_env).
    iIntros "!# % [Hτκ HΓ₃] !> /=".
    solve_env.
  Qed.

  Lemma sem_typed_app τ ρ' ρ κ Γ₁ Γ₂ e₁ e₂ :
    ¡ ρ' ≤R ρ -∗
    Γ₂ ⊨ e₁ : ¡ ρ' : (τ -{ ρ }-∘ κ) ⊨ [] -∗
    Γ₁ ⊨ e₂ : ρ : τ ⊨ Γ₂ -∗
    Γ₁ ⊨ (e₁ e₂) : ρ : κ ⊨ [].
  Proof.
    iIntros "#Hρ'ρ #He₁ #He₂ !# %vs HΓ₁ /=".
    iApply (ewpw_bind [AppRCtx _]); first done.
    iApply (ewpw_mono with "[HΓ₁]"); first (by iApply "He₂").
    iIntros "!# % [Hτ HΓ₂] !> /=".
    iApply (ewpw_bind [AppLCtx _]); first done.
    iApply ewpw_sub; first iApply "Hρ'ρ".
    iApply (ewpw_mono_os with "[HΓ₂]").
    { by iApply "He₁". }
    iIntros "%w [Hτκ HΓ₃] !> /=".
    iApply (ewpw_mono with "[Hτκ Hτ]").
    {  by iApply "Hτκ".  }
    iIntros "!# % $ !> //=".
  Qed.

  Lemma sem_typed_app_nil τ ρ κ Γ₁ Γ₂ e₁ e₂ :
    Γ₂ ⊨ e₁ : ⟨⟩ : (τ -{ ρ }-∘ κ) ⊨ [] -∗
    Γ₁ ⊨ e₂ : ρ : τ ⊨ Γ₂ -∗
    Γ₁ ⊨ (e₁ e₂) : ρ : κ ⊨ [].
  Proof.
    iIntros "#He₁ #He₂".
    iApply (sem_typed_app _ ⟨⟩%R).
    { iApply row_le_trans; [iApply row_le_os_elim|iApply row_le_nil]. }
    { iApply sem_typed_sub_nil. iApply "He₁". }
    iApply "He₂".
  Qed.

  Lemma sem_typed_app_os τ ρ κ Γ₁ Γ₂ Γ₃ e₁ e₂ `{! OSRow ρ}: 
    Γ₂ ⊨ e₁ : ρ : (τ -{ ρ }-∘ κ) ⊨ Γ₃ -∗
    Γ₁ ⊨ e₂ : ρ : τ ⊨ Γ₂ -∗
    Γ₁ ⊨ (e₁ e₂) : ρ : κ ⊨ Γ₃.
  Proof.
    iIntros "#He₁ #He₂ !# %vs HΓ₁ /=".
    iApply (ewpw_bind [AppRCtx _]); first done.
    iApply (ewpw_mono with "[HΓ₁]"); first (by iApply "He₂").
    iIntros "!# % [Hτ HΓ₂] !> /=".
    iApply (ewpw_bind [AppLCtx _]); first done.
    iApply (ewpw_mono_os with "[HΓ₂]").
    { by iApply "He₁". }
    iIntros "%w [Hτκ HΓ₃] !> /=".
    iApply (ewpw_mono_os with "[Hτκ Hτ]").
    { by iApply "Hτκ". }
    iIntros "% $ !> //=".
  Qed.

  Lemma sem_typed_app_ms τ ρ κ Γ₁ Γ₂ Γ₃ e₁ e₂: 
    copy_env Γ₃ -∗ copy_ty τ -∗
    Γ₂ ⊨ e₁ : ρ : (τ -{ ρ }-∘ κ) ⊨ Γ₃ -∗
    Γ₁ ⊨ e₂ : ρ : τ ⊨ Γ₂ -∗
    Γ₁ ⊨ (e₁ e₂) : ρ : κ ⊨ Γ₃.
  Proof.
    iIntros "#HΓcpy #Hcpyτ #He₁ #He₂ !# %vs HΓ₁ /=".
    iApply (ewpw_bind [AppRCtx _]); first done.
    iApply (ewpw_mono with "[HΓ₁]"); first (by iApply "He₂").
    iIntros "!# % [Hτ HΓ₂] !> /=".
    iDestruct ("Hcpyτ" with "Hτ") as "#Hτ'".
    iApply (ewpw_bind [AppLCtx _]); first done.
    iApply (ewpw_mono with "[HΓ₂]").
    { by iApply "He₁". }
    iIntros "!# %w [Hτκ HΓ₃] !> /=".
    iApply (ewpw_mono with "[Hτκ Hτ']").
    { by iApply "Hτκ". }
    iDestruct ("HΓcpy" with "HΓ₃") as "#HΓ₃'".
    iIntros "!# % $ !> //=".
  Qed.

  Lemma sem_typed_seq τ ρ κ Γ₁ Γ₂ Γ₃ e₁ e₂ : 
    Γ₁ ⊨ e₁ : ρ : τ ⊨ Γ₂ -∗
    Γ₂ ⊨ e₂ : ρ : κ ⊨ Γ₃ -∗
    Γ₁ ⊨ (e₁ ;; e₂) : ρ : κ ⊨ Γ₃.
  Proof.
    iIntros "#He₁ #He₂ !# %vs HΓ₁ /=".
    iApply (ewpw_bind ([AppRCtx _])); first done. simpl.
    iApply (ewpw_mono with "[HΓ₁]"); first (by iApply "He₁").
    iIntros "!# % [Hτ HΓ₂] !> /=". ewpw_pure_steps.
    iApply (ewpw_mono with "[Hτ HΓ₂]"); first (by iApply "He₂").
    iIntros "!# % [Hτκ HΓ₃] !> /=". iFrame.
  Qed.

  Lemma sem_typed_pair τ ρ κ Γ₁ Γ₂ Γ₃ e₁ e₂ `{! OSRow ρ}: 
    Γ₂ ⊨ e₁ : ρ : τ ⊨ Γ₃ -∗
    Γ₁ ⊨ e₂ : ρ : κ ⊨ Γ₂ -∗
    Γ₁ ⊨ (e₁,e₂) : ρ : (τ × κ) ⊨ Γ₃.
  Proof.
    iIntros "#He₁ #He₂ !# %vs HΓ₁ //=".
    iApply (ewpw_bind ([PairRCtx (subst_map vs e₁)])); first done.
    iApply (ewpw_mono with "[HΓ₁]"); first (by iApply "He₂").
    iIntros "!# % [Hτ HΓ₂] !> /=".
    iApply (ewpw_bind ([PairLCtx v])); first done.
    iApply (ewpw_mono_os with "[HΓ₂]").
    { by iApply "He₁". }
    iIntros (w) "[Hκw HΓ₃] //= !>". ewpw_pure_steps.
    solve_env.
  Qed.

  Lemma sem_typed_pair_ms τ ρ κ Γ₁ Γ₂ Γ₃ e₁ e₂ : 
    copy_ty κ -∗
    Γ₂ ⊨ e₁ : ρ : τ ⊨ Γ₃ -∗
    Γ₁ ⊨ e₂ : ρ : κ ⊨ Γ₂ -∗
    Γ₁ ⊨ (e₁,e₂) : ρ : (τ × κ) ⊨ Γ₃.
  Proof.
    iIntros "#Hκcpy #He₁ #He₂ !# %vs HΓ₁ //=".
    iApply (ewpw_bind ([PairRCtx (subst_map vs e₁)])); first done.
    iApply (ewpw_mono with "[HΓ₁]"); first (by iApply "He₂").
    iIntros "!# % [Hκ HΓ₂] !> /=".
    iApply (ewpw_bind ([PairLCtx v])); first done.
    iDestruct ("Hκcpy" with "Hκ") as "#Hκ'".
    iApply (ewpw_mono with "[HΓ₂]").
    { by iApply "He₁". }
    iIntros "!# %w [Hκw HΓ₃] //= !>". ewpw_pure_steps.
    solve_env.
  Qed.

  Lemma sem_typed_fst x τ κ Γ : 
    ⊢ (x, τ × κ) :: Γ ⊨ Fst x : ⟨⟩ : τ ⊨ (x, ⊤ × κ) :: Γ.
  Proof.
    iIntros "!# %vs /= (% & % & [(% & % & % & Hτ & Hκ) HΓ]) //=". rewrite H H0.
    ewpw_pure_steps. solve_env.
  Qed.

  Lemma sem_typed_snd x τ κ Γ : 
    ⊢ (x, τ × κ) :: Γ ⊨ Snd x : ⟨⟩ : κ ⊨ (x, τ × ⊤) :: Γ.
  Proof.
    iIntros "!# %vs /= (% & % & [(% & % & % & Hτ & Hκ) HΓ]) //=". rewrite H H0.
    ewpw_pure_steps. solve_env.
  Qed.

  Lemma sem_typed_pair_elim τ ρ κ ι Γ₁ Γ₂ Γ₃ x₁ x₂ e₁ e₂ :
    x₁ ∉ (env_dom Γ₂) → x₂ ∉ (env_dom Γ₂) →
    x₁ ∉ (env_dom Γ₃) → x₂ ∉ (env_dom Γ₃) →
    x₁ ≠ x₂ →
    Γ₁ ⊨ e₁ : ρ : (τ × κ) ⊨ Γ₂ -∗
    (x₁, τ) :: (x₂, κ) :: Γ₂ ⊨ e₂ : ρ : ι ⊨ Γ₃ -∗
    Γ₁ ⊨ (let: (x₁, x₂) := e₁ in e₂) : ρ : ι ⊨ Γ₃.
  Proof.
    iIntros (?????) "#He₁ #He₂ !# %vs HΓ₁ //=". ewpw_pure_steps.
    set ex1x2 := (λ: x₁ x₂, subst_map (binder_delete x₂ 
                                      (binder_delete x₁ vs)) e₂)%V. 
    iApply (ewpw_bind ([AppLCtx ex1x2; AppRCtx pair_elim])); first done.
    iApply (ewpw_mono with "[HΓ₁]"); first (by iApply "He₁").
    iIntros "!# % [Hτκv HΓ₂] //= !>". 
    unfold pair_elim. ewpw_pure_steps.
    iDestruct "Hτκv" as "(%v₁ & %v₂ & -> & Hτ & Hκ)".
    unfold ex1x2. ewpw_pure_steps. 
    destruct (decide _) as [[]|[]]; [|split; [done|congruence]].
    rewrite delete_commute -subst_map_insert -delete_insert_ne; last congruence.
    rewrite -subst_map_insert.
    iApply (ewpw_mono with "[Hτ Hκ HΓ₂]"); first (iApply "He₂").
    - iExists v₁. iFrame. iSplitL "".
      { rewrite lookup_insert_ne; last done. by rewrite lookup_insert. }
      iExists v₂. iFrame; iSplitL ""; [by rewrite lookup_insert|].
      by do 2 (rewrite -env_sem_typed_insert; last done).
    - iIntros "!# % [Hιv HΓ₃]". iFrame.
      rewrite -(env_sem_typed_insert _ _ x₂ v₂); last done.
      by rewrite -(env_sem_typed_insert _ _ x₁ v₁).
  Qed.
  
  Lemma sem_typed_left_inj τ ρ κ Γ₁ Γ₂ e : 
    Γ₁ ⊨ e : ρ : τ ⊨ Γ₂ -∗
    Γ₁ ⊨ InjL e : ρ : (τ + κ) ⊨ Γ₂.
  Proof.
    iIntros "#He !# %vs HΓ₁ //=".
    iApply (ewpw_bind [InjLCtx]); first done.
    iApply (ewpw_mono with "[HΓ₁]"); first (by iApply "He").
    iIntros "!# % [Hτ HΓ₂] /= !>". ewpw_pure_steps.
    iFrame. iExists v. iLeft. by iFrame.
  Qed.

  Lemma sem_typed_right_inj τ ρ κ Γ₁ Γ₂ e : 
    Γ₁ ⊨ e : ρ : κ ⊨ Γ₂ -∗
    Γ₁ ⊨ InjR e : ρ : (τ + κ) ⊨ Γ₂.
  Proof.
    iIntros "#He !# %vs HΓ₁ //=".
    iApply (ewpw_bind [InjRCtx]); first done.
    iApply (ewpw_mono with "[HΓ₁]"); first (by iApply "He").
    iIntros "!# % [Hκ HΓ₂] /= !>". ewpw_pure_steps.
    iFrame. iExists v. iRight. by iFrame.
  Qed.

  Lemma sem_typed_match τ ρ κ ι Γ₁ Γ₂ Γ₃ e₁ x y e₂ e₃ :
    x ∉ env_dom Γ₂ → x ∉ env_dom Γ₃ → y ∉ env_dom Γ₂ → y ∉ env_dom Γ₃ →
    Γ₁ ⊨ e₁ : ρ : (τ + κ) ⊨ Γ₂ -∗
    (x, τ) ::? Γ₂ ⊨ e₂ : ρ : ι ⊨ Γ₃ -∗
    (y, κ) ::? Γ₂ ⊨ e₃ : ρ : ι ⊨ Γ₃ -∗
    Γ₁ ⊨ match: e₁ with InjL x => e₂ | InjR y => e₃ end : ρ : ι ⊨ Γ₃.
  Proof.
    iIntros (????) "#He₁ #He₂ #He₃ !# %vs HΓ₁ //=".
    iApply (ewpw_bind [CaseCtx _ _]); first done.
    iApply (ewpw_mono with "[HΓ₁]"); first (by iApply "He₁").
    iIntros "!# %v [(%w & [(-> & Hτ)|(-> & Hκ)]) HΓ₂] //= !>"; ewpw_pure_steps.
    - destruct x; simpl.
      + iApply (ewpw_mono with "[HΓ₂ Hτ]"); [by iApply "He₂"|eauto].
      + rewrite -subst_map_insert.
        iApply (ewpw_mono with "[HΓ₂ Hτ]"); first (iApply "He₂"; solve_env).
        iIntros "!# % [$ HΓ₃] //=". solve_env.
    - destruct y; simpl.
      + iApply (ewpw_mono with "[HΓ₂ Hκ]"); [iApply "He₃"; solve_env|eauto].
      + rewrite -subst_map_insert.
        iApply (ewpw_mono with "[HΓ₂ Hκ]"); [iApply "He₃"; solve_env|].
        iIntros "!# % [$ HΓ₃] //=". solve_env.
  Qed.

  Lemma sem_typed_none τ Γ₁: 
    ⊢ Γ₁ ⊨ NONE : ⟨⟩ : Option τ ⊨ Γ₁.
  Proof.
    iIntros. iApply sem_typed_left_inj. iApply sem_typed_unit. 
  Qed.

  Lemma sem_typed_some τ ρ Γ₁ Γ₂ e: 
    Γ₁ ⊨ e : ρ : τ ⊨ Γ₂ -∗ 
    Γ₁ ⊨ SOME e : ρ : Option τ ⊨ Γ₂.
  Proof.
    iIntros "He". iApply sem_typed_right_inj. iApply "He".
  Qed.

  Lemma sem_typed_match_option ρ κ ι Γ₁ Γ₂ Γ₃ e₁ x e₂ e₃ :
    x ∉ env_dom Γ₂ → x ∉ env_dom Γ₃ →
    Γ₁ ⊨ e₁ : ρ : Option κ ⊨ Γ₂ -∗
    Γ₂ ⊨ e₂ : ρ : ι ⊨ Γ₃ -∗
    (x, κ) :: Γ₂ ⊨ e₃ : ρ : ι ⊨ Γ₃ -∗
    Γ₁ ⊨ match: e₁ with NONE => e₂ | SOME x => e₃ end : ρ : ι ⊨ Γ₃.
  Proof.
    iIntros (??) "#He₁ #He₂ #He₃ !# %vs HΓ₁ //=".
    iApply (ewpw_bind [CaseCtx _ _]); first done.
    iApply (ewpw_mono with "[HΓ₁]"); first (by iApply "He₁").
    iIntros "!# %v [(%w & [(-> & _)|(-> & Hκ)]) HΓ₂] !> //="; ewpw_pure_steps.
    - iApply (ewpw_mono with "[HΓ₂]"); [iApply "He₂"; solve_env|eauto].
    - rewrite -subst_map_insert.
      iApply (ewpw_mono with "[HΓ₂ Hκ]"); [iApply "He₃"; solve_env|].
      iIntros "!# % [$ HΓ₃] //=". solve_env.
  Qed.

  Lemma bin_op_copy_types (τ κ ι : sem_ty Σ) op :
    typed_bin_op op τ κ ι → ⊢ copy_ty τ ∗ copy_ty κ ∗ copy_ty ι.
  Proof. intros []; (iSplit; [|iSplit]); solve_copy. Qed.

  Lemma sem_typed_bin_op τ κ ι ρ Γ₁ Γ₂ Γ₃ e₁ e₂ op :
    typed_bin_op op τ κ ι →
    Γ₂ ⊨ e₁ : ρ : τ ⊨ Γ₃ -∗
    Γ₁ ⊨ e₂ : ρ : κ ⊨ Γ₂ -∗
    Γ₁ ⊨ BinOp op e₁ e₂ : ρ : ι ⊨ Γ₃.
  Proof.
    iIntros (Hop) "#He₁ #He₂ !# %vs HΓ₁ //=".
    iDestruct (bin_op_copy_types _ _ _ _ Hop) as "[Hcpyτ [Hcpyκ Hcpyι]]". 
    iApply (ewpw_bind [BinOpRCtx _ _]); first done.
    iApply (ewpw_mono with "[HΓ₁]"); [iApply "He₂"; solve_env|eauto].
    iIntros "!# %v [Hκ HΓ₂] //= !>". 
    iDestruct ("Hcpyκ" with "Hκ") as "#Hκ'".
    iApply (ewpw_bind [BinOpLCtx _ _]); first done.
    iApply (ewpw_mono with "[HΓ₂]"); [iApply "He₁"; solve_env|eauto].
    iIntros "!# %w [Hτ HΓ₂] //= !>".
    destruct op; inversion_clear Hop;
      iDestruct "Hτ" as "(%n1 & ->)";
      iDestruct "Hκ'" as "(%n2 & ->)";
      ewpw_pure_steps; try done; eauto.
  Qed.
  
  Lemma sem_typed_if τ ρ Γ₁ Γ₂ Γ₃ e₁ e₂ e₃ :
    Γ₁ ⊨ e₁ : ρ : 𝔹 ⊨ Γ₂ -∗
    Γ₂ ⊨ e₂ : ρ : τ ⊨ Γ₃ -∗
    Γ₂ ⊨ e₃ : ρ : τ ⊨ Γ₃ -∗
    Γ₁ ⊨ (if: e₁ then e₂ else e₃) : ρ : τ ⊨ Γ₃.
  Proof.
    iIntros "#He₁ #He₂ #He₃ !# %vs HΓ₁ //=".
    iApply (ewpw_bind [IfCtx (subst_map vs e₂) (subst_map vs e₃)]) ;first done.
    iApply (ewpw_mono with "[HΓ₁]"); [iApply "He₁"; solve_env|eauto].
    iIntros "!# %v ((%b & ->) & HΓ₂) //= !>".
    destruct b; ewpw_pure_steps.
    - iApply (ewpw_mono with "[HΓ₂]"); [iApply "He₂"; solve_env|eauto].
    - iApply (ewpw_mono with "[HΓ₂]"); [iApply "He₃"; solve_env|eauto].
  Qed.
  
  (* Type abstraction and application *)
  Lemma sem_typed_TLam C Γ₁ Γ₂ e : 
    copy_env Γ₁ -∗
    (∀ α, Γ₁ ⊨ e : ⟨⟩ : C α ⊨ []) -∗
    Γ₁ ++ Γ₂ ⊨ (Λ: e) : ⟨⟩ : (∀T: α , C α)%T ⊨ Γ₂.
  Proof.
    iIntros "#Hcpy #He !# %vs HΓ₁₂ //=".
    iDestruct (env_sem_typed_app with "HΓ₁₂") as "[HΓ₁ HΓ₂]".
    iDestruct ("Hcpy" with "HΓ₁") as "#HΓ₁'".
    ewpw_pure_steps. iIntros "{$HΓ₂} %α //= !#". ewpw_pure_steps.
    iApply ewpw_mono; [iApply "He"; solve_env|].
    iIntros "!# %w [$ _] //=".
  Qed.

  Lemma sem_typed_TApp C τ ρ Γ₁ Γ₂ e :
    Γ₁ ⊨ e : ρ : (∀T: α , C α) ⊨ Γ₂ -∗
    Γ₁ ⊨ e <_> : ρ : C τ ⊨ Γ₂. 
  Proof.
    iIntros "#He !# %vs HΓ₁ /=".
    iApply (ewpw_bind [AppLCtx _]); first done.
    iApply (ewpw_mono with "[HΓ₁]"); [iApply "He"; solve_env|].
    iIntros "!# %w [Hw HΓ₂] //= !>".
    iApply ewpw_sub; first iApply row_le_nil.
    iApply (ewpw_mono_os with "[Hw]"); [iApply "Hw"|].
    iIntros "% HC !>". iFrame "#∗".
  Qed.

  (* Signature abstraction and application *)
  Lemma sem_typed_RLam C Γ₁ Γ₂ e : 
    copy_env Γ₁ -∗
    (∀ θ, Γ₁ ⊨ e : ⟨⟩ : C θ ⊨ []) -∗
    Γ₁ ++ Γ₂ ⊨ (Λ: e) : ⟨⟩ : (∀R: θ , C θ)%T ⊨ Γ₂.
  Proof.
    iIntros "#Hcpy #He !# %vs HΓ₁₂ /=".
    iDestruct (env_sem_typed_app with "HΓ₁₂") as "[HΓ₁ HΓ₂]".
    ewpw_pure_steps. iFrame.
    iDestruct ("Hcpy" with "HΓ₁") as "#HΓ₁'".
    iIntros (ρ). ewpw_pure_steps. iIntros "!#".
    ewpw_pure_steps.
    iApply ewpw_mono; [by iApply "He"|].
    iIntros "!# % [$ _] //=".
  Qed.

  Lemma sem_typed_RApp C ρ ρ' Γ₁ Γ₂ e :
    Γ₁ ⊨ e : ρ : (∀R: θ , C θ) ⊨ Γ₂ -∗
    Γ₁ ⊨ e <_> : ρ : C ρ' ⊨ Γ₂. 
  Proof.
    iIntros "#He !# %vs HΓ₁ /=".
    iApply (ewpw_bind [AppLCtx _]); first done.
    iApply (ewpw_mono with "[HΓ₁]"); [by iApply "He"|].
    iIntros "!# %v [HC HΓ₂] /= !>".
    iApply ewpw_sub; first iApply row_le_nil.
    iApply (ewpw_mono_os with "[HC]"); [iApply ("HC" $! ρ')|].
    iIntros "%w HCρ !>". iFrame "∗#".
  Qed.

  (* Existential type packing and unpacking *)
  Lemma sem_typed_pack C τ ρ Γ₁ Γ₂ e :
    Γ₁ ⊨ e : ρ : C τ ⊨ Γ₂ -∗
    Γ₁ ⊨ (pack: e) : ρ : (∃: α, C α) ⊨ Γ₂. 
  Proof.
    iIntros "#He %vs !# HΓ₁ //=".
    iApply (ewpw_bind [AppRCtx _]); first done.
    iApply (ewpw_mono with "[HΓ₁]"); [by iApply "He"|].
    iIntros "!# %v [Hτv HΓ₂] //= !>".
    unfold exist_pack. ewpw_pure_steps. iFrame.
    by iExists τ. 
  Qed.

  Lemma sem_typed_unpack C κ ρ Γ₁ Γ₂ Γ₃ x e₁ e₂ :
    x ∉ env_dom Γ₂ → x ∉ env_dom Γ₃ →
    Γ₁ ⊨ e₁ : ρ : (∃: α, C α) ⊨ Γ₂ -∗
    (∀ τ, (x, C τ) :: Γ₂ ⊨ e₂ : ρ : κ ⊨ Γ₃) -∗
    Γ₁ ⊨ (unpack: x := e₁ in e₂) : ρ : κ ⊨ Γ₃.
  Proof.
    iIntros (??) "#He₁ #He₂ %vs !# HΓ₁ //=".
    iApply (ewpw_bind [AppRCtx _]); first done.
    iApply (ewpw_mono with "[HΓ₁]"); [by iApply "He₁"|].
    iIntros "!# %w [(%τ & Hτw) HΓ₂] //= !>". unfold exist_unpack.
    ewpw_pure_steps. rewrite -subst_map_insert.
    iApply (ewpw_mono with "[HΓ₂ Hτw]"); [iApply "He₂";solve_env|].
    iIntros "!# %u [Hκ HΓ₃]". solve_env.
  Qed.

  (* Recursive type rules *)
  Lemma sem_typed_fold C ρ Γ₁ Γ₂ e `{NonExpansive C}:
    Γ₁ ⊨ e : ρ : (C (μT: α, C α)) ⊨ Γ₂ -∗
    Γ₁ ⊨ (fold: e) : ρ : (μT: α, C α) ⊨ Γ₂.
  Proof.
    iIntros "#He %vs !# HΓ₁ //=".
    iApply (ewpw_bind [AppRCtx _]); first done.
    iApply (ewpw_mono with "[HΓ₁]"); [by iApply "He"|].
    iIntros "!# %w [HC HΓ₂] //= !>".
    unfold rec_fold. ewpw_pure_steps. 
    iFrame. by iApply sem_ty_rec_unfold. 
  Qed.

  Lemma sem_typed_unfold C ρ Γ₁ Γ₂ e `{NonExpansive C}:
    Γ₁ ⊨ e : ρ : (μT: α, C α) ⊨ Γ₂ -∗
    Γ₁ ⊨ (unfold: e) : ρ : (C (μT: α, C α)) ⊨ Γ₂.
  Proof.
    iIntros "#He %vs !# HΓ₁ //=".
    iApply (ewpw_bind [AppRCtx _]); first done. 
    iApply (ewpw_mono with "[HΓ₁]"); [by iApply "He"|].
    iIntros "!# %w [Hμ HΓ₂] //= !>". 
    rewrite sem_ty_rec_unfold. 
    unfold rec_unfold. ewpw_pure_steps. 
    iFrame.
  Qed.

  (* List type rules *)
  Lemma sem_typed_nil τ Γ : 
    ⊢ Γ ⊨ NIL : ⟨⟩ : List τ ⊨ Γ.
  Proof.
    iIntros "!# %vs HΓ //=". 
    ewpw_pure_steps. unfold sem_ty_list. 
    rewrite sem_ty_rec_unfold. iIntros "{$HΓ} !>".
    unfold ListF. iExists #(). by iLeft.
  Qed.
  
  Lemma sem_typed_cons τ ρ Γ₁ Γ₂ Γ₃ e₁ e₂ `{! OSRow ρ}:
    Γ₂ ⊨ e₁ : ρ : τ ⊨ Γ₃-∗
    Γ₁ ⊨ e₂ : ρ : List τ ⊨ Γ₂-∗
    Γ₁ ⊨ CONS e₁ e₂ : ρ : List τ ⊨ Γ₃.
  Proof.
    iIntros "#He₁ #He₂ !# %vs HΓ₁ //=". 
    iApply (ewpw_bind [InjRCtx; PairRCtx _]); first done.
    iApply (ewpw_mono with "[HΓ₁]"); [by iApply "He₂"|].
    iIntros "!# %l [Hl HΓ₂] //= !>".
    iApply (ewpw_bind [InjRCtx; PairLCtx _]); first done.
    iApply (ewpw_mono_os with "[HΓ₂]"); [by iApply "He₁"|].
    iIntros "%x [Hx HΓ₃] //= !>". ewpw_pure_steps.
    unfold sem_ty_list. rewrite !sem_ty_rec_unfold.
    iIntros "{$HΓ₃} !>". iExists (x,l)%V. iRight. iSplit; first done.
    iExists x, l. iFrame; iSplit; first done.
    by rewrite sem_ty_rec_unfold. 
  Qed.

  Lemma sem_typed_cons_ms τ ρ Γ₁ Γ₂ Γ₃ e₁ e₂ :
    copy_ty τ -∗
    Γ₂ ⊨ e₁ : ρ : τ ⊨ Γ₃-∗
    Γ₁ ⊨ e₂ : ρ : List τ ⊨ Γ₂-∗
    Γ₁ ⊨ CONS e₁ e₂ : ρ : List τ ⊨ Γ₃.
  Proof.
    iIntros "#Hτcpy #He₁ #He₂ !# %vs HΓ₁ //=". 
    iApply (ewpw_bind [InjRCtx; PairRCtx _]); first done.
    iApply (ewpw_mono with "[HΓ₁]"); [by iApply "He₂"|].
    iIntros "!# %l [Hl HΓ₂] //= !>".
    iApply (ewpw_bind [InjRCtx; PairLCtx _]); first done.
    iDestruct (copy_ty_list with "Hτcpy Hl") as "#Hl'". 
    iApply (ewpw_mono with "[HΓ₂]"); [by iApply "He₁"|].
    iIntros "!# %x [Hx HΓ₃] //= !>". ewpw_pure_steps.
    unfold sem_ty_list. rewrite !sem_ty_rec_unfold.
    iIntros "{$HΓ₃} !>". iExists (x,l)%V. iRight. iSplit; first done.
    iExists x, l. iFrame; iSplit; first done.
    by rewrite sem_ty_rec_unfold. 
  Qed.

  Lemma sem_typed_match_list τ ρ κ Γ₁ Γ₂ Γ₃ x xs e₁ e₂ e₃ :
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
    iIntros (?????) "#He₁ #He₂ #He₃ !# %vs HΓ₁ //=".
    iApply (ewpw_bind [CaseCtx _ _]); first done. simpl.
    iApply (ewpw_mono with "[HΓ₁]");
      [iApply (sem_typed_unfold with "He₁ HΓ₁")|].
    iIntros "!# %v₁ [Hl HΓ₂] !>". 
    iDestruct "Hl" as "(%v' & [[-> ->]|(-> & (%w₁ & %w₂ & -> & Hτ & Hμ))])"; 
    ewpw_pure_steps.
    { iApply (ewpw_mono with "[HΓ₂]"); 
        [iApply ("He₂" with "[$HΓ₂]")|eauto]. }
    rewrite lookup_delete. simpl.
    repeat solve_dec. ewpw_pure_steps. repeat solve_dec.
    rewrite delete_commute -subst_map_insert delete_commute.
    rewrite insert_delete_insert. rewrite subst_map_insert.
    rewrite subst_subst_ne; [|congruence]. rewrite delete_commute.
    rewrite -subst_map_insert -delete_insert_ne; try congruence.
    rewrite -subst_map_insert. 
    iApply (ewpw_mono with "[Hμ Hτ HΓ₂]"); [iApply "He₃"; solve_env|].
    { rewrite env_sem_typed_insert; last done; solve_env. }
    iIntros "!# %u [Hκ HΓ₃]". iFrame.
    rewrite -(env_sem_typed_insert _ _ x w₁); last done.
    by rewrite -(env_sem_typed_insert _ _ xs w₂).
  Qed.

  (* Reference rules *)
  
  Lemma sem_typed_alloc τ ρ Γ₁ Γ₂ e :
    Γ₁ ⊨ e : ρ : τ ⊨ Γ₂ -∗
    Γ₁ ⊨ ref e : ρ : Ref τ ⊨ Γ₂.
  Proof.
    iIntros "#He !# %vs HΓ₁ //=".
    iApply (ewpw_bind [AllocCtx]); first done. simpl.
    iApply (ewpw_mono with "[HΓ₁]"); [by iApply "He"|].
    iIntros "!# %v [Hτ HΓ₂] !>".
    iApply ewpw_alloc. iIntros "!> %l Hl !>". solve_env.
  Qed.
  
  Lemma sem_typed_load τ Γ x : 
    ⊢ ((x, Ref τ) :: Γ ⊨ !x : ⟨⟩ : τ ⊨ (x, Ref ⊤) :: Γ).
  Proof.
    iIntros "%vs !# //= [%v (%Hrw & (%w & -> & (%l & Hl & Hτ)) & HΓ)]".
    rewrite Hrw. iApply (ewpw_load with "Hl").
    iIntros "!> Hl !>". solve_env.
  Qed.
  
  Lemma sem_typed_load_copy τ Γ x :
    copy_ty τ -∗
    ((x, Ref τ) :: Γ ⊨ !x : ⟨⟩ : τ ⊨ (x, Ref τ) :: Γ).
  Proof.
    iIntros "#Hcpy %vs !# //= [%v (%Hrw & (%w & -> & (%l & Hl & Hτ)) & HΓ)]".
    rewrite Hrw. iApply (ewpw_load with "Hl").
    iDestruct ("Hcpy" with "Hτ") as "#Hτ'".
    iIntros "!> Hl !>". solve_env.
  Qed.

  Lemma sem_typed_free τ ρ Γ₁ Γ₂ e :
    Γ₁ ⊨ e : ρ : Ref τ ⊨ Γ₂ -∗
    Γ₁ ⊨ Free e : ρ : τ ⊨ Γ₂.
  Proof.
    iIntros "#He !# %vs HΓ₁ //=".
    iApply (ewpw_bind [FreeCtx]); first done. simpl.
    iApply (ewpw_mono with "[HΓ₁]"); [by iApply "He"|].
    iIntros "!# %v [(%l & -> & (%w & Hl & Hτ)) HΓ₂]".
    iApply (ewpw_free with "Hl"). iIntros "!> {$Hτ} {$HΓ₂} //=". 
  Qed.

  Lemma sem_typed_store τ κ ι ρ Γ₁ Γ₂ x e :
    (x, Ref τ) :: Γ₁ ⊨ e : ρ : ι ⊨ (x, Ref κ) :: Γ₂ -∗
    (x, Ref τ) :: Γ₁ ⊨ (x <- e) : ρ : () ⊨ (x, Ref ι) :: Γ₂.
  Proof.
    iIntros "#He !# %vs //= HΓ₁' //=".
    iApply (ewpw_bind [StoreRCtx _]); first done. simpl.
    iApply (ewpw_mono with "[HΓ₁']"); [iApply "He"; solve_env|].
    iIntros "!# %w [Hι [%v (%Hrw & (%l & -> & (% & Hl & Hκ)) & HΓ₂)]] /=". 
    rewrite Hrw. iApply (ewpw_store with "Hl"). 
    iIntros "!> !> Hl !>". solve_env. 
  Qed.

  Lemma sem_typed_alloc_cpy τ ρ Γ₁ Γ₂ e :
    Γ₁ ⊨ e : ρ : τ ⊨ Γ₂ -∗
    Γ₁ ⊨ ref e : ρ : Refᶜ  τ ⊨ Γ₂.
  Proof.
    iIntros "#He !# %vs HΓ₁ //=".
    iApply (ewpw_bind [AllocCtx]); first done. simpl.
    iApply (ewpw_mono with "[HΓ₁]"); [by iApply "He"|].
    iIntros "!# %v [Hτ HΓ₂] !>".
    iApply ewpw_alloc. iIntros "!> %l Hl". iFrame.
    iMod (inv_alloc (tyN.@l) _
       (∃ w, l ↦ w ∗ τ w)%I with "[Hl Hτ]") as "#Hinv".
    { iExists v. by iFrame. }
    iModIntro. iExists l. by auto.
  Qed.

  Lemma sem_typed_load_cpy τ ρ Γ₁ Γ₂ e :
    copy_ty τ -∗
    Γ₁ ⊨ e : ρ : Refᶜ τ ⊨ Γ₂ -∗
    Γ₁ ⊨ !e : ρ : τ ⊨ Γ₂.
  Proof.
    iIntros "#Hcpy #He %vs !# //= HΓ₁".
    iApply (ewpw_bind [LoadCtx]); first done.
    iApply (ewpw_mono with "[HΓ₁]"); [by iApply "He"|].
    iIntros "!# %v [(%l & -> & Hinv) HΓ₂] /= !>".
    iApply (ewpw_atomic _ (⊤ ∖ ↑tyN.@l)).
    iMod (inv_acc _ (tyN.@l) with "Hinv") as "[(%u & >Hl & Hτ) Hclose]"; first done.
    iModIntro. iApply (ewpw_load with "Hl").
    iIntros "!> Hl !>". 
    iDestruct ("Hcpy" with "Hτ") as "#Hτ'".
    iMod ("Hclose" with "[Hl]"); solve_env.
  Qed.

  Lemma sem_typed_store_cpy τ ρ Γ₁ Γ₂ Γ₃ e₁ e₂ `{! OSRow ρ}: 
    Γ₂ ⊨ e₁ : ρ : Refᶜ τ ⊨ Γ₃ -∗
    Γ₁ ⊨ e₂ : ρ : τ ⊨ Γ₂ -∗
    Γ₁ ⊨ (e₁ <- e₂) : ρ : () ⊨ Γ₃.
  Proof.
    iIntros "#He₁ #He₂ %vs !# /= HΓ₁ /=".
    iApply (ewpw_bind [StoreRCtx _]); first done. simpl.
    iApply (ewpw_mono with "[HΓ₁]"); [by iApply "He₂"|].
    iIntros "!# %w [Hτ HΓ₂] !>". 
    iApply (ewpw_bind [StoreLCtx _]); first done. simpl.
    iApply (ewpw_mono_os with "[HΓ₂]"); [by iApply "He₁"|].
    iIntros "%u [(%l & -> & Hinv) HΓ₃] !>".
    iApply (ewpw_atomic _ (⊤ ∖ ↑tyN.@l)).
    iMod (inv_acc _ (tyN.@l) with "Hinv") as "[(%u & >Hl & _) Hclose]"; first done.
    iModIntro. iApply (ewpw_store with "Hl"). 
    iIntros "!> Hl !>".  
    iMod ("Hclose" with "[Hl Hτ]"); solve_env.
  Qed.

  Lemma sem_typed_replace_cpy_os τ ρ Γ₁ Γ₂ Γ₃ e₁ e₂ `{! OSRow ρ}: 
    Γ₂ ⊨ e₁ : ρ : Refᶜ τ ⊨ Γ₃ -∗
    Γ₁ ⊨ e₂ : ρ : τ ⊨ Γ₂ -∗
    Γ₁ ⊨ (e₁ <!- e₂) : ρ : τ ⊨ Γ₃.
  Proof.
    iIntros "#He₁ #He₂ %vs !# /= HΓ₁ /=".
    iApply (ewpw_bind [ReplaceRCtx _]); first done. simpl.
    iApply (ewpw_mono_os with "[HΓ₁]"); [by iApply "He₂"|].
    iIntros "%w [Hτ HΓ₂] !>". 
    iApply (ewpw_bind [ReplaceLCtx _]); first done. simpl.
    iApply (ewpw_mono_os with "[HΓ₂]"); [by iApply "He₁"|].
    iIntros "%u [(%l & -> & Hinv) HΓ₃] !>".
    iApply (ewpw_atomic _ (⊤ ∖ ↑tyN.@l)).
    iMod (inv_acc _ (tyN.@l) with "Hinv") as "[(%u & >Hl & Hu) Hclose]"; first done.
    iModIntro. iApply (ewpw_replace with "Hl"). 
    iIntros "!> Hl !>".  
    iMod ("Hclose" with "[Hl Hτ]").
    { iExists w. iFrame. } 
    iIntros "!>". iFrame.
  Qed.
  
  Lemma sem_typed_replace_cpy_ms τ ρ Γ₁ Γ₂ Γ₃ e₁ e₂ :
    copy_ty τ -∗
    Γ₂ ⊨ e₁ : ρ : Refᶜ τ ⊨ Γ₃ -∗
    Γ₁ ⊨ e₂ : ρ : τ ⊨ Γ₂ -∗
    Γ₁ ⊨ (e₁ <!- e₂) : ρ : τ ⊨ Γ₃.
  Proof.
    iIntros "#Hcpy #He₁ #He₂ %vs !# /= HΓ₁ /=".
    iApply (ewpw_bind [ReplaceRCtx _]); first done. simpl.
    iApply (ewpw_mono with "[HΓ₁]"); [by iApply "He₂"|].
    iIntros "!# %w [Hτ HΓ₂] !>". 
    iApply (ewpw_bind [ReplaceLCtx _]); first done. simpl.
    iDestruct ("Hcpy" with "Hτ") as "#Hτ'". 
    iApply (ewpw_mono with "[HΓ₂]"); [by iApply "He₁"|].
    iIntros "!# %u [(%l & -> & Hinv) HΓ₃] !>".
    iApply (ewpw_atomic _ (⊤ ∖ ↑tyN.@l)).
    iMod (inv_acc _ (tyN.@l) with "Hinv") as "[(%u & >Hl & Hu) Hclose]"; first done.
    iModIntro. iApply (ewpw_replace with "Hl"). 
    iIntros "!> Hl !>".  
    iMod ("Hclose" with "[Hl]").
    { iExists w. iFrame "#∗". } 
    iIntros "!>". iFrame.
  Qed.

  (* Effect handling rules *)
  
  Lemma sem_typed_perform_os τ ρ' l (A B : sem_ty Σ → sem_ty Σ) Γ₁ Γ₂ e
    `{ NonExpansive A, NonExpansive B, ! OSRow ρ' } :
    let σ := (∀S: α, A α ⇒ B α | OS)%S in
    let ρ := ((l, σ) ·: ρ')%R in
    Γ₁ ⊨ e : ρ : A τ ⊨ Γ₂ -∗
    Γ₁ ⊨ (perform: (effect l, e) ) : ρ : B τ ⊨ Γ₂.
  Proof.
    iIntros (σ ρ) "#He !# %vs HΓ₁ //=". 
    iApply (ewpw_bind [AppRCtx _; DoCtx OS; PairRCtx _]); simpl; first done.
    assert (HOS : OSRow ((l, σ) · ρ')).
    { apply row_ins_os_row; [apply _|done]. }
    iApply (ewpw_mono_os with "[HΓ₁]"); [by iApply "He"|].
    iIntros "%v [Hι HΓ₂] //= !>". rewrite /rec_perform.
    iApply (ewpw_bind [AppRCtx _]); first done.
    ewpw_pure_steps. iApply ewpw_do_os.
    rewrite /sem_row_iEff /=.
    iExists v, l, 0, σ. iSplit; first done.
    iAssert (ρ !! (l, 0) ≡ Some σ)%I as "Hlookup".
    { rewrite lookup_insert //. }
    iDestruct (filter_os_lookup ρ l 0 σ) as "[_ H]".
    iDestruct ("H" with "[]") as "$".
    { iFrame "#". rewrite /σ {2} sem_sig_eff_unfold_1 //. }
    rewrite sem_sig_eff_eq /=.
    iExists τ, v. iFrame. iSplitR; first done.
    iIntros "%b Hκ". ewpw_pure_steps. iFrame "∗#".
  Qed.

  Lemma sem_typed_perform_ms τ ρ' m l (A B : sem_ty Σ → sem_ty Σ) Γ₁ Γ₂ e
    `{ NonExpansive A, NonExpansive B } :
    let σ := (∀S: α, A α ⇒ B α | m)%S in
    let ρ := ((l, σ) ·: ρ')%R in
    copy_env Γ₂ -∗
    Γ₁ ⊨ e : ρ : A τ ⊨ Γ₂ -∗
    Γ₁ ⊨ (performₘ: (effect l, e)) : ρ : B τ ⊨ Γ₂.
  Proof.
    iIntros (σ ρ) "#HΓcpy #He !# %vs HΓ₁ //=". 
    iApply (ewpw_bind [AppRCtx _; DoCtx MS; PairRCtx _]); simpl; first done.
    iApply (ewpw_mono with "[HΓ₁]"); [by iApply "He"|].
    iIntros "!# %v [Hι HΓ₂] //= !>". rewrite /rec_perform.
    iApply (ewpw_bind [AppRCtx _]); first done.
    ewpw_pure_steps. iApply ewpw_do_ms. simpl.
    iExists v, l, 0, σ. iSplit; first done.
    iSplit; first rewrite lookup_insert //.
    rewrite sem_sig_eff_eq /=.
    iExists τ, v. iFrame. iSplitR; first done.
    iDestruct ("HΓcpy" with "HΓ₂") as "#HΓ₂'". 
    destruct m; simpl; last iIntros "!#"; 
    iIntros "%b Hκ"; ewpw_pure_steps; iFrame "∗#".
  Qed.

  Lemma sem_typed_lft τ l σ ρ Γ₁ Γ₂ e :
    Γ₁ ⊨ e : ρ : τ ⊨ Γ₂ -∗
    Γ₁ ⊨ (lft: (effect l, e)) : ((l, σ) ·: ρ)%R : τ ⊨ Γ₂.
  Proof.
    iIntros "#He !# %vs HΓ₁ /=".
    iApply ewpw_lft. by iApply "He".
  Qed.

  Lemma sem_typed_unlft τ ρ l Γ₁ Γ₂ e :
    Γ₁ ⊨ e : ⦗ ρ | l ⦘ : τ ⊨ Γ₂ -∗
    Γ₁ ⊨ (unlft: (effect l, e)) : ρ : τ ⊨ Γ₂.
  Proof.
    iIntros "#He !# %vs HΓ₁ /=".
    iApply ewpw_unlft. by iApply "He".
  Qed.

  Lemma sem_typed_shallow_try_os m l A B τ τ' ρ' ρ'' Γ₁ Γ₂ Γ₃ Γ' x k e h r `{NonExpansive A, NonExpansive B, ! OSRow ρ' }:
    x ∉ env_dom Γ₂ → x ∉ env_dom Γ' → x ∉ env_dom Γ₃ → k ∉ env_dom Γ₃ → k ∉ env_dom Γ' → x ≠ k →
    let σ := (∀S: α, A α ⇒ B α | m)%S in
    let ρ := ((l, σ) ·: ρ')%R in
    ρ' ≤R ρ'' -∗
    Γ₁ ⊨ e : ρ : τ ⊨ Γ₂ -∗
    (∀ α, (x, A α) :: (k, B α -{ ρ }-∘ τ) :: Γ' ⊨ h : ρ'' : τ' ⊨ Γ₃) -∗
    (x, τ) :: Γ₂ ++ Γ' ⊨ r : ρ'' : τ' ⊨ Γ₃ -∗
    Γ₁ ++ Γ' ⊨ (shallow-try-ls: e handle l with
                  effect  (λ: x k, h)
                | return  (λ: x, r) end) : ρ'' : τ' ⊨ Γ₃.
  Proof. 
    iIntros (????????) "#Hle #He #Hh #Hr !# %vs HΓ₁Γ' /=".
    iDestruct (env_sem_typed_app with "HΓ₁Γ'") as "[HΓ₁ HΓ']". 
    ewpw_pure_steps. iApply (ewpw_shallow_try_ls _ _ OS with "[HΓ₁] [HΓ']").
    { iApply ("He" with "HΓ₁"). }
    repeat iSplit; eauto. simpl. iSplit.
    - iIntros (v) "[Hτ HΓ₂]". ewpw_pure_steps. rewrite - subst_map_insert. 
      iApply (ewpw_mono with "[HΓ₂ HΓ' Hτ]").
      { iApply "Hr". solve_env. iApply env_sem_typed_app; solve_env. }
      iIntros "!# %w [$ HΓ₃] !>". solve_env.
    - iIntros (v k') "(%Φ & Hρ & HPost)".
      rewrite sem_sig_eff_eq. iDestruct "Hρ" as "(%α & %a & <- & Ha & Hκb)". 
      ewpw_pure_steps. solve_dec.
      rewrite subst_subst_ne // - subst_map_insert - delete_insert_ne // - subst_map_insert.
      iApply (ewpw_mono with "[HΓ' Ha Hκb HPost]").
      + iApply "Hh". solve_env. do 2 rewrite - env_sem_typed_insert //. iFrame.
        iIntros (?) "HB". 
        rewrite !bi.intuitionistically_if_elim. 
        iApply (ewpw_mono with "[Hκb HPost HB]").
        { iApply ("HPost" with "[Hκb HB]"). by iApply "Hκb". }
        iIntros "!# % [$ _] //".
      + iIntros "!# % [$ HΓ₃] !>". do 2 rewrite - env_sem_typed_insert //. 
  Qed.

  Lemma sem_typed_shallow_try_ms l A B τ τ' ρ' ρ'' Γ₁ Γ₂ Γ₃ Γ' x k e h r `{NonExpansive A, NonExpansive B }:
    x ∉ env_dom Γ₂ → x ∉ env_dom Γ' → x ∉ env_dom Γ₃ → k ∉ env_dom Γ₃ → k ∉ env_dom Γ' → x ≠ k →
    let σ := (∀S: α, A α ⇒ B α | MS)%S in
    let ρ := ((l, σ) ·: ρ')%R in
    copy_env Γ' -∗
    ρ' ≤R ρ'' -∗
    Γ₁ ⊨ e : ρ : τ ⊨ Γ₂ -∗
    (∀ α, (x, A α) :: (k, B α -{ ρ }-> τ) :: Γ' ⊨ h : ρ'' : τ' ⊨ Γ₃) -∗
    (x, τ) :: Γ₂ ++ Γ' ⊨ r : ρ'' : τ' ⊨ Γ₃ -∗
    Γ₁ ++ Γ' ⊨ (shallow-try-ls: e handle l with
                  effect  (λ: x k, h)
                | return  (λ: x, r) end) : ρ'' : τ' ⊨ Γ₃.
  Proof. 
    iIntros (????????) "#Hcpy #Hle #He #Hh #Hr !# %vs HΓ₁Γ' /=".
    iDestruct (env_sem_typed_app with "HΓ₁Γ'") as "[HΓ₁ HΓ'']". 
    iDestruct ("Hcpy" with "HΓ''") as "#HΓ'".
    ewpw_pure_steps. iApply (ewpw_shallow_try_ls _ _ MS with "[HΓ₁] [HΓ']").
    { iApply ("He" with "HΓ₁"). }
    repeat iSplit; eauto. simpl. iIntros "!#". iSplit.
    - iIntros (v) "[Hτ HΓ₂]". ewpw_pure_steps. rewrite - subst_map_insert. 
      iApply (ewpw_mono with "[HΓ₂ HΓ' Hτ]").
      { iApply "Hr". solve_env. iApply env_sem_typed_app; solve_env. }
      iIntros "!# %w [$ HΓ₃] !>". rewrite - env_sem_typed_insert //.
    - iIntros (v k') "(%Φ & Hρ & HPost)".
      rewrite sem_sig_eff_eq. iDestruct "Hρ" as "(%α & %a & <- & Ha & Hκb)". 
      ewpw_pure_steps. solve_dec.
      rewrite subst_subst_ne // - subst_map_insert - delete_insert_ne // - subst_map_insert.
      iApply (ewpw_mono with "[HΓ' Ha Hκb HPost]").
      + iApply "Hh". solve_env; last do 2 rewrite - env_sem_typed_insert //. 
        iDestruct "Hκb" as "#Hκb". iDestruct "HPost" as "#HPost".
        iIntros (?) "!# HB". 
        iApply (ewpw_mono with "[Hκb HPost HB]").
        { iApply ("HPost" with "[Hκb HB]"). by iApply "Hκb". }
        iIntros "!# % [$ _] //".
      + iIntros "!# % [$ HΓ₃] !>". do 2 rewrite - env_sem_typed_insert //. 
  Qed.

  Lemma sem_typed_shallow_try_ms_alt l A B τ τ' ρ' ρ'' Γ₁ Γ₂ Γ₃ Γ' x k e h r `{NonExpansive A, NonExpansive B, ! OSRow ρ' }:
    x ∉ env_dom Γ₂ → x ∉ env_dom Γ' → x ∉ env_dom Γ₃ → k ∉ env_dom Γ₃ → k ∉ env_dom Γ' → x ≠ k →
    let σ := (∀S: α, A α ⇒ B α | MS)%S in
    let ρ := ((l, σ) ·: ρ')%R in
    ρ' ≤R ρ'' -∗
    Γ₁ ⊨ e : ρ : τ ⊨ Γ₂ -∗
    (∀ α, (x, A α) :: (k, B α -{ ρ }-> τ) :: Γ' ⊨ h : ρ'' : τ' ⊨ Γ₃) -∗
    (x, τ) :: Γ₂ ++ Γ' ⊨ r : ρ'' : τ' ⊨ Γ₃ -∗
    Γ₁ ++ Γ' ⊨ (shallow-try-ls: e handle l with
                  effect  (λ: x k, h)
                | return  (λ: x, r) end) : ρ'' : τ' ⊨ Γ₃.
  Proof. 
    iIntros (????????) "#Hle #He #Hh #Hr !# %vs HΓ₁Γ' /=".
    iDestruct (env_sem_typed_app with "HΓ₁Γ'") as "[HΓ₁ HΓ']". 
    ewpw_pure_steps. iApply (ewpw_shallow_try_ls _ _ OS with "[HΓ₁] [HΓ']").
    { iApply ("He" with "HΓ₁"). }
    repeat iSplit; eauto. simpl. iSplit.
    - iIntros (v) "[Hτ HΓ₂]". ewpw_pure_steps. rewrite - subst_map_insert. 
      iApply (ewpw_mono with "[HΓ₂ HΓ' Hτ]").
      { iApply "Hr". solve_env. iApply env_sem_typed_app; solve_env. }
      iIntros "!# %w [$ HΓ₃] !>". solve_env.
    - iIntros (v k') "(%Φ & Hρ & HPost)".
      rewrite sem_sig_eff_eq. iDestruct "Hρ" as "(%α & %a & <- & Ha & Hκb)". 
      ewpw_pure_steps. solve_dec.
      rewrite subst_subst_ne // - subst_map_insert - delete_insert_ne // - subst_map_insert.
      iApply (ewpw_mono with "[HΓ' Ha Hκb HPost]").
      + iApply "Hh". solve_env; last do 2 rewrite - env_sem_typed_insert //.
        iDestruct "Hκb" as "#Hκb". iDestruct "HPost" as "#HPost".
        iIntros (?) "!# HB". 
        iApply (ewpw_mono with "[Hκb HPost HB]").
        { iApply ("HPost" with "[Hκb HB]"). by iApply "Hκb". }
        iIntros "!# % [$ _] //".
      + iIntros "!# % [$ HΓ₃] !>". do 2 rewrite - env_sem_typed_insert //. 
  Qed.

  Lemma sem_typed_deep_try_os m l A B τ τ' ρ' ρ'' Γ₁ Γ₂ Γ₃ Γ' x k e h r `{NonExpansive A, NonExpansive B}:
    x ∉ env_dom Γ₂ → x ∉ env_dom Γ' → x ∉ env_dom Γ₃ → k ∉ env_dom Γ₃ → k ∉ env_dom Γ' → x ≠ k →
    let σ := (∀S: α, A α ⇒ B α | m)%S in
    let ρ := ((l, σ) ·: ρ')%R in
    copy_env Γ' -∗
    ρ' ≤R ρ'' -∗
    Γ₁ ⊨ e : ρ : τ ⊨ Γ₂ -∗
    (∀ α, (x, A α) :: (k, B α -{ ρ'' }-∘ τ') :: Γ' ⊨ h : ρ'' : τ' ⊨ Γ₃) -∗
    (x, τ) :: Γ₂ ++ Γ' ⊨ r : ρ'' : τ' ⊨ Γ₃ -∗
    Γ₁ ++ Γ' ⊨ (deep-try-ls: e handle l with
                        effect  (λ: x k, h)
                      | return  (λ: x, r) end)%E : ρ'' : τ' ⊨ Γ₃.
  Proof.
    iIntros (????????) "#Hcpy #Hle #He #Hh #Hr !# %vs HΓ₁Γ' /=".
    iDestruct (env_sem_typed_app with "HΓ₁Γ'") as "[HΓ₁ HΓ'']". 
    iDestruct ("Hcpy" with "HΓ''") as "#HΓ'".
    ewpw_pure_steps. iApply (ewpw_deep_try_ls _ _ MS with "[HΓ₁] [HΓ']").
    { iApply ("He" with "HΓ₁"). }
    iLöb as "IH".
    rewrite deep_handler_ls_unfold /deep_handler_pre.
    repeat iSplit; eauto. simpl. iIntros "!#". 
    - iIntros (v) "[Hτ HΓ₂]". ewpw_pure_steps. rewrite - subst_map_insert. 
      iApply (ewpw_mono with "[HΓ₂ HΓ' Hτ]").
      { iApply "Hr". solve_env. iApply env_sem_typed_app; solve_env. }
      iIntros "!# %w [$ HΓ₃] !>". solve_env.
    - iIntros (v k') "!# (%Φ & Hρ & HPost)".
      rewrite sem_sig_eff_eq. iDestruct "Hρ" as "(%α & %a & <- & Ha & Hκb)". 
      ewpw_pure_steps. solve_dec.
      rewrite subst_subst_ne // - subst_map_insert - delete_insert_ne // - subst_map_insert.
      iApply (ewpw_mono with "[HΓ' Ha Hκb HPost]").
      + iApply "Hh". solve_env. do 2 rewrite - env_sem_typed_insert //. iFrame "#".
        iIntros (?) "HB". 
        rewrite !bi.intuitionistically_if_elim. 
        iApply (ewpw_mono with "[Hκb HPost HB]").
        { iApply ("HPost" with "[Hκb HB]"). by iApply "Hκb". iNext. rewrite - deep_handler_ls_unfold. iApply "IH". }
        iIntros "!# % [$ _] //".
      + iIntros "!# % [$ HΓ₃] !>". do 2 rewrite - env_sem_typed_insert //. 
  Qed.

  Lemma sem_typed_deep_try_ms l A B τ τ' ρ' ρ'' Γ₁ Γ₂ Γ₃ Γ' x k e h r `{NonExpansive A, NonExpansive B}:
    x ∉ env_dom Γ₂ → x ∉ env_dom Γ' → x ∉ env_dom Γ₃ → k ∉ env_dom Γ₃ → k ∉ env_dom Γ' → x ≠ k →
    let σ := (∀S: α, A α ⇒ B α | MS)%S in
    let ρ := ((l, σ) ·: ρ')%R in
    copy_env Γ' -∗
    ρ' ≤R ρ'' -∗
    Γ₁ ⊨ e : ρ : τ ⊨ Γ₂ -∗
    (∀ α, (x, A α) :: (k, B α -{ ρ'' }-> τ') :: Γ' ⊨ h : ρ'' : τ' ⊨ Γ₃) -∗
    (x, τ) :: Γ₂ ++ Γ' ⊨ r : ρ'' : τ' ⊨ Γ₃ -∗
    Γ₁ ++ Γ' ⊨ (deep-try-ls: e handle l with
                        effect  (λ: x k, h)
                      | return  (λ: x, r) end)%E : ρ'' : τ' ⊨ Γ₃.
  Proof.
    iIntros (????????) "#Hcpy #Hle #He #Hh #Hr !# %vs HΓ₁Γ' /=".
    iDestruct (env_sem_typed_app with "HΓ₁Γ'") as "[HΓ₁ HΓ'']". 
    iDestruct ("Hcpy" with "HΓ''") as "#HΓ'".
    ewpw_pure_steps. iApply (ewpw_deep_try_ls _ _ MS with "[HΓ₁] [HΓ']").
    { iApply ("He" with "HΓ₁"). }
    iLöb as "IH".
    rewrite deep_handler_ls_unfold /deep_handler_pre.
    repeat iSplit; eauto. simpl. iIntros "!#". 
    - iIntros (v) "[Hτ HΓ₂]". ewpw_pure_steps. rewrite - subst_map_insert. 
      iApply (ewpw_mono with "[HΓ₂ HΓ' Hτ]").
      { iApply "Hr". solve_env. iApply env_sem_typed_app; solve_env. }
      iIntros "!# %w [$ HΓ₃] !>". solve_env.
    - iIntros (v k') "!# (%Φ & Hρ & HPost)".
      rewrite sem_sig_eff_eq. iDestruct "Hρ" as "(%α & %a & <- & Ha & Hκb)". 
      ewpw_pure_steps. solve_dec.
      rewrite subst_subst_ne // - subst_map_insert - delete_insert_ne // - subst_map_insert.
      iApply (ewpw_mono with "[HΓ' Ha Hκb HPost]").
      + iApply "Hh". solve_env; last do 2 rewrite - env_sem_typed_insert //. 
        iDestruct "Hκb" as "#Hκb". iDestruct "HPost" as "#HPost".
        iIntros (?) "!# HB". 
        iApply (ewpw_mono with "[Hκb HPost HB]").
        { iApply ("HPost" with "[Hκb HB]"). by iApply "Hκb". iNext. rewrite - deep_handler_ls_unfold. iApply "IH". }
        iIntros "!# % [$ _] //".
      + iIntros "!# % [$ HΓ₃] !>". do 2 rewrite - env_sem_typed_insert //. 
  Qed.

  Lemma sem_typed_deep_try_2_os m l1 l2 A1 B1 A2 B2 τ τ' ρ' ρ'' Γ₁ Γ₂ Γ₃ Γ' x k e h1 h2 r `{NonExpansive A1, NonExpansive B1, NonExpansive A2, NonExpansive B2}:
    x ∉ env_dom Γ₂ → x ∉ env_dom Γ' → x ∉ env_dom Γ₃ → k ∉ env_dom Γ₃ → k ∉ env_dom Γ' → x ≠ k → l1 ≠ l2 →
    let σ1 := (∀S: α, A1 α ⇒ B1 α | m)%S in
    let σ2 := (∀S: α, A2 α ⇒ B2 α | m)%S in
    let ρ := ((l1, σ1) ·: (l2, σ2) ·: ρ')%R in
    copy_env Γ' -∗
    ρ' ≤R ρ'' -∗
    Γ₁ ⊨ e : ρ : τ ⊨ Γ₂ -∗
    (∀ α, (x, A1 α) :: (k, B1 α -{ ρ'' }-∘ τ') :: Γ' ⊨ h1 : ρ'' : τ' ⊨ Γ₃) -∗
    (∀ α, (x, A2 α) :: (k, B2 α -{ ρ'' }-∘ τ') :: Γ' ⊨ h2 : ρ'' : τ' ⊨ Γ₃) -∗
    (x, τ) :: Γ₂ ++ Γ' ⊨ r : ρ'' : τ' ⊨ Γ₃ -∗
    Γ₁ ++ Γ' ⊨ (deep-try-ls2: e with
                        effect l1 => (λ: x k, h1)
                      | effect l2 => (λ: x k, h2)
                      | return  (λ: x, r) end)%E : ρ'' : τ' ⊨ Γ₃.
  Proof.
    iIntros (??????????) "#Hcpy #Hle #He #Hh1 #Hh2 #Hr !# %vs HΓ₁Γ' /=".
    iDestruct (env_sem_typed_app with "HΓ₁Γ'") as "[HΓ₁ HΓ'']". 
    iDestruct ("Hcpy" with "HΓ''") as "#HΓ'".
    ewpw_pure_steps. iApply (ewpw_deep_try_ls_2 _ _ _ MS with "[HΓ₁] [HΓ']").
    { iApply ("He" with "HΓ₁"). }
    iLöb as "IH".
    rewrite deep_handler_ls_2_unfold.
    repeat iSplit; eauto; simpl; iIntros "!#"; last iSplit.
    - iIntros (v) "[Hτ HΓ₂]". ewpw_pure_steps. rewrite - subst_map_insert. 
      iApply (ewpw_mono with "[HΓ₂ HΓ' Hτ]").
      { iApply "Hr". solve_env. iApply env_sem_typed_app; solve_env. }
      iIntros "!# %w [$ HΓ₃] !>". solve_env.
    - iIntros (v k') "(%Φ & Hρ & HPost)".
      rewrite sem_sig_eff_eq. iDestruct "Hρ" as "(%α & %a & <- & Ha & Hκb)". 
      ewpw_pure_steps. solve_dec.
      rewrite subst_subst_ne // - subst_map_insert - delete_insert_ne // - subst_map_insert.
      iApply (ewpw_mono with "[HΓ' Ha Hκb HPost]").
      + iApply "Hh1". solve_env. do 2 rewrite - env_sem_typed_insert //. iFrame "#".
        iIntros (?) "HB". 
        rewrite !bi.intuitionistically_if_elim. 
        iApply (ewpw_mono with "[Hκb HPost HB]").
        { iApply ("HPost" with "[Hκb HB]"). by iApply "Hκb". iNext. rewrite - deep_handler_ls_2_unfold. iApply "IH". }
        iIntros "!# % [$ _] //".
      + iIntros "!# % [$ HΓ₃] !>". do 2 rewrite - env_sem_typed_insert //. 
    - iIntros (v k') "(%Φ & Hρ & HPost)".
      rewrite sem_sig_eff_eq. iDestruct "Hρ" as "(%α & %a & <- & Ha & Hκb)". 
      ewpw_pure_steps. solve_dec.
      rewrite subst_subst_ne // - subst_map_insert - delete_insert_ne // - subst_map_insert.
      iApply (ewpw_mono with "[HΓ' Ha Hκb HPost]").
      + iApply "Hh2". solve_env. do 2 rewrite - env_sem_typed_insert //. iFrame "#".
        iIntros (?) "HB". 
        rewrite !bi.intuitionistically_if_elim. 
        iApply (ewpw_mono with "[Hκb HPost HB]").
        { iApply ("HPost" with "[Hκb HB]"). by iApply "Hκb". iNext. rewrite - deep_handler_ls_2_unfold. iApply "IH". }
        iIntros "!# % [$ _] //".
      + iIntros "!# % [$ HΓ₃] !>". do 2 rewrite - env_sem_typed_insert //. 
  Qed.

  Lemma sem_typed_deep_try_2_ms l1 l2 A1 B1 A2 B2 τ τ' ρ' ρ'' Γ₁ Γ₂ Γ₃ Γ' x k e h1 h2 r `{NonExpansive A1, NonExpansive B1, NonExpansive A2, NonExpansive B2}:
    x ∉ env_dom Γ₂ → x ∉ env_dom Γ' → x ∉ env_dom Γ₃ → k ∉ env_dom Γ₃ → k ∉ env_dom Γ' → x ≠ k → l1 ≠ l2 →
    let σ1 := (∀S: α, A1 α ⇒ B1 α | MS)%S in
    let σ2 := (∀S: α, A2 α ⇒ B2 α | MS)%S in
    let ρ := ((l1, σ1) ·: (l2, σ2) ·: ρ')%R in
    copy_env Γ' -∗
    ρ' ≤R ρ'' -∗
    Γ₁ ⊨ e : ρ : τ ⊨ Γ₂ -∗
    (∀ α, (x, A1 α) :: (k, B1 α -{ ρ'' }-> τ') :: Γ' ⊨ h1 : ρ'' : τ' ⊨ Γ₃) -∗
    (∀ α, (x, A2 α) :: (k, B2 α -{ ρ'' }-> τ') :: Γ' ⊨ h2 : ρ'' : τ' ⊨ Γ₃) -∗
    (x, τ) :: Γ₂ ++ Γ' ⊨ r : ρ'' : τ' ⊨ Γ₃ -∗
    Γ₁ ++ Γ' ⊨ (deep-try-ls2: e with
                        effect l1 => (λ: x k, h1)
                      | effect l2 => (λ: x k, h2)
                      | return  (λ: x, r) end)%E : ρ'' : τ' ⊨ Γ₃.
  Proof.
    iIntros (??????????) "#Hcpy #Hle #He #Hh1 #Hh2 #Hr !# %vs HΓ₁Γ' /=".
    iDestruct (env_sem_typed_app with "HΓ₁Γ'") as "[HΓ₁ HΓ'']". 
    iDestruct ("Hcpy" with "HΓ''") as "#HΓ'".
    ewpw_pure_steps. iApply (ewpw_deep_try_ls_2 _ _ _ MS with "[HΓ₁] [HΓ']").
    { iApply ("He" with "HΓ₁"). }
    iLöb as "IH".
    rewrite deep_handler_ls_2_unfold.
    repeat iSplit; eauto; simpl; iIntros "!#"; last iSplit.
    - iIntros (v) "[Hτ HΓ₂]". ewpw_pure_steps. rewrite - subst_map_insert. 
      iApply (ewpw_mono with "[HΓ₂ HΓ' Hτ]").
      { iApply "Hr". solve_env. iApply env_sem_typed_app; solve_env. }
      iIntros "!# %w [$ HΓ₃] !>". solve_env.
    - iIntros (v k') "(%Φ & Hρ & HPost)".
      rewrite sem_sig_eff_eq. iDestruct "Hρ" as "(%α & %a & <- & Ha & Hκb)". 
      ewpw_pure_steps. solve_dec.
      rewrite subst_subst_ne // - subst_map_insert - delete_insert_ne // - subst_map_insert.
      iApply (ewpw_mono with "[HΓ' Ha Hκb HPost]").
      + iApply "Hh1". solve_env; last do 2 rewrite - env_sem_typed_insert //. 
        iDestruct "Hκb" as "#Hκb". iDestruct "HPost" as "#HPost".
        iIntros (?) "!# HB". 
        iApply (ewpw_mono with "[Hκb HPost HB]").
        { iApply ("HPost" with "[Hκb HB]"). 
          by iApply "Hκb". iNext. rewrite - deep_handler_ls_2_unfold. iApply "IH". }
        iIntros "!# % [$ _] //".
      + iIntros "!# % [$ HΓ₃] !>". do 2 rewrite - env_sem_typed_insert //. 
    - iIntros (v k') "(%Φ & Hρ & HPost)".
      rewrite sem_sig_eff_eq. iDestruct "Hρ" as "(%α & %a & <- & Ha & Hκb)". 
      ewpw_pure_steps. solve_dec.
      rewrite subst_subst_ne // - subst_map_insert - delete_insert_ne // - subst_map_insert.
      iApply (ewpw_mono with "[HΓ' Ha Hκb HPost]").
      + iApply "Hh2". solve_env; last do 2 rewrite - env_sem_typed_insert //. 
        iDestruct "Hκb" as "#Hκb". iDestruct "HPost" as "#HPost".
        iIntros (?) "!# HB". 
        iApply (ewpw_mono with "[Hκb HPost HB]").
        { iApply ("HPost" with "[Hκb HB]"). 
          by iApply "Hκb". iNext. rewrite - deep_handler_ls_2_unfold. iApply "IH". }
        iIntros "!# % [$ _] //".
      + iIntros "!# % [$ HΓ₃] !>". do 2 rewrite - env_sem_typed_insert //. 
  Qed.

End compatibility.
