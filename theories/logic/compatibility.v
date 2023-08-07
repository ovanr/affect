
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
From affine_tes.lang Require Import hazel.
From affine_tes.logic Require Import iEff.
From affine_tes.logic Require Import sem_types.
From affine_tes.logic Require Import sem_typed.
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
  
  (* λ-calculus rules *)

  Lemma sem_typed_afun Γ₁ Γ₂ x e τ ρ κ: 
    x ∉ (env_dom Γ₁) →
    x ∉ (env_dom Γ₂) →
    (x,τ) :: Γ₁ ⊨ e : ρ : κ ⊨ [] -∗
    Γ₁ ++ Γ₂ ⊨ (λ: x, e) : ⟨⟩ : (τ -{ ρ }-∘ κ) ⊨ Γ₂.
  Proof.
    iIntros (??) "#He !# %Φ %vs HΓ₁₂ HΦ //=".
    ewp_pure_steps. 
    rewrite env_sem_typed_app. iApply "HΦ". 
    iDestruct "HΓ₁₂" as "[HΓ₁ $]".
    iIntros (Φ' w) "Hτ HΦ'". ewp_pure_steps.
    rewrite -subst_map_insert. 
    iApply ("He" with "[HΓ₁ Hτ] [HΦ']").
    - iSplitL "Hτ". 
      { iExists w. iIntros "{$Hτ} !%". apply lookup_insert. }
      by iApply env_sem_typed_insert.
    - iIntros (v) "//= [Hκ _]". by iApply "HΦ'". 
  Qed.
  
  Lemma sem_typed_ufun Γ₁ Γ₂ f x e τ ρ κ: 
    x ∉ (env_dom Γ₁) →
    f ∉ (env_dom Γ₁) →
    x ≠ f →
    copy_env Γ₁ →
    (x,τ) :: (f, τ -{ ρ }-> κ) :: Γ₁ ⊨ e : ρ : κ ⊨ [] -∗
    Γ₁ ++ Γ₂ ⊨ (rec: f x := e) : ⟨⟩ : (τ -{ ρ }-> κ) ⊨ Γ₂.
  Proof.
    iIntros (??? HcpyΓ₁) "#He !# %Φ %vs HΓ₁₂ HΦ //=".
    ewp_pure_steps.
    rewrite env_sem_typed_app. iApply "HΦ". 
    iDestruct "HΓ₁₂" as "[HΓ₁ $]".
    rewrite HcpyΓ₁. iDestruct "HΓ₁" as "#HΓ₁".
    iLöb as "IH".
    iIntros (Φ' w) "!# Hw HΦ'". ewp_pure_steps. 
    rewrite subst_subst_ne; last done.
    rewrite -subst_map_insert.
    rewrite -delete_insert_ne; last done. 
    rewrite -subst_map_insert.
    iApply ("He" with "[Hw] [HΦ']").
    - iSplitL "Hw"; last iSplitR "HΓ₁".
      + iExists w. iFrame. iPureIntro.
        rewrite lookup_insert_ne; last done.
        by rewrite lookup_insert.
      + iExists _. iSplit; [by rewrite lookup_insert|]. 
        iApply "IH".
      + by do 2 (iApply env_sem_typed_insert; first done).
    - iIntros (v) "[Hκ _]". by iApply "HΦ'". 
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
    iApply ("Hτκw" with "Hτ"). 
    iIntros (u) "Hκ". iApply "HΦ". iFrame.
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
    rewrite <- subst_map_insert.
    iApply ("He₂" with "[Hτ Hκ HΓ₂]").
    - iSplitL "Hτ".
      { iExists v₁. iFrame. iPureIntro. 
        rewrite lookup_insert_ne; last done.
        by rewrite lookup_insert. }
      iSplitL "Hκ".
      { iExists v₂. iFrame. iPureIntro. 
        by rewrite lookup_insert. }
      by repeat (iApply env_sem_typed_insert; first done).
    - iIntros (v) "[Hιv HΓ₃]". iApply "HΦ". iFrame.
      iApply (env_sem_typed_delete _ _ x₁ v₁); first done.
      iApply (env_sem_typed_delete _ _ x₂ v₂); done.
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

  Lemma sem_typed_case Γ₁ Γ₂ Γ₃ e₁ e₂ e₃ τ ρ κ ι: 
    Γ₁ ⊨ e₁ : ρ : (τ + κ) ⊨ Γ₂ -∗
    Γ₂ ⊨ e₂ : ⟨⟩ : (τ -{ ρ }-∘ ι) ⊨ Γ₃ -∗
    Γ₂ ⊨ e₃ : ⟨⟩ : (κ -{ ρ }-∘ ι) ⊨ Γ₃ -∗
    Γ₁ ⊨ Case e₁ e₂ e₃ : ρ : ι ⊨ Γ₃.
  Proof.
    iIntros "#He₁ #He₂ #He₃ !# %Φ %vs HΓ₁ HΦ //=".
    iApply (ewp_bind [CaseCtx _ _]); first done.
    iApply ("He₁" with "HΓ₁").
    iIntros (v) "[(%w & [(-> & Hτ)|(-> & Hκ)]) HΓ₂] //="; 
      ewp_pure_steps;
      iApply (ewp_bind [AppLCtx _]); try done; 
      ewp_bottom.
    - iApply ("He₂" with "HΓ₂ [Hτ HΦ]").
      iIntros (v) "[Hτι HΓ₃] //=".
      iApply ("Hτι" with "Hτ"). 
      iIntros (u) "Hι". iApply "HΦ". iFrame.
    - iApply ("He₃" with "HΓ₂ [Hκ HΦ]").
      iIntros (v) "[Hκι HΓ₃] //=".
      iApply ("Hκι" with "Hκ"). 
      iIntros (u) "Hκ". iApply "HΦ". iFrame.
  Qed.

  Lemma sem_typed_un_op Γ₁ Γ₂ e op τ κ ρ: 
    typed_un_op op τ κ →
    Γ₁ ⊨ e : ρ : τ ⊨ Γ₂-∗
    Γ₁ ⊨ UnOp op e : ρ : κ ⊨ Γ₂.
  Proof.
    iIntros (Hop) "#He !# %Φ %vs HΓ₁ HΦ //=".
    iApply (ewp_bind [UnOpCtx _]); first done.
    iApply ("He" with "HΓ₁").
    iIntros (v) "[Hv HΓ₂] //=".
    destruct op; inversion_clear Hop;
    iDestruct "Hv" as "(%n & ->)"; ewp_pure_steps; try done;
    iApply "HΦ"; eauto.
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
    (∀ A, Γ₁ ⊨ e : ρ : C A ⊨ []) -∗
    Γ₁ ++ Γ₂ ⊨ (Λ: e) : ⟨⟩ : (∀: A , ρ , C A)%T ⊨ Γ₂.
  Proof.
    iIntros "#He !# %Φ %vs HΓ₁₂ HΦ //=".
    rewrite env_sem_typed_app.
    iDestruct "HΓ₁₂" as "[HΓ₁ HΓ₂]".
    ewp_pure_steps. iApply "HΦ". 
    iIntros "{$HΓ₂} %A //=". ewp_pure_steps.
    iApply ("He" with "HΓ₁ []"). 
    iIntros (w) "[HC _] {$HC}".
  Qed.

  Lemma sem_typed_TApp Γ₁ Γ₂ e ρ τ C : 
    Γ₁ ⊨ e : ρ : (∀: α , ρ , C α) ⊨ Γ₂ -∗
    Γ₁ ⊨ e <_> : ρ : C τ ⊨ Γ₂. 
  Proof.
    iIntros "#He !# %Φ %vs HΓ₁ HΦ //=".
    iApply (ewp_bind [AppLCtx _]); first done.
    iApply ("He" with "HΓ₁").
    iIntros "%w [Hw HΓ₂] //=".
    iApply (ewp_mono with "[Hw]").
    { iApply "Hw". }
    iIntros (u) "HC !>". iApply "HΦ". iFrame.
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
    iApply ("He₂" with "[HΓ₂ Hτw]").
    - simpl. iSplitL "Hτw".
      { iExists w. iFrame. iPureIntro. by rewrite lookup_insert. }
      by iApply env_sem_typed_insert.
    - iIntros (u) "[Hκ HΓ₃]". iApply "HΦ". iFrame.
      by iApply env_sem_typed_delete.
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
  
  Lemma sem_typed_list_match Γ₁ Γ₂ Γ₃ x xs e₁ e₂ e₃ ρ τ κ :
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
    iApply ("He₃" with "[Hμ Hτ HΓ₂]").
    - iSplitL "Hτ".
      { iExists w₁. iFrame. by rewrite lookup_insert. }
      iSplitL "Hμ".
      + iExists w₂. unfold sem_ty_list. iSplitR; [|done].
        rewrite lookup_insert_ne; [|congruence].  
        by rewrite lookup_insert. 
      + iApply env_sem_typed_insert; first done.
        by iApply env_sem_typed_insert; first done.
    - iIntros (u) "[Hκ HΓ₃]". iApply "HΦ". iFrame.
      iApply (env_sem_typed_delete _ _ xs w₂); first done.
      iApply (env_sem_typed_delete _ _ x w₁); done.
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
    iApply ewp_alloc. iIntros "!> %l Hl !>". iApply "HΦ". iFrame.
    iExists l. iSplit; first done. iExists v. iFrame.
  Qed.
  
  Lemma sem_typed_load Γ x ρ τ: 
    ⊢ ((x, Ref τ) :: Γ ⊨ !x : ρ : τ ⊨ (x, Ref Moved) :: Γ).
  Proof.
    iIntros "%Φ %vs !# //= [(%v & -> & (%l & -> & (%w & Hl & Hτ))) HΓ] HΦ //=". 
    iApply (ewp_load with "Hl").
    iIntros "!> Hl !>". iApply "HΦ". iFrame. iExists #l.
    iSplitR; first done. iExists l. iSplitR; first done.
    iExists w. iFrame.
  Qed.
  
  Lemma sem_typed_load_copy Γ x ρ τ: 
    copy_ty τ →
    ⊢ ((x, Ref τ) :: Γ ⊨ !x : ρ : τ ⊨ (x, Ref τ) :: Γ).
  Proof.
    iIntros (Hcpy) "%Φ %vs !# //= [(%v & -> & (%l & -> & (%w & Hl & Hτ))) HΓ] HΦ //=". 
    iApply (ewp_load with "Hl").
    rewrite Hcpy. iDestruct "Hτ" as "#Hτ".
    iIntros "!> Hl !>". iApply "HΦ". iIntros "{$Hτ $HΓ}". iExists #l.
    iSplitR; first done. iExists l. iSplitR; first done.
    iExists w. iIntros "{$Hτ $Hl}".
  Qed.

  Lemma sem_typed_store Γ₁ Γ₂ x e ρ τ κ: 
    Γ₁ ⊨ e : ρ : κ ⊨ Γ₂ -∗
    (x, Ref τ) :: Γ₁ ⊨ (x <- e) : ρ : () ⊨ (x, Ref κ) :: Γ₂.
  Proof.
    iIntros "#He !# %Φ %vs //= [(%v & -> & (%l & -> & (%u & Hl & Hτ))) HΓ₁] HΦ //=".
    iApply (ewp_bind [StoreRCtx _]); first done. simpl.
    iApply ("He" with "HΓ₁").
    iIntros (w) "[Hκ HΓ₂]". 
    iApply (ewp_store with "Hl"). iIntros "!> Hl !>". iApply "HΦ". 
    iFrame. iSplitR; first done. iExists #l. iSplitR; first done.
    iExists l. iSplitR; first done. iExists w. iFrame.
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
    iApply ewp_do_os. rewrite upcl_sem_row_eff.
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
  Lemma sem_typed_shallow_try Γ₁ Γ₂ Γ₃ Γ' w k x e h r ι κ τ τ': 
    x ∉ env_dom Γ₂ → x ∉ env_dom Γ' → x ∉ env_dom Γ₃ →
    w ∉ env_dom Γ' → k ∉ env_dom Γ' →
    w ∉ env_dom Γ₃ → k ∉ env_dom Γ₃ → w ≠ k →
    let ρ := (ι ⇒ κ)%R in
    Γ₁ ⊨ e : ρ : τ' ⊨ Γ₂ -∗
    (w, ι) :: (k, κ -{ ρ }-∘ τ') :: Γ' ⊨ h w k : ρ : τ ⊨ Γ₃ -∗
    (x, τ') :: Γ₂ ++ Γ' ⊨ r x : ρ : τ ⊨ Γ₃ -∗
    Γ₁ ++ Γ' ⊨ (TryWith e (λ: w k, h w k) (λ: x, r x)) : (ι ⇒ κ) : τ ⊨ Γ₃.
  Proof.
    iIntros (????????) "%ρ #He #Hh #Hr !# %Φ %vs HΓ₁' HΦ //=".
    rewrite env_sem_typed_app. iDestruct "HΓ₁'" as "[HΓ₁ HΓ']".
    ewp_pure_steps.
    iApply (ewp_try_with _ _ _ (λ v, τ' v ∗ env_sem_typed Γ₂ vs) 
                    with "[HΓ₁] [HΓ' HΦ]"). 
    { iApply ("He" with "HΓ₁"). iIntros "* [Hτ' HΓ₂] {$Hτ' $HΓ₂}". }
    iSplit; [|iSplit; iIntros (v c)];
    last (iIntros "?"; by rewrite upcl_bottom).
    - iIntros (v) "[Hv HΓ₂] //=". ewp_pure_steps.
      rewrite -subst_map_insert.
      iApply ("Hr" with "[HΓ₂ HΓ' Hv]").
      + simpl. iSplitL "Hv".
        { iExists v. iIntros "{$Hv} !%". apply lookup_insert. }
        rewrite env_sem_typed_app. iFrame.
        iSplitL "HΓ₂"; by iApply env_sem_typed_insert.
      + iIntros (u) "[Hw HΓ₃] //=".
        iApply "HΦ". iFrame. by iApply (env_sem_typed_delete _ _ x v).
    - rewrite upcl_sem_row_eff.
      iIntros "(%a & -> & Ha & Hκb) //=". ewp_pure_steps.
      rewrite decide_True; [|split; first done; by injection].
      rewrite subst_subst_ne; last done.
      rewrite -subst_map_insert -delete_insert_ne; last done.
      rewrite -subst_map_insert.
      iApply ("Hh" with "[HΓ' Hκb Ha]").
      + simpl. iSplitL "Ha".
        { iExists a. iIntros "{$Ha} !%". apply lookup_insert. }
        iSplitL "Hκb".
        2: { do 2 (iApply env_sem_typed_insert; try done). }
        iExists c. iSplitR.
        { iPureIntro; rewrite lookup_insert_ne; last done; apply lookup_insert. }
        iIntros (Φ' b) "Hb HΦ'". 
        iApply (ewp_mono with "[Hb Hκb]"); [by iApply "Hκb"|].
        iIntros (?) "[? _] !> //=". by iApply "HΦ'".
      + iIntros (u) "[Hu HΓ₃]". iApply "HΦ". iFrame.
        iApply (env_sem_typed_delete _ _ k c); first done.
        by iApply (env_sem_typed_delete _ _ w a).
  Qed.
  
  Lemma sem_typed_deep_try Γ₁ Γ' Γ₂ Γ₃ e x w k h r ρ' ι κ τ τ':
    x ∉ env_dom Γ₂ → x ∉ env_dom Γ' → x ∉ env_dom Γ₃ →
    w ∉ env_dom Γ' → w ∉ env_dom Γ₃ →
    k ∉ env_dom Γ' → k ∉ env_dom Γ₃ → w ≠ k → copy_env Γ' →
    let ρ := (ι ⇒ κ)%R in
    Γ₁ ⊨ e : ρ : τ ⊨ Γ₂ -∗
    (w, ι) :: (k, κ -{ ρ' }-∘ τ') :: Γ' ⊨ h w k : ρ' : τ' ⊨ Γ₃ -∗
    (x, τ) :: Γ₂ ++ Γ' ⊨ r x : ρ' : τ' ⊨ Γ₃ -∗
    Γ₁ ++ Γ' ⊨ (deep-try: e with effect (λ: w k, h w k) | return (λ: x, r x) end) : ρ' : τ' ⊨ Γ₃.
  Proof.
    iIntros (???????? Hcpy) "%ρ #He #Hh #Hr !# %Φ %vs HΓ₁' HΦ //=".
    rewrite env_sem_typed_app. iDestruct "HΓ₁'" as "[HΓ₁ HΓ']".
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
      + simpl. iSplitL "Hv".
        iExists v. iIntros "{$Hv} !%". apply lookup_insert.
        rewrite env_sem_typed_app. iSplitL "HΓ₂";
        by iApply env_sem_typed_insert.
      + iIntros (?) "[Hτ' HΓ₃] {$Hτ'}".
        by iApply (env_sem_typed_delete _ _ x v).
    - rewrite upcl_sem_row_eff.
      iIntros "(%a & -> & Ha & Hκb)". ewp_pure_steps.
      rewrite decide_True; [|split; first done; by injection].
      rewrite subst_subst_ne; last done.
      rewrite -subst_map_insert -delete_insert_ne; last done.
      rewrite -subst_map_insert.
      iApply ("Hh" with "[Ha HΓ' Hκb]").
      + simpl. iSplitL "Ha".
        { iExists a; iIntros "{$Ha} !%"; apply lookup_insert. }
        iSplitL "Hκb".
        2: { do 2 (iApply env_sem_typed_insert; try done). }
        iExists c. iSplitR.
        { iPureIntro; rewrite lookup_insert_ne; last done; apply lookup_insert. }
        iIntros (Φ' b) "Hb HΦ'". iApply (ewp_mono with "[Hb Hκb] [HΦ']").
        { iApply ("Hκb" with "Hb []"). rewrite !deep_handler_unfold. iApply "IH". }
          iIntros "* [Hτ' HΓ₃] !>". by iApply "HΦ'".
      + iIntros (u) "[Hτ' HΓ₃] {$Hτ'}".
        iApply (env_sem_typed_delete _ _ k c); first done.
        by iApply (env_sem_typed_delete _ _ w a).
    Qed.

End compatibility.
