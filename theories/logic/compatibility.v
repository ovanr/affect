
(* compatibility.v *)

(* 
  The compatibility lemmas are what one gets when the syntactic typing judgment
  is replaced witha a semantic typing judgment.
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
    ⊢ Γ ⊨ #() : ⟨⟩ : ().
  Proof.
    iIntros (vs) "!# HΓ //=". by iApply ewp_value.
  Qed.
  
  Lemma sem_typed_bool Γ (b : bool) : 
    ⊢ Γ ⊨ #b : ⟨⟩ : 𝔹.
  Proof.
    iIntros (vs) "!# HΓ //=". iApply ewp_value. by iExists b.
  Qed.
  
  Lemma sem_typed_int Γ (i : Z) : 
    ⊢ Γ ⊨ #i : ⟨⟩ : ℤ.
  Proof.
    iIntros (vs) "!# HΓ //=". iApply ewp_value. by iExists i.
  Qed.
  
  (* Subsumption rule *)
  
  Lemma sem_typed_sub Γ Γ' e ρ ρ' τ τ':
    Γ ≤E Γ' →
    ρ'  ≤R ρ → 
    τ'  ≤T τ →
    Γ' ⊨ e : ρ' : τ' -∗ Γ ⊨ e : ρ : τ.
  Proof.
    iIntros (HΓle Hρle Hτle) "#He !# %vs HΓ //=".
    rewrite HΓle.
    iApply ewp_os_prot_mono.
    { iApply Hρle. }
    iApply (ewp_mono with "[HΓ He]").
    { by iApply "He". }
    iIntros (v) "Hτ'". iModIntro.
    by iApply Hτle.
  Qed.
  
  (* λ-calculus rules *)
  
  Lemma sem_typed_lfun Γ x e τ ρ κ: 
    x ∉ (env_dom Γ) →
    (x,τ) :: Γ ⊨ e : ρ : κ -∗
    Γ ⊨ (λ: x, e) : ⟨⟩ : (τ -{ ρ }-∘ κ).
  Proof.
    iIntros (Helem) "#He !# %vs HΓ //=".
    ewp_pure_steps. iIntros (w) "Hw". ewp_pure_steps. 
    rewrite <- subst_map_insert.
    iApply "He". simpl in *. iSplitL "Hw".
    - iExists w. iFrame. iPureIntro.
      by rewrite lookup_insert.
    - by iApply env_sem_typed_insert.
  Qed.
  
  Lemma sem_typed_ufun Γ x e τ ρ κ: 
    x ∉ (env_dom Γ) →
    copy_env Γ →
    (x,τ) :: Γ ⊨ e : ρ : κ -∗
    Γ ⊨ (λ: x, e) : ⟨⟩ : (τ -{ ρ }-> κ).
  Proof.
    iIntros (Helem HcpyΓ) "#He !# %vs HΓ //=".
    ewp_pure_steps. rewrite HcpyΓ. iDestruct "HΓ" as "#HΓ".
    iIntros (w) "!# Hw". ewp_pure_steps. 
    rewrite <- subst_map_insert.
    iApply "He". simpl in *. iSplitL "Hw".
    - iExists w. iFrame. iPureIntro.
      by rewrite lookup_insert.
    - by iApply env_sem_typed_insert.
  Qed.
  
  Lemma sem_typed_app Γ₁ Γ₂ e₁ e₂ τ ρ κ: 
    Γ₁ ⊨ e₁ : ρ : (τ -{ ρ }-∘ κ) -∗
    Γ₂ ⊨ e₂ : ρ : τ -∗
    Γ₁ ++ Γ₂ ⊨ (e₁ e₂) : ρ : κ.
  Proof.
    iIntros "#He₁ #He₂ !# %vs HΓ₁₂ //=".
    rewrite env_sem_typed_app.
    iDestruct "HΓ₁₂" as "[HΓ₁ HΓ₂]".
    iApply (ewp_bind ([AppRCtx (subst_map vs e₁)])); first done.
    iApply (ewp_mono with "[HΓ₂]").
    { by iApply "He₂". }
    iIntros (v) "Hτv //=". iModIntro.
    iApply (ewp_bind ([AppLCtx v])); first done.
    iApply (ewp_mono with "[HΓ₁]").
    { by iApply "He₁". }
    iIntros (w) "Hτκw //=". iModIntro; by iApply "Hτκw". 
  Qed.
  
  Lemma sem_typed_pair Γ₁ Γ₂ e₁ e₂ τ ρ κ: 
    Γ₁ ⊨ e₁ : ρ : τ -∗
    Γ₂ ⊨ e₂ : ρ : κ -∗
    Γ₁ ++ Γ₂ ⊨ (e₁,e₂) : ρ : (τ × κ).
  Proof.
    iIntros "#He₁ #He₂ !# %vs HΓ₁₂ //=".
    rewrite env_sem_typed_app.
    iDestruct "HΓ₁₂" as "[HΓ₁ HΓ₂]".
    iApply (ewp_bind ([PairRCtx (subst_map vs e₁)])); first done.
    iApply (ewp_mono with "[HΓ₂]").
    { by iApply "He₂". }
    iIntros (v) "Hτv //=". iModIntro.
    iApply (ewp_bind ([PairLCtx v])); first done.
    iApply (ewp_mono with "[HΓ₁]").
    { by iApply "He₁". }
    iIntros (w) "Hκw //=". iModIntro. ewp_pure_steps.
    iExists w, v. iFrame. by iPureIntro.
  Qed.
  
  Lemma sem_typed_pair_elim Γ₁ Γ₂ x₁ x₂ e₁ e₂ τ ρ κ ι: 
    x₁ ∉ (env_dom Γ₂) ->
    x₂ ∉ (env_dom Γ₂) ->
    x₁ ≠ x₂ ->
    Γ₁ ⊨ e₁ : ρ : (τ × κ) -∗
    (x₁, τ) :: (x₂, κ) :: Γ₂ ⊨ e₂ : ρ : ι -∗
    Γ₁ ++ Γ₂ ⊨ (let: (x₁, x₂) := e₁ in e₂) : ρ : ι.
  Proof.
    iIntros (Helem₁ Helem₂ Hnex₁₂) "#He₁ #He₂ !# %vs HΓ₁₂ //=".
    rewrite env_sem_typed_app.
    iDestruct "HΓ₁₂" as "[HΓ₁ HΓ₂]".
    ewp_pure_steps.
    set ex1x2 := (λ: x₁ x₂, subst_map (binder_delete x₂ 
                                      (binder_delete x₁ vs)) e₂)%V. 
    iApply (ewp_bind ([AppLCtx ex1x2; AppRCtx pair_elim])); first done.
    iApply (ewp_mono with "[HΓ₁]").
    { by iApply "He₁". }
    iIntros (v) "Hτκv". iModIntro. simpl in *. 
    unfold pair_elim. ewp_pure_steps.
    iDestruct "Hτκv" as "(%v₁ & %v₂ & -> & Hτ & Hκ)".
    unfold ex1x2. ewp_pure_steps. 
    destruct (decide _) as [[]|[]]; [|split; [done|congruence]].
    rewrite delete_commute -subst_map_insert -delete_insert_ne
      ;last congruence.
    rewrite <- subst_map_insert.
    iApply "He₂". simpl. iSplitL "Hτ".
    { iExists v₁. iFrame. iPureIntro. 
      rewrite lookup_insert_ne; last done.
      by rewrite lookup_insert. }
    iSplitL "Hκ".
    { iExists v₂. iFrame. iPureIntro. 
      by rewrite lookup_insert. }
    by repeat (iApply env_sem_typed_insert; first done).
  Qed.
  
  Lemma sem_typed_un_op Γ e op τ κ ρ: 
    typed_un_op op τ κ →
    Γ ⊨ e : ρ : τ -∗
    Γ ⊨ UnOp op e : ρ : κ.
  Proof.
    iIntros (Hop) "#He !# %vs HΓ //=".
    iApply (ewp_bind [UnOpCtx _]); first done.
    iApply (ewp_mono with "[HΓ]").
    { by iApply "He". }
    iIntros (v) "Hv !> //=".
    destruct op; inversion_clear Hop;
    iDestruct "Hv" as "(%n & ->)";
    ewp_pure_steps; eauto.
  Qed.
  
  Lemma sem_typed_bin_op Γ₁ Γ₂ e₁ e₂ op τ κ ι ρ: 
    typed_bin_op op τ κ ι →
    Γ₁ ⊨ e₁ : ρ : τ -∗
    Γ₂ ⊨ e₂ : ρ : κ -∗
    Γ₁ ++ Γ₂ ⊨ BinOp op e₁ e₂ : ρ : ι.
  Proof.
    iIntros (Hop) "#He₁ #He₂ !# %vs HΓ₁₂ //=".
    rewrite env_sem_typed_app.
    iDestruct "HΓ₁₂" as "[HΓ₁ HΓ₂]".
    iApply (ewp_bind [BinOpRCtx _ _]); first done.
    iApply (ewp_mono with "[HΓ₂]").
    { by iApply "He₂". }
    iIntros (v) "Hv !> //=". 
    iApply (ewp_bind [BinOpLCtx _ _]); first done.
    iApply (ewp_mono with "[HΓ₁]").
    { by iApply "He₁". }
    iIntros (w) "Hw !> //=". 
    destruct op; inversion_clear Hop;
      iDestruct "Hv" as "(%n1 & ->)";
      iDestruct "Hw" as "(%n2 & ->)";
      ewp_pure_steps; eauto.
  Qed.
  
  Lemma sem_typed_if Γ₁ Γ₂ e₁ e₂ e₃ ρ τ: 
    Γ₁ ⊨ e₁ : ρ : 𝔹 -∗
    Γ₂ ⊨ e₂ : ρ : τ -∗
    Γ₂ ⊨ e₃ : ρ : τ -∗
    Γ₁ ++ Γ₂ ⊨ (if: e₁ then e₂ else e₃) : ρ : τ.
  Proof.
    iIntros "#He₁ #He₂ #He₃ !# %vs HΓ₁₂ //=".
    rewrite env_sem_typed_app.
    iDestruct "HΓ₁₂" as "[HΓ₁ HΓ₂]".
    iApply (ewp_bind [IfCtx (subst_map vs e₂) (subst_map vs e₃)])
      ;first done.
    iApply (ewp_mono with "[HΓ₁]").
    { by iApply "He₁". }
    iIntros (v) "(%b & ->)". iModIntro. simpl.
    destruct b; ewp_pure_steps.
    - by iApply "He₂".
    - by iApply "He₃".
  Qed.
  
  (* Type abstraction and application *)
  Lemma sem_typed_TLam Γ ρ e C : 
    (∀ A, Γ ⊨ e : ρ : C A) -∗
    Γ ⊨ (Λ: e) : ⟨⟩ : (∀: A , ρ , C A)%T.
  Proof.
    iIntros "#Hv !# %vs HΓ //=".
    ewp_pure_steps. iIntros "%A". ewp_pure_steps.
    by iApply "Hv".
  Qed.

  Lemma sem_typed_TApp Γ e ρ τ C : 
    Γ ⊨ e : ρ : (∀: α , ρ , C α) -∗
    Γ ⊨ e <_> : ρ : C τ. 
  Proof.
    iIntros "#Hv !# %vs HΓ //=".
    iApply (ewp_bind [AppLCtx _]); first done.
    iApply (ewp_mono with "[HΓ]").
    { by iApply "Hv". }
    iIntros "%w Hw !> //=".
  Qed.

  (* Existential type packing and unpacking *)
  Lemma sem_typed_pack Γ ρ e C τ :
    Γ ⊨ e : ρ : C τ -∗
    Γ ⊨ (pack: e) : ρ : (∃: α, C α)%T. 
  Proof.
    iIntros "#He %vs !# HΓ //=".
    iApply (ewp_bind [AppRCtx _]); first done.
    iApply (ewp_mono with "[HΓ]"); [by iApply "He"|].
    iIntros (v) "Hτv !> //=".
    unfold exist_pack. ewp_pure_steps.
    by iExists τ. 
  Qed.

  Lemma sem_typed_unpack Γ₁ Γ₂ x ρ e₁ e₂ κ C :
    x ∉ env_dom Γ₂ →
    Γ₁ ⊨ e₁ : ρ : (∃: α, C α) -∗
    (∀ τ, (x, C τ) :: Γ₂ ⊨ e₂ : ρ : κ) -∗
    Γ₁ ++ Γ₂ ⊨ (unpack: x := e₁ in e₂) : ρ : κ.
  Proof.
    iIntros (Hnotin) "#He₁ #He₂ %vs !# HΓ₁₂ //=".
    rewrite env_sem_typed_app.
    iDestruct "HΓ₁₂" as "[HΓ₁ HΓ₂]".
    iApply (ewp_bind [AppRCtx _]); first done.
    iApply (ewp_mono with "[HΓ₁]"); [by iApply "He₁"|].
    iIntros (w) "(%τ & Hτw) !> //=". unfold exist_unpack.
    ewp_pure_steps. rewrite -subst_map_insert.
    iApply "He₂". simpl. iSplitL "Hτw".
    { iExists w. iFrame. iPureIntro. by rewrite lookup_insert. }
    by iApply env_sem_typed_insert.
  Qed.

  Lemma sem_typed_nil Γ τ: 
    ⊢ Γ ⊨ NIL : ⟨⟩ : List τ.
  Proof.
    iIntros "!# %vs HΓ //=". 
    ewp_pure_steps. by iExists [].
  Qed.
  
  Lemma sem_typed_cons Γ₁ Γ₂ e₁ e₂ ρ τ: 
    Γ₁ ⊨ e₁ : ρ : τ -∗
    Γ₂ ⊨ e₂ : ρ : List τ -∗
    Γ₁ ++ Γ₂ ⊨ CONS e₁ e₂ : ρ : List τ.
  Proof.
    iIntros "#He₁ #He₂ !# %vs HΓ₁₂ //=". 
    rewrite env_sem_typed_app.
    iDestruct "HΓ₁₂" as "(HΓ₁ & HΓ₂)".
    iApply (ewp_bind [InjRCtx; PairRCtx _]); first done.
    iApply (ewp_mono with "[HΓ₂]").
    { by iApply "He₂". }
    iIntros (l) "Hl !> //=".
    iApply (ewp_bind [InjRCtx; PairLCtx _]); first done.
    iApply (ewp_mono with "[HΓ₁]"); [by iApply "He₁"|].
    iIntros (x) "Hx !> //=". ewp_pure_steps.
    iDestruct "Hl" as "(%xs & Hxs)".
    iExists (x :: xs). simpl. iExists l. by iFrame.
  Qed.
  
  Lemma sem_typed_list_match Γ₁ Γ₂ x xs e₁ e₂ e₃ ρ τ κ :
    x ∉ (env_dom Γ₂) ->
    xs ∉ (env_dom Γ₂) ->
    x ≠ xs ->
    Γ₁ ⊨ e₁ : ρ : List τ -∗
    Γ₂ ⊨ e₂ : ρ : κ -∗
    ((x, τ) :: (xs, (List τ)%T) :: Γ₂) ⊨ e₃ : ρ : κ -∗
    Γ₁ ++ Γ₂ ⊨ list-match: e₁ with 
                    CONS x => xs => e₃ 
                  | NIL => e₂
                end : ρ : κ.
  Proof.
    iIntros (Hx Hxs Hneq) "#He₁ #He₂ #He₃ !# %vs HΓ₁₂ //=".
    rewrite env_sem_typed_app.
    iDestruct "HΓ₁₂" as "(HΓ₁ & HΓ₂)".
    iApply (ewp_bind [CaseCtx _ _]); first done.
    iApply (ewp_mono with "[HΓ₁]"); [by iApply "He₁"|].
    iIntros (v₁) "(%l & Hl) !> //=". destruct l.
    - iDestruct "Hl" as "->". ewp_pure_steps.
      iApply ("He₂" with "[$HΓ₂]").
    - simpl. iDestruct "Hl" as "(%tl & -> & Hτ & Htl)". 
      ewp_pure_steps. rewrite lookup_delete. simpl.
      rewrite decide_False; [|by intros [_ []]].
      rewrite decide_True; last done. ewp_pure_steps.
      rewrite decide_True; [|split; congruence].
      rewrite delete_commute -subst_map_insert delete_commute.
      rewrite insert_delete_insert. rewrite subst_map_insert.
      rewrite subst_subst_ne; [|congruence]. rewrite delete_commute.
      rewrite -subst_map_insert -delete_insert_ne; try congruence.
      rewrite -subst_map_insert. iApply "He₃". simpl.
      iSplitL "Hτ".
      { iExists v. iFrame. by rewrite lookup_insert. }
      iSplitL "Htl".
      + iExists tl. unfold sem_ty_list. iSplitR.
        { rewrite lookup_insert_ne; [|congruence].  
          by rewrite lookup_insert. }
        by iExists l.
      + iApply env_sem_typed_insert; first done.
        by iApply env_sem_typed_insert; first done.
  Qed.


  (* Reference rules *)
  
  (* The references that we implement here are always copyable, 
     so we have ∀ τ, copy_ty (Ref τ).
     This allows us to treat references in a non sub-structural way.
     Since we do not have `free` in our language
     we do not have use-after-free and double-free problems
     and so making them persistent will be too restrictive.
     This is why the `load` does not return the reference back
     and we can always `load` from the same reference more than once.
  
     The down side of this is that we cannot store
     non-persistent functions like continuations.
  *)
     
  Lemma sem_typed_alloc Γ e ρ τ: 
    copy_ty τ →
    Γ ⊨ e : ρ : τ -∗
    Γ ⊨ ref e : ρ : Ref τ.
  Proof.
    iIntros (Hcpyτ) "#He !# %vs HΓ //=".
    iApply (ewp_bind [AllocCtx]); first done. simpl.
    iApply (ewp_mono with "[HΓ]").
    { by iApply "He". }
    iIntros (v) "Hτ". iModIntro.
    iApply ewp_alloc. iIntros "!> %l Hl".
    iMod (inv_alloc (tyN.@l) _
         (∃ w, l ↦ w ∗ τ w)%I with "[Hl Hτ]") as "#Hinv".
    { iExists v. by iFrame. }
    iModIntro. iExists l. do 2 (iSplit; try done).
    by iApply copy_pers.
  Qed.
  
  Lemma sem_typed_load Γ e ρ τ: 
    Γ ⊨ e : ρ : Ref τ -∗
    Γ ⊨ !e : ρ : τ.
  Proof.
    iIntros "#He !# %vs HΓ //". simpl.
    iApply (ewp_bind [LoadCtx]); first done. simpl.
    iApply (ewp_mono with "[HΓ]").
    { by iApply "He". }
    iIntros (v) "(%l & -> & #Hcpy & #Hinv)". iModIntro.
    iApply (ewp_atomic _ (⊤ ∖ ↑tyN.@l)).
    iMod (inv_acc _ (tyN.@l) with "Hinv") as "[(%w & >Hl & HA) Hclose]"; 
      first done.
    iModIntro. iApply (ewp_load with "Hl").
    iNext. 
    iDestruct ("Hcpy" with "HA") as "#Hτ".
    iIntros "Hl !>". simpl.
    iMod ("Hclose" with "[Hl]"); last done.
    iExists w. by iFrame.
  Qed.
  
  Lemma sem_typed_store Γ₁ Γ₂ e₁ e₂ ρ τ: 
    Γ₁ ⊨ e₁ : ρ : Ref τ -∗
    Γ₂ ⊨ e₂ : ρ : τ -∗
    Γ₁ ++ Γ₂ ⊨ (e₁ <- e₂) : ρ : ().
  Proof.
    iIntros "#He₁ #He₂ !# %vs HΓ₁₂ //=".
    rewrite !env_sem_typed_app.
    iDestruct "HΓ₁₂" as "(HΓ₁ & HΓ₂)". 
    iApply (ewp_bind [StoreRCtx _]); first done. simpl.
    iApply (ewp_mono with "[HΓ₂]").
    { by iApply "He₂". }
    iIntros (v) "Hτ". iModIntro.
    iApply (ewp_bind [StoreLCtx _]); first done. simpl.
    iApply (ewp_mono with "[HΓ₁]").
    { by iApply "He₁". }
    iIntros (w) "(%l & -> & #Hcpy & #Hinv)". iModIntro.
    iApply (ewp_atomic _ (⊤ ∖ ↑tyN.@l)).
    iMod (inv_acc _ (tyN.@l) with "Hinv") as "[(%w & >Hl & HA) Hclose]"; 
      first done.
    iModIntro. iApply (ewp_store with "Hl").
    iIntros "!> Hl !>". 
    iMod ("Hclose" with "[Hl Hτ]"); last done.
    iExists v. by iFrame. 
  Qed.
  
  (* Effect handling rules *)
  
  Lemma sem_typed_do Γ e ι κ: 
    Γ ⊨ e : (ι ⇒ κ) : ι -∗
    Γ ⊨ (do: e) : (ι ⇒ κ) : κ.
  Proof.
    iIntros "#He !# %vs HΓ //=". 
    iApply (ewp_bind [DoCtx OS]); first done.
    iApply (ewp_mono with "[HΓ]").
    { by iApply "He". }
    iIntros (v) "Hι". iModIntro. simpl.
    iApply ewp_do_os. rewrite upcl_sem_row_eff.
    iExists v. eauto with iFrame.
  Qed.
  
  
  Lemma sem_typed_shallow_try Γ₁ Γ₂ e h r ι κ τ τ': 
    let ρ := (ι ⇒ κ)%R in
    Γ₁ ⊨ e : ρ : τ' -∗
    Γ₂ ⊨ h : ⟨⟩ : (ι ⊸ (κ -{ ρ }-∘ τ') -{ ρ }-∘ τ) -∗
    Γ₂ ⊨ r : ⟨⟩ : (τ' -{ ρ }-∘ τ) -∗
    Γ₁ ++ Γ₂ ⊨ (TryWith e h r) : (ι ⇒ κ) : τ.
  Proof.
    iIntros "%ρ #He #Hh #Hr !# %vs HΓ₁₂ //=".
    rewrite !env_sem_typed_app.
    iDestruct "HΓ₁₂" as "(HΓ₁ & HΓ₂)". ewp_pure_steps.
    iApply (ewp_try_with with "[HΓ₁] [HΓ₂]").
    { by iApply "He". }
    iSplit; [|iSplit; iIntros (v k)];
    last (iIntros "HFalse"; by rewrite upcl_bottom).
    - iIntros (v) "Hv //=".
      iApply (ewp_bind [AppLCtx v]); first done.
      ewp_bottom.
      iApply (ewp_mono with "[HΓ₂]"); [by iApply "Hr"|].
      iIntros (w) "Hw". iModIntro. simpl.
      by iApply "Hw".
    - rewrite upcl_sem_row_eff.
      iIntros "(%a & -> & Ha & Hκb)".
      iApply (ewp_bind [AppLCtx k; AppLCtx a]); first done.
      ewp_bottom.
      iApply (ewp_mono with "[HΓ₂]").
      { by iApply "Hh". }
      iIntros (h') "Hh'". iModIntro. simpl. 
      iApply (ewp_bind [AppLCtx k]); first done. 
      iApply (ewp_mono with "[Hh' Ha]").
      { ewp_bottom. by iApply "Hh'". }
      iIntros (ha) "Hha". iModIntro. simpl.
      iApply "Hha". iIntros (w) "Hw".
      by iApply "Hκb".
  Qed.
  
  Lemma sem_typed_deep_try Γ₁ Γ₂ Γ₃ e h r ρ' ι κ τ τ': 
    let ρ := (ι ⇒ κ)%R in
    Γ₁ ⊨ e : ρ : τ -∗
    Γ₂ ⊨ h : ⟨⟩ : (ι → (κ -{ ρ' }-∘ τ') -{ ρ' }-> τ') -∗
    Γ₃ ⊨ r : ⟨⟩ : (τ -{ ρ' }-∘ τ') -∗
    Γ₁ ++ Γ₂ ++ Γ₃ ⊨ (deep-try: e with effect h | return r end) : ρ' : τ'.
  Proof.
    iIntros "%ρ #He #Hh #Hr !# %vs HΓ₁₂₃ //=".
    rewrite !env_sem_typed_app. 
    iDestruct "HΓ₁₂₃" as "(HΓ₁ & HΓ₂ & HΓ₃)". ewp_pure_steps.
    set ctx_r := AppRCtx (deep_try_with (λ: <>, subst_map vs e) 
                                        (subst_map vs h))%E.
    iApply (ewp_bind [ctx_r]); first done.
    ewp_bottom.
    iApply (ewp_mono with "[HΓ₃]").
    { by iApply "Hr". }
    iIntros (r') "Hr'". iModIntro. simpl.
    ewp_pure_steps.
    set ctx_h := [
      AppLCtx r';
      AppRCtx (deep_try_with (λ: <>, subst_map vs e))%E].
    iApply (ewp_bind ctx_h); first done.
    ewp_bottom.
    iApply (ewp_mono with "[HΓ₂]"); [by iApply "Hh"|].
    iIntros (h') "#Hh'". iModIntro. simpl. ewp_pure_steps.
    iApply (ewp_deep_try_with with "[HΓ₁]").
    { by iApply "He". }
    iLöb as "IH".
    rewrite !deep_handler_unfold.
    iSplit; [|iSplit; iIntros (v k)];
    last (iIntros "HFalse"; by rewrite upcl_bottom).
    - iIntros (v) "Hv //=".
      by iApply "Hr'".
    - rewrite upcl_sem_row_eff.
      iIntros "(%a & -> & Ha & Hκb)".
      iApply (ewp_bind [AppLCtx k]); first done. 
      ewp_bottom. simpl. 
      iApply (ewp_mono with "[Ha]"); [by iApply "Hh'"|].
      iIntros (ha) "Hha !>". iApply "Hha".
      iIntros (w) "Hw". iApply ("Hκb" with "Hw"). 
      iNext. rewrite !deep_handler_unfold. 
      iApply ("IH" with "Hr'").
    Qed.

End compatibility.
