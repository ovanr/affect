(* interp.v *)

(* This file contains the definition of the 
   interpretation of types, of rows, and of typing judgments. 
   Types are interpreted as semantic types which are Iris's predicates, 
   a row is interpreted as a semantic row which is an iEff protocol,
   and typing judgments are interpreted as specifications written in 
   terms of the extended weakest precondition.
*)

From iris.proofmode Require Import base tactics classes.
From iris.base_logic.lib Require Import iprop invariants.
From iris.program_logic Require Import weakestpre.
From iris Require Import bi.
From stdpp Require Import base stringmap fin_map_dom fin_maps.

(* Hazel Reasoning *)
From program_logic Require Import weakest_precondition 
                                  tactics 
                                  shallow_handler_reasoning 
                                  deep_handler_reasoning 
                                  state_reasoning.

(* Local imports *)
From affine_tes.lang Require Import hazel.
From affine_tes.logic Require Import iEff.


Context `{!heapGS Σ}.

(** * Semantic Types. *)

Definition sem_ty := val → (iProp Σ).

Declare Scope sem_ty_scope.
Bind Scope sem_ty_scope with sem_ty.
Delimit Scope sem_ty_scope with T.

(** * Semantic Row. *)

Definition sem_row := iEff Σ.

Declare Scope sem_row_scope.
Bind Scope ieff_scope with sem_row.
Delimit Scope sem_row_scope with R.

(* Copyable types *)
Definition copy_ty (τ : sem_ty) := ∀ v, Persistent (τ v).

(* Base types. *)
Definition sem_ty_unit : sem_ty := (λ v, ⌜ v = #() ⌝)%I.
Definition sem_ty_bool : sem_ty := (λ v, ∃ b : bool, ⌜ v = #b ⌝)%I.
Definition sem_ty_int : sem_ty := (λ v, ∃ n : Z, ⌜ v = #n ⌝)%I.

(* Reference Type *)
Definition tyN := nroot .@ "ty".
Definition sem_ty_ref (τ : sem_ty): sem_ty := 
  (λ v, ∃ l : loc, ⌜ v = #l ⌝ ∗ 
                   inv (tyN .@ l) (∃ w, l ↦ w ∗ ⌜ copy_ty τ ⌝ ∗ □ (τ w)))%I.

(* Product type. *)
Definition sem_ty_prod (τ κ : sem_ty) : sem_ty := 
  (λ v, ∃ v₁ v₂, ⌜v = (v₁, v₂)%V⌝ ∗ τ v₁ ∗ κ v₂)%I.

(* Empty Effect Row. *)
Definition sem_row_bot : sem_row := iEff_bottom.

(* Effect Row. *)
Definition sem_row_eff (τ κ : sem_ty) : sem_row :=
  (>> (a : val) >> ! a {{ τ a }};
   << (b : val) << ? b {{ κ b }} @OS).

Lemma upcl_sem_row_eff τ κ v Φ :
  iEff_car (upcl OS (sem_row_eff τ κ)) v Φ ⊣⊢
    (∃ a, ⌜ v = a ⌝ ∗ τ a ∗ (∀ b, κ b -∗ Φ b))%I.
Proof. by rewrite /sem_row_eff (upcl_tele' [tele _] [tele _]). Qed.

Lemma sem_row_eff_eq τ κ v Φ :
  iEff_car (sem_row_eff τ κ) v Φ ⊣⊢
    (∃ a, ⌜ a = v ⌝ ∗ τ a ∗ (∀ b, κ b -∗ Φ b))%I.
Proof. by rewrite /sem_row_eff (iEff_tele_eq' [tele _] [tele _]). Qed.

(* Linear Arrow type. *)
Definition sem_ty_larr
  (τ : sem_ty)
  (ρ : sem_row)
  (κ : sem_ty) : sem_ty :=
  (λ (v : val), ∀ (w : val), τ w -∗ EWP (v w) <| ρ |> {{ κ }})%I.

(* Unrestricted Arrow type. *)
Definition sem_ty_uarr
  (τ : sem_ty)
  (ρ : sem_row)
  (κ : sem_ty) : sem_ty :=
  (λ (v : val), ∀ (w : val), □ (τ w -∗ EWP (v w) <| ρ |> {{ κ }} ))%I.


(* Notations. *)
Notation "()" := sem_ty_unit : sem_ty_scope.
Notation "'𝔹'" := (sem_ty_bool) : sem_ty_scope.
Notation "'ℤ'" := (sem_ty_int) : sem_ty_scope.
Notation "τ '×' κ" := (sem_ty_prod τ%T κ%T)
  (at level 120, κ at level 200) : sem_ty_scope.

Notation "'Ref' τ" := (sem_ty_ref τ%T) 
  (at level 50) : sem_ty_scope.

Notation "⟨⟩" := sem_row_bot : sem_row_scope.
Notation "τ ⇒ κ" := (sem_row_eff τ%T κ%T) 
  (at level 100, κ at level 200) : sem_row_scope.

Notation "τ '-{' ρ '}-∘' κ" := (sem_ty_larr τ%T ρ%R κ%T)
  (at level 100, ρ, κ at level 200) : sem_ty_scope.
Notation "τ ⊸ κ" := (sem_ty_larr τ%T sem_row_bot κ%T)
  (at level 99, κ at level 200) : sem_ty_scope.

Notation "τ '-{' ρ '}->' κ" := (sem_ty_uarr τ%T ρ%R κ%T)
  (at level 100, ρ, κ at level 200) : sem_ty_scope.
Notation "τ → κ" := (sem_ty_uarr τ%T sem_row_bot κ%T)
  (at level 99, κ at level 200) : sem_ty_scope.

(** The Type Context

The type context is represented as a list.
Due to the requirement that a type context Γ is ctx_sem_typed,
we can utilize the seperation logic's disjointness to argue about
variables occuring twice in the context.

Thus if we have a `ctx_sem_typed Γ vs` assumption and
the same variable occurs twice in Γ we get that:

∙ They cannot be of the same non-persistent type (e.g. ref nat):
  So if we have `ctx_typed (l : ref nat; l : ref nat) vs`,  
  since the variables l are the same, we would have
  that l, v ∈ vs, and that ⟦ ref nat ⟧ v ∗ ⟦ ref nat ⟧ v
  But that means we would need to provide that l ↦ w ∗ l ↦ w
  which would be impossible.

∙ If they have the same type which is a persistent type (e.g. nat):
  Then it is fine, in fact it must be allowed to allow for Copy types

∙ If they don't have the same type:
  Then `vs` would still have only 1 value for the variable `l` so
  it would be impossible to provide ctx_typed proof.

*) 

Notation ctx := (list (string * sem_ty)).

(** The domain of the context. *)
Notation ctx_dom := (map fst).

Fixpoint ctx_sem_typed (Γ : ctx)
                       (vs : gmap string val) : iProp Σ :=
  match Γ with
    | [] => emp
    | (x,A) :: Γ' => (∃ v, ⌜ vs !! x = Some v ⌝ ∗ A v) ∗ 
                     ctx_sem_typed Γ' vs
  end.

Lemma ctx_sem_typed_empty vs : ⊢ ctx_sem_typed [] vs.
Proof. done. Qed.

Lemma ctx_sem_typed_insert Γ vs (x : string) v :
  x ∉ (ctx_dom Γ) →
  ctx_sem_typed Γ vs ⊢ ctx_sem_typed Γ (binder_insert x v vs).
Proof.
  iIntros (Helem) "Henv".
  iInduction Γ as [|[y A] Γ'] "IH"; first done. simpl in *.
  iDestruct "Henv" as "((%w & %Hvs & HAw) & HΓ')". iSplitL "HAw".
  - iExists w. iFrame. iPureIntro.
    destruct (decide (y = x)) as [->|]. 
    { destruct Helem. by apply elem_of_list_here. }
    by rewrite lookup_insert_ne.
  - iApply "IH"; last done. iPureIntro. 
    destruct (not_elem_of_cons (ctx_dom Γ') x y) as [[ ] _]; done.
Qed.

Lemma ctx_sem_typed_app Γ₁ Γ₂ vs :
  ctx_sem_typed (Γ₁ ++ Γ₂) vs ⊢ 
  ctx_sem_typed Γ₁ vs ∗ ctx_sem_typed Γ₂ vs.
Proof. 
  iIntros "HΓ₁₂". iInduction Γ₁ as [|[y A] Γ₁'] "IH"; first (by iFrame).
  simpl in *. 
  iDestruct "HΓ₁₂" as "($ & HΓ₁'₂)". by iApply "IH".
Qed.

Definition copy_ctx Γ :=
  ∀ vs, Persistent (ctx_sem_typed Γ vs).


(* Sub-typing and relations *)

Definition ty_le (A B : sem_ty) := ∀ v, A v ⊢ B v.
Definition row_le (ρ ρ' : sem_row) := ⊢ iEff_le ρ ρ'.
Definition ctx_le Γ₁ Γ₂ :=
  ∀ vs, ctx_sem_typed Γ₁ vs ⊢ ctx_sem_typed Γ₂ vs.

Notation "Γ₁ '≤C' Γ₂" := (ctx_le Γ₁ Γ₂) (at level 98).
Notation "τ '≤T' κ" := (ty_le τ%T κ%T) (at level 98).

Notation "ρ '≤R' ρ'" := (row_le ρ%R ρ'%R) (at level 98).

Lemma row_le_refl (ρ : sem_row) : ρ ≤R ρ.
Proof. iApply iEff_le_refl. Qed.

Lemma row_le_trans (ρ₁ ρ₂ ρ₃: sem_row) : 
    ρ₁ ≤R ρ₂ →
    ρ₂ ≤R ρ₃ →
    ρ₁ ≤R ρ₃. 
Proof. 
  intros Hρ₁₂ Hρ₂₃. 
  iApply iEff_le_trans; [iApply Hρ₁₂|iApply Hρ₂₃]. 
Qed.

Lemma row_le_bot (ρ : sem_row) :
  ⟨⟩ ≤R ρ.
Proof. iApply iEff_le_bottom. Qed.

Lemma row_le_eff (ι₁ ι₂ κ₁ κ₂ : sem_ty) :
  ι₁ ≤T ι₂ →
  κ₂ ≤T κ₁ →
  ((ι₁ ⇒ κ₁) ≤R (ι₂ ⇒ κ₂)).
Proof.
  iIntros (Hι₁₂ Hκ₂₁ v) "%Φ !#".
  rewrite !sem_row_eff_eq.
  iIntros "(%a & -> & Hι₁ & HκΦ₁)".
  iExists v. iSplit; first done. iSplitL "Hι₁".
  { by iApply Hι₁₂. }
  iIntros (b) "Hκ₂". iApply "HκΦ₁".
  by iApply Hκ₂₁.
Qed.

Lemma ty_le_refl (τ : sem_ty) : τ ≤T τ.
Proof. done. Qed.

Lemma ty_le_trans (τ₁ τ₂ τ₃ : sem_ty) :
  τ₁ ≤T τ₂ →
  τ₂ ≤T τ₃ →
  τ₁ ≤T τ₃.
Proof. 
  iIntros (Hτ₁₂ Hτ₂₃ v) "Hτ₁". 
  iApply Hτ₂₃. by iApply Hτ₁₂.
Qed.

Lemma ty_le_arr (τ κ : sem_ty) (ρ : sem_row) :
  (τ -{ ρ }-> κ) ≤T (τ -{ ρ }-∘ κ).
Proof.
  iIntros (v) "#Hτκ %w Hw".
  iApply (ewp_mono with "[Hw]").
  { by iApply "Hτκ". }
  iIntros (u) "Hu". by iModIntro.
Qed.

Lemma ty_le_larr (τ₁ κ₁ τ₂ κ₂ : sem_ty) (ρ ρ' : sem_row) :
  ρ ≤R ρ' →
  τ₂ ≤T τ₁ →
  κ₁ ≤T κ₂ →
  (τ₁ -{ ρ }-∘ κ₁) ≤T (τ₂ -{ ρ' }-∘ κ₂).
Proof.
  iIntros (Hρ Hτ₂₁ Hκ₁₂ v) "Hτκ₁ %w Hw".
  iApply ewp_os_prot_mono.
  { iApply Hρ. }
  iApply (ewp_mono with "[Hw Hτκ₁]").
  { iApply "Hτκ₁". by iApply Hτ₂₁. }
  iIntros (u) "Hu". iModIntro. by iApply Hκ₁₂.
Qed.

Lemma ty_le_uarr (τ₁ κ₁ τ₂ κ₂ : sem_ty) (ρ ρ' : sem_row) :
  ρ ≤R ρ' →
  τ₂ ≤T τ₁ →
  κ₁ ≤T κ₂ →
  (τ₁ -{ ρ }-> κ₁) ≤T (τ₂ -{ ρ' }-> κ₂).
Proof.
  iIntros (Hρ Hτ₂₁ Hκ₁₂ v) "#Hτκ₁ %w !# Hw".
  iApply ewp_os_prot_mono.
  { iApply Hρ. }
  iApply (ewp_mono with "[Hw]").
  { iApply "Hτκ₁". by iApply Hτ₂₁. }
  iIntros (u) "Hu". iModIntro. by iApply Hκ₁₂.
Qed.

Lemma ty_le_prod (τ₁ τ₂ κ₁ κ₂ : sem_ty) :
  τ₁ ≤T τ₂ →
  κ₁ ≤T κ₂ →
  (τ₁ × κ₁) ≤T (τ₂ × κ₂).
Proof.
  iIntros (Hτ₁₂ Hκ₁₂ v) "(%w₁ & %w₂ & -> &Hw₁ & Hw₂)".
  iExists w₁, w₂. iSplit; first done. iSplitL "Hw₁".
  { by iApply Hτ₁₂. }
  by iApply Hκ₁₂.
Qed.

Lemma ctx_le_refl Γ : Γ ≤C Γ.
Proof. done. Qed.

Lemma ctx_le_trans Γ₁ Γ₂ Γ₃ : 
  Γ₁ ≤C Γ₂ →
  Γ₂ ≤C Γ₃ →
  Γ₁ ≤C Γ₃.
Proof.
  iIntros (HΓ₁₂ HΓ₂₃ vs) "HΓ₁ //=".  
  iApply HΓ₂₃. by iApply HΓ₁₂.
Qed.

Lemma ctx_le_cons Γ₁ Γ₂ τ₁ τ₂ x :
  Γ₁ ≤C Γ₂ →
  τ₁ ≤T τ₂ →
  (x, τ₁) :: Γ₁ ≤C (x, τ₂) :: Γ₂.
Proof.
  iIntros (HΓ₁₂ Hτ₁₂ vs) "//= ((%v & Hlookup & Hv) & HΓ₁)".
  iSplitR "HΓ₁"; last (by iApply HΓ₁₂).
  iExists v. iFrame. by iApply Hτ₁₂.
Qed.

Lemma ctx_le_copy_contraction Γ x τ :
  copy_ty τ →
  (x, τ) :: Γ ≤C (x, τ) :: (x, τ) :: Γ.
Proof.
  iIntros (Hcpyτ vs) "//= [(%w & -> & Hτ) $]". 
  rewrite Hcpyτ. iDestruct "Hτ" as "#Hτ".
  iSplitL; iExists w; by iSplit.
Qed.

Lemma ctx_le_swap Γ x y τ κ :
  (x, τ) :: (y, κ) :: Γ ≤C (y, κ) :: (x, τ) :: Γ.
Proof. iIntros (vs) "($ & $ & $) //=". Qed.

(* Copyable types *)

Lemma copy_ty_unit : copy_ty ().
Proof. 
  iIntros (v). apply bi.pure_persistent.
Qed.

Lemma copy_ty_bool : copy_ty 𝔹.
Proof. 
  iIntros (v).
  apply bi.exist_persistent. iIntros (x).
  apply bi.pure_persistent.
Qed.

Lemma copy_ty_nat : copy_ty ℤ.
Proof. 
  iIntros (v). 
  apply bi.exist_persistent. iIntros (x).
  apply bi.pure_persistent.
Qed.

Lemma copy_ty_ref τ : copy_ty (Ref τ).
Proof.
  iIntros (v). unfold sem_ty_ref.
  apply bi.exist_persistent. iIntros (x).
  apply bi.sep_persistent.
  { apply bi.pure_persistent. }
  apply inv_persistent.
Qed.

Lemma copy_ty_uarr τ ρ κ : copy_ty (τ -{ ρ }-> κ).
Proof.
  iIntros (v). unfold sem_ty_uarr.
  apply bi.forall_persistent. iIntros (x).
  apply bi.intuitionistically_persistent.
Qed.

Lemma copy_ty_prod τ κ : copy_ty τ → copy_ty κ → copy_ty (τ × κ).
Proof.
  iIntros (Hcpyτ Hcpyκ v). unfold sem_ty_prod.
  do 2 (apply bi.exist_persistent; iIntros (?)).
  apply bi.sep_persistent; [apply bi.pure_persistent|].
  apply bi.sep_persistent.
  { apply Hcpyτ. }
  apply Hcpyκ. 
Qed.

Lemma copy_ctx_nil : copy_ctx [].
Proof. iIntros (vs). apply bi.emp_persistent. Qed.

Lemma copy_ctx_cons Γ x τ : 
  copy_ctx Γ →
  copy_ty τ →
  copy_ctx ((x, τ) :: Γ).
Proof. 
  iIntros (HcpyΓ Hcpyτ vs). simpl.
  apply bi.sep_persistent; last done.
  apply bi.exist_persistent. intros v.
  apply bi.sep_persistent; last done.
  apply bi.pure_persistent.
Qed.

(** Semantic typing rules *)

(* Semantic typing judgment. *)
Definition sem_typed 
  (Γ  : ctx)
  (e  : expr)
  (ρ  : sem_row)
  (α  : sem_ty) : Prop :=
    ∀ (vs : gmap string val),
        ctx_sem_typed Γ vs ⊢ EWP (subst_map vs e) <| ρ |> {{ α }}.

Notation "Γ ⊨ e : ρ : α" := (sem_typed Γ e%E ρ%R α%T)
  (at level 74, e, ρ, α at next level) : bi_scope.

Notation "⊨ e : ρ : α" := (sem_typed [] e%E ρ%R α%T)
  (at level 74, e, ρ, α at next level) : bi_scope.

Open Scope bi_scope.
Open Scope ieff_scope.

(* Semantic typing rules. *)

(* Base rules *)

Lemma sem_typed_unit Γ : 
  Γ ⊨ #() : ⟨⟩ : ().
Proof.
  iIntros (vs) "HΓ //=". by iApply ewp_value.
Qed.

Lemma sem_typed_bool Γ (b : bool) : 
  Γ ⊨ #b : ⟨⟩ : 𝔹.
Proof.
  iIntros (vs) "HΓ //=". iApply ewp_value. by iExists b.
Qed.

Lemma sem_typed_int Γ (i : Z) : 
  Γ ⊨ #i : ⟨⟩ : ℤ.
Proof.
  iIntros (vs) "HΓ //=". iApply ewp_value. by iExists i.
Qed.

(* Subsumption rule *)

Lemma sem_typed_sub Γ Γ' e ρ ρ' τ τ':
  Γ' ≤C Γ →
  ρ  ≤R ρ' → 
  τ  ≤T τ' →
  Γ ⊨ e: ρ : τ →
  Γ' ⊨ e: ρ' : τ'.
Proof.
  iIntros (HΓle Hρle Hτle He vs) "HΓ' //=".
  rewrite HΓle.
  iApply ewp_os_prot_mono.
  { iApply Hρle. }
  iApply (ewp_mono with "[HΓ']").
  { by iApply He. }
  iIntros (v) "Hτ". iModIntro.
  by iApply Hτle.
Qed.

(* λ-calculus rules *)

Lemma sem_typed_lfun Γ x e τ ρ κ: 
  x ∉ (ctx_dom Γ) →
  (x,τ) :: Γ ⊨ e : ρ : κ →
  Γ ⊨ (λ: x, e) : ⟨⟩ : (τ -{ ρ }-∘ κ).
Proof.
  iIntros (Helem He vs) "HΓ //=".
  ewp_pure_steps. iIntros (w) "Hw". ewp_pure_steps. 
  rewrite <- subst_map_insert.
  iApply He. simpl in *. iSplitL "Hw".
  - iExists w. iFrame. iPureIntro.
    by rewrite lookup_insert.
  - by iApply ctx_sem_typed_insert.
Qed.

Lemma sem_typed_ufun Γ x e τ ρ κ: 
  x ∉ (ctx_dom Γ) →
  copy_ctx Γ →
  (x,τ) :: Γ ⊨ e : ρ : κ →
  Γ ⊨ (λ: x, e) : ⟨⟩ : (τ -{ ρ }-> κ).
Proof.
  iIntros (Helem HcpyΓ He vs) "HΓ //=".
  ewp_pure_steps. rewrite HcpyΓ. iDestruct "HΓ" as "#HΓ".
  iIntros (w) "!# Hw". ewp_pure_steps. 
  rewrite <- subst_map_insert.
  iApply He. simpl in *. iSplitL "Hw".
  - iExists w. iFrame. iPureIntro.
    by rewrite lookup_insert.
  - by iApply ctx_sem_typed_insert.
Qed.

Lemma sem_typed_app Γ₁ Γ₂ e₁ e₂ τ ρ κ: 
  Γ₁ ⊨ e₁ : ρ : (τ -{ ρ }-∘ κ) →
  Γ₂ ⊨ e₂ : ρ : τ →
  Γ₁ ++ Γ₂ ⊨ (e₁ e₂) : ρ : κ.
Proof.
  iIntros (He₁ He₂ vs) "HΓ₁₂ //=".
  rewrite ctx_sem_typed_app.
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

Lemma sem_typed_pair Γ₁ Γ₂ e₁ e₂ τ ρ κ: 
  Γ₁ ⊨ e₁ : ρ : τ →
  Γ₂ ⊨ e₂ : ρ : κ →
  Γ₁ ++ Γ₂ ⊨ (e₁,e₂) : ρ : (τ × κ).
Proof.
  iIntros (He₁ He₂ vs) "HΓ₁₂ //=".
  rewrite ctx_sem_typed_app.
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

Lemma sem_typed_pair_elim Γ₁ Γ₂ x₁ x₂ e₁ e₂ τ ρ κ ι: 
  x₁ ∉ (ctx_dom Γ₂) ->
  x₂ ∉ (ctx_dom Γ₂) ->
  x₁ ≠ x₂ ->
  Γ₁ ⊨ e₁ : ρ : (τ × κ) →
  (x₁, τ) :: (x₂, κ) :: Γ₂ ⊨ e₂ : ρ : ι →
  Γ₁ ++ Γ₂ ⊨ (let: (x₁, x₂) := e₁ in e₂) : ρ : ι.
Proof.
  iIntros (Helem₁ Helem₂ Hnex₁₂ He₁ He₂ vs) "HΓ₁₂ //=".
  rewrite ctx_sem_typed_app.
  iDestruct "HΓ₁₂" as "[HΓ₁ HΓ₂]".
  ewp_pure_steps.
  set ex1x2 := (λ: x₁ x₂, subst_map (binder_delete x₂ 
                                    (binder_delete x₁ vs)) e₂)%V. 
  iApply (ewp_bind ([AppLCtx ex1x2; AppRCtx pair_elim])); first done.
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
  by repeat (iApply ctx_sem_typed_insert; first done).
Qed.

Lemma sem_typed_if Γ₁ Γ₂ e₁ e₂ e₃ ρ τ: 
  Γ₁ ⊨ e₁ : ρ : 𝔹 →
  Γ₂ ⊨ e₂ : ρ : τ →
  Γ₂ ⊨ e₃ : ρ : τ →
  Γ₁ ++ Γ₂ ⊨ (if: e₁ then e₂ else e₃) : ρ : τ.
Proof.
  iIntros (He₁ He₂ He₃ vs) "HΓ₁₂ //=".
  rewrite ctx_sem_typed_app.
  iDestruct "HΓ₁₂" as "[HΓ₁ HΓ₂]".
  iApply (ewp_bind [IfCtx (subst_map vs e₂) (subst_map vs e₃)])
    ;first done.
  iApply (ewp_mono with "[HΓ₁]").
  { by iApply He₁. }
  iIntros (v) "(%b & ->)". iModIntro. simpl.
  destruct b; ewp_pure_steps.
  - by iApply He₂.
  - by iApply He₃.
Qed.

(* reference rules *)

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
  Γ ⊨ e : ρ : τ →
  Γ ⊨ ref e : ρ : Ref τ.
Proof.
  iIntros (Hcpyτ He vs) "HΓ //=".
  iApply (ewp_bind [AllocCtx]); first done. simpl.
  iApply (ewp_mono with "[HΓ]").
  { by iApply He. }
  iIntros (v) "Hτ". iModIntro.
  iApply ewp_alloc. iIntros "!> %l Hl".
  iMod (inv_alloc (tyN.@l) _
       (∃ w, l ↦ w ∗ ⌜copy_ty τ⌝ ∗ □ τ w)%I with "[Hl Hτ]") as "#Hinv".
  { iExists v. iFrame. iSplit; first done.
    by iApply bi.intuitionistic. }
  iModIntro. iExists l. by auto.
Qed.

Lemma sem_typed_load Γ e ρ τ: 
  Γ ⊨ e : ρ : Ref τ →
  Γ ⊨ !e : ρ : τ.
Proof.
  iIntros (He vs) "HΓ //". simpl.
  iApply (ewp_bind [LoadCtx]); first done. simpl.
  iApply (ewp_mono with "[HΓ]").
  { by iApply He. }
  iIntros (v) "(%l & -> & #Hinv)". iModIntro.
  iApply (ewp_atomic _ (⊤ ∖ ↑tyN.@l)).
  iMod (inv_acc _ (tyN.@l) with "Hinv") as "[(%w & >Hl & >%Hcpy & HA) Hclose]"; 
    first done.
  iModIntro. iApply (ewp_load with "Hl").
  iNext. iDestruct "HA" as "#HA". 
  iIntros "Hl !>". simpl.
  iMod ("Hclose" with "[Hl]"); last done.
  iExists w. iFrame. by iSplit.
Qed.

Lemma sem_typed_store Γ₁ Γ₂ e₁ e₂ ρ τ: 
  Γ₁ ⊨ e₁ : ρ : Ref τ →
  Γ₂ ⊨ e₂ : ρ : τ →
  Γ₁ ++ Γ₂ ⊨ (e₁ <- e₂) : ρ : ().
Proof.
  iIntros (He₁ He₂ vs) "HΓ₁₂ //=".
  rewrite !ctx_sem_typed_app.
  iDestruct "HΓ₁₂" as "(HΓ₁ & HΓ₂)". 
  iApply (ewp_bind [StoreRCtx _]); first done. simpl.
  iApply (ewp_mono with "[HΓ₂]").
  { by iApply He₂. }
  iIntros (v) "Hτ". iModIntro.
  iApply (ewp_bind [StoreLCtx _]); first done. simpl.
  iApply (ewp_mono with "[HΓ₁]").
  { by iApply He₁. }
  iIntros (w) "(%l & -> & #Hinv)". iModIntro.
  iApply (ewp_atomic _ (⊤ ∖ ↑tyN.@l)).
  iMod (inv_acc _ (tyN.@l) with "Hinv") as "[(%w & >Hl & >%Hcpy & HA) Hclose]"; 
    first done.
  iModIntro. iApply (ewp_store with "Hl").
  iIntros "!> Hl !>". 
  iMod ("Hclose" with "[Hl Hτ]"); last done.
  iExists v. iFrame. iSplit; first done.
  by iApply bi.intuitionistic.
Qed.

(* Effect handling rules *)

Lemma sem_typed_do Γ e ι κ: 
  Γ ⊨ e : (ι ⇒ κ) : ι →
  Γ ⊨ (do: e) : (ι ⇒ κ) : κ.
Proof.
  iIntros (He vs) "HΓ //=". 
  iApply (ewp_bind [DoCtx OS]); first done.
  iApply (ewp_mono with "[HΓ]").
  { by iApply He. }
  iIntros (v) "Hι". iModIntro. simpl.
  iApply ewp_do_os. rewrite upcl_sem_row_eff.
  iExists v. eauto with iFrame.
Qed.


Lemma sem_typed_shallow_try Γ₁ Γ₂ e h r ι κ τ τ': 
  let ρ := (ι ⇒ κ)%R in
  Γ₁ ⊨ e : ρ : τ' →
  Γ₂ ⊨ h : ⟨⟩ : (ι ⊸ (κ -{ ρ }-∘ τ') -{ ρ }-∘ τ) →
  Γ₂ ⊨ r : ⟨⟩ : (τ' -{ ρ }-∘ τ) →
  Γ₁ ++ Γ₂ ⊨ (TryWith e h r) : (ι ⇒ κ) : τ.
Proof.
  iIntros (ρ He Hh Hr vs) "HΓ₁₂ //=".
  rewrite !ctx_sem_typed_app.
  iDestruct "HΓ₁₂" as "(HΓ₁ & HΓ₂)". ewp_pure_steps.
  iApply (ewp_try_with with "[HΓ₁] [HΓ₂]").
  { by iApply He. }
  iSplit; [|iSplit; iIntros (v k)];
  last (iIntros "HFalse"; by rewrite upcl_bottom).
  - iIntros (v) "Hv //=".
    iApply (ewp_bind [AppLCtx v]); first done.
    iApply ewp_os_prot_mono; [by iApply iEff_le_bottom|]. 
    iApply (ewp_mono with "[HΓ₂]"); [by iApply Hr|].
    iIntros (w) "Hw". iModIntro. simpl.
    by iApply "Hw".
  - rewrite upcl_sem_row_eff.
    iIntros "(%a & -> & Ha & Hκb)".
    iApply (ewp_bind [AppLCtx k; AppLCtx a]); first done.
    iApply ewp_os_prot_mono; [by iApply iEff_le_bottom|]. 
    iApply (ewp_mono with "[HΓ₂]").
    { by iApply Hh. }
    iIntros (h') "Hh'". iModIntro. simpl. 
    iApply (ewp_bind [AppLCtx k]); first done. 
    iApply (ewp_mono with "[Hh' Ha]").
    { iApply ewp_os_prot_mono; [by iApply iEff_le_bottom|].
      by iApply "Hh'". }
    iIntros (ha) "Hha". iModIntro. simpl.
    iApply "Hha". iIntros (w) "Hw".
    by iApply "Hκb".
Qed.

(* 
∙ Why does the handler branch of a deep-try handler need to be a value?
  Because even though it is typed inside an empty context, we might produce
   a non-persistent resource (a continuation) while evaluating the closed expression.
  A counter-example where the handler is an expression and it eventually 
  leads to a continuation being called twice (so an unsafe expression) follows:

   deep-try (do #();; do #()) with
     effect (
       shallow-try do #() with 
         effect (λ: _ k', λ v k, k' #();; k #())
         return (λ: _, λ v k, #())
       end
     )
     return (λ v, v) 
   end
  ⇝
   deep-try (do #();; do #()) with
     effect (
       shallow-try eff #() ∙ with 
         effect (λ: () k', λ v k, k' #();; k #())
         return (λ: _, λ v k, #())
       end
     )
     return (λ v, v) 
   end
  ⇝ 
   deep-try (do #();; do #()) with
     effect (
         λ v k, (cont l ∙) #() ;; k #()
     )
     return id 
   end / l ↦ #false
  ⇝ 
   deep-try (eff #() (∙ ;; do #())) with
     effect (
         λ v k, (cont l ∙) #() ;; k #()
     )
     return (λ v, v) 
   end / l ↦ #false
  ⇝ 
   (cont l ∙) #() ;; 
   deep-try (#() ;; do #()) with
      effect (λ v k, (cont l ∙) #() ;; k #())
      return (λ v, v) 
   end / l ↦ #false
 *)
Lemma sem_typed_deep_try Γ₁ Γ₂ Γ₃ e (h : val) r ρ' ι κ τ τ': 
  copy_ctx Γ₂ →
  let ρ := (ι ⇒ κ)%R in
  Γ₁ ⊨ e : ρ : τ →
  Γ₂ ⊨ (of_val h) : ⟨⟩ : (ι ⊸ (κ -{ ρ' }-∘ τ') -{ ρ' }-∘ τ') →
  Γ₃ ⊨ r : ⟨⟩ : (τ -{ ρ' }-∘ τ') →
  Γ₁ ++ Γ₂ ++ Γ₃ ⊨ (deep-try: e with effect h | return r end) : ρ' : τ'.
Proof.
  iIntros (Hcpy ρ He Hh Hr vs) "HΓ₁₂₃ //=".
  rewrite !ctx_sem_typed_app. rewrite Hcpy.
  iDestruct "HΓ₁₂₃" as "(HΓ₁ & #HΓ₂ & HΓ₃)". ewp_pure_steps.
  set rctx := AppRCtx (deep_try_with (λ: <>, subst_map vs e)%E (subst_map vs h))%E.
  iApply (ewp_bind [rctx]); first done.
  iApply ewp_os_prot_mono; [by iApply iEff_le_bottom|].
  iApply (ewp_mono with "[HΓ₃]").
  { by iApply Hr. }
  iIntros (r') "Hr'". iModIntro. simpl.
  ewp_pure_steps.
  iApply (ewp_deep_try_with with "[HΓ₁]").
  { by iApply He. }
  iLöb as "IH".
  rewrite !deep_handler_unfold.
  iSplit; [|iSplit; iIntros (v k)];
  last (iIntros "HFalse"; by rewrite upcl_bottom).
  - iIntros (v) "Hv //=".
    by iApply "Hr'".
  - rewrite upcl_sem_row_eff.
    iIntros "(%a & -> & Ha & Hκb)".
    iApply (ewp_bind [AppLCtx k; AppLCtx a]); first done. 
    iApply ewp_os_prot_mono; [by iApply iEff_le_bottom|]. 
    simpl. iApply ewp_mono.
    { by iApply Hh. }
    iIntros (h') "Hh'". iModIntro. simpl.
    iApply (ewp_bind [AppLCtx k]); first done. simpl.
    iApply ewp_os_prot_mono; [by iApply iEff_le_bottom|]. 
    iApply (ewp_mono with "[Hh' Ha]").
    { by iApply "Hh'". }
    iIntros (h'a) "Hh'a". iModIntro. simpl.
    iApply "Hh'a". iIntros (w) "Hw".
    iApply ("Hκb" with "Hw"). iNext.
    rewrite !deep_handler_unfold. 
    iApply ("IH" with "Hr'").
  Qed.
