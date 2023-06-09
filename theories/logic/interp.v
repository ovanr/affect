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

(* Hazel Reasoning *)
From program_logic Require Import protocols 
                                  weakest_precondition 
                                  tactics 
                                  shallow_handler_reasoning 
                                  deep_handler_reasoning 
                                  state_reasoning.

(* Local imports *)
From affine_tes.lang Require Import hazel.

(** * Semantic Types. *)

Definition sem_ty Σ := val → (iProp Σ).

Declare Scope sem_ty_scope.
Bind Scope sem_ty_scope with sem_ty.
Delimit Scope sem_ty_scope with T.

(** * Semantic Row. *)

Definition sem_row Σ := iEff Σ.

Declare Scope sem_row_scope.
Bind Scope ieff_scope with sem_row.
Delimit Scope sem_row_scope with R.

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

Lemma upcl_sem_row_eff {Σ} A B v Φ :
  iEff_car (upcl OS (sem_row_eff (Σ:=Σ) A B)) v Φ ⊣⊢
    (∃ a, ⌜ v = a ⌝ ∗ A a ∗ (∀ b, B b -∗ Φ b))%I.
Proof. by rewrite /sem_row_eff (upcl_tele' [tele _] [tele _]). Qed.

(* Arrow type. *)
Definition sem_ty_arr `{!heapGS Σ}
  (A : sem_ty Σ)
  (R : sem_row Σ)
  (B : sem_ty Σ) :=
  (λ (v : val), ∀ (w : val), A w -∗ EWP (v w) <| R |> {{ B }})%I.

(* Notations. *)
Notation "()" := sem_ty_unit : sem_ty_scope.
Notation "'𝔹'" := (sem_ty_bool) : sem_ty_scope.
Notation "'ℤ'" := (sem_ty_int) : sem_ty_scope.
Infix "*" := sem_ty_prod : sem_ty_scope.

Notation "⟨⟩" := sem_row_null : sem_row_scope.
Notation "A ⇒ B" := (sem_row_eff A B) 
  (at level 100, B at level 200) : sem_row_scope.

Notation "A '-{' R '}-∘' B" := (sem_ty_arr A%T R%R B%T)
  (at level 100, R, B at level 200) : sem_ty_scope.
Notation "A ⊸ B" := (sem_ty_arr A%T sem_row_null B%T)
  (at level 99, B at level 200) : sem_ty_scope.


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

Notation ctx Σ := (list (string * (sem_ty Σ))).

(** The domain of the context. *)
Definition ctx_dom Σ : ctx Σ -> list string := map fst.

Fixpoint ctx_sem_typed Σ (Γ : ctx Σ)
                         (vs : gmap string val) : iProp Σ :=
  match Γ with
    | [] => True
    | (x,A) :: Γ' => (∃ v, ⌜ vs !! x = Some v ⌝ ∗ A v) ∗ 
                     ctx_sem_typed Σ Γ' vs
  end.

Lemma ctx_sem_typed_empty Σ vs : ⊢ ctx_sem_typed Σ [] vs.
Proof. done. Qed.

Lemma ctx_sem_typed_insert Σ Γ vs (x : string) v :
  x ∉ (ctx_dom Σ Γ) →
  ctx_sem_typed Σ Γ vs ⊢ ctx_sem_typed Σ Γ (binder_insert x v vs).
Proof.
  iIntros (Helem) "Henv".
  iInduction Γ as [|[y A] Γ'] "IH"; first done. simpl in *.
  iDestruct "Henv" as "((%w & %Hvs & HAw) & HΓ')". iSplitL "HAw".
  - iExists w. iFrame. iPureIntro.
    destruct (decide (y = x)) as [->|]. 
    { destruct Helem. by apply elem_of_list_here. }
    by rewrite lookup_insert_ne.
  - iApply "IH"; last done. iPureIntro. 
    destruct (not_elem_of_cons (ctx_dom Σ Γ') x y) as [[ ] _]; done.
Qed.

Lemma ctx_sem_typed_app Σ Γ₁ Γ₂ vs :
  ctx_sem_typed Σ (Γ₁ ++ Γ₂) vs ⊢ 
  ctx_sem_typed Σ Γ₁ vs ∗ ctx_sem_typed Σ Γ₂ vs.
Proof. 
  iIntros "HΓ₁₂". iInduction Γ₁ as [|[y A] Γ₁'] "IH"; first (by iFrame).
  simpl in *. 
  iDestruct "HΓ₁₂" as "($ & HΓ₁'₂)". by iApply "IH".
Qed.


Section semantic_typing_rules.

Context `{!heapGS Σ}.

(* Semantic typing judgment. *)
Definition sem_typed 
  (Γ  : ctx Σ)
  (e  : expr)
  (ρ  : sem_row Σ)
  (α  : sem_ty Σ) : Prop :=
    ∀ (vs : gmap string val),
        ctx_sem_typed Σ Γ vs ⊢ EWP (subst_map vs e) <| ρ |> {{ α }}.

Notation "Γ ⊨ e : ρ : α" := (sem_typed Γ e%E ρ%R α%T)
  (at level 74, e, ρ, α at next level) : bi_scope.

Notation "⊨ e : ρ : α" := (sem_typed [] e%E ρ%R α%T)
  (at level 74, e, ρ, α at next level) : bi_scope.

Open Scope bi_scope.
Open Scope ieff_scope.

(* Semantic typing rules. *)

(* Base rules *)

Lemma sem_typed_unit Γ ρ : 
  Γ ⊨ #() : ρ : ().
Proof.
  iIntros (vs) "HΓ //=". by iApply ewp_value.
Qed.

Lemma sem_typed_bool Γ ρ (b : bool) : 
  Γ ⊨ #b : ρ : 𝔹.
Proof.
  iIntros (vs) "HΓ //=". iApply ewp_value. by iExists b.
Qed.

Lemma sem_typed_int Γ ρ (i : Z) : 
  Γ ⊨ #i : ρ : ℤ.
Proof.
  iIntros (vs) "HΓ //=". iApply ewp_value. by iExists i.
Qed.

(* Subsumption rule *)

Lemma sem_typed_sub Γ e τ ρ: 
  Γ ⊨ e: ⟨⟩ : τ →
  Γ ⊨ e: ρ : τ.
Proof.
  iIntros (He vs) "HΓ //=".
  iApply ewp_os_prot_mono.
  { iApply iEff_le_bottom. }
  by iApply He.
Qed.

(* λ-calculus rules *)

Lemma sem_typed_fun Γ x e τ ρ κ: 
  x ∉ (ctx_dom Σ Γ) →
  (x,τ) :: Γ ⊨ e : ρ : κ →
  Γ ⊨ (λ: x, e) : ⟨⟩ : (τ -{ ρ }-∘ κ).
Proof.
  iIntros (Helem He vs) "HΓ //=".
  ewp_pure_steps. iIntros (w) "Hτw". ewp_pure_steps. 
  rewrite <- subst_map_insert.
  iApply He. simpl in *. iSplitL "Hτw".
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
  Γ₁ ++ Γ₂ ⊨ (e₁,e₂) : ρ : τ * κ.
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
  x₁ ∉ (ctx_dom Σ Γ₂) ->
  x₂ ∉ (ctx_dom Σ Γ₂) ->
  x₁ ≠ x₂ ->
  Γ₁ ⊨ e₁ : ρ : (τ * κ) →
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
Lemma sem_typed_deep_try Γ₁ Γ₂ e (h : val) r ρ' ι κ τ τ': 
  let ρ := (ι ⇒ κ)%R in
  Γ₁ ⊨ e : ρ : τ →
  ⊨ (of_val h) : ⟨⟩ : (ι ⊸ (κ -{ ρ' }-∘ τ') -{ ρ' }-∘ τ') →
  Γ₂ ⊨ r : ⟨⟩ : (τ -{ ρ' }-∘ τ') →
  Γ₁ ++ Γ₂ ⊨ (deep-try: e with effect h | return r end) : ρ' : τ'.
Proof.
  iIntros (ρ He Hh Hr vs) "HΓ₁₂ //=".
  rewrite ctx_sem_typed_app.
  iDestruct "HΓ₁₂" as "[HΓ₁ HΓ₂]". ewp_pure_steps.
  set rctx := AppRCtx (deep_try_with (λ: <>, subst_map vs e)%E (subst_map vs h))%E.
  iApply (ewp_bind [rctx]); first done.
  iApply ewp_os_prot_mono; [by iApply iEff_le_bottom|].
  iApply (ewp_mono with "[HΓ₂]").
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
    { iApply Hh. iApply (ctx_sem_typed_empty _ empty). }
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

End semantic_typing_rules.
