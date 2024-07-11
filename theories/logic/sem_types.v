
(* sem_types.v *)

(* This file contains the definition of semantic types,
   together with the definition of base types and type formers.  
*)

From iris.proofmode Require Import base tactics.
From iris.algebra Require Import ofe list.
From iris.base_logic Require Export iprop upred invariants.

(* Hazel Reasoning *)
From hazel.program_logic Require Import weakest_precondition 
                                        state_reasoning
                                        protocols.

(* Local imports *)
From affect.lib Require Import logic.
From affect.lang Require Import affect.
From affect.logic Require Import sem_def.
From affect.logic Require Import mode.
From affect.logic Require Import sem_sig.
From affect.logic Require Import sem_row.
From affect.logic Require Import sem_env.
From affect.logic Require Import ewpw.

(* Base types. *)
Definition sem_ty_void {Σ} : sem_ty Σ := (λ v, False)%I.
Definition sem_ty_unit {Σ} : sem_ty Σ := (λ v, ⌜ v = #() ⌝)%I.
Definition sem_ty_bool {Σ} : sem_ty Σ := (λ v, ∃ b : bool, ⌜ v = #b ⌝)%I.
Definition sem_ty_int {Σ} : sem_ty Σ := (λ v, ∃ n : Z, ⌜ v = #n ⌝)%I.
Definition sem_ty_string {Σ} : sem_ty Σ := (λ v, ∃ s : string, ⌜ v = #(LitStr s)⌝)%I.
Definition sem_ty_top {Σ} : sem_ty Σ := (λ v, True)%I.

Definition sem_ty_bang {Σ} (τ : sem_ty Σ) : sem_ty Σ := (λ v, □ τ v)%I.
(* generalised bang type *)
Notation "'!_[ m ] τ" := (
  match m with
      OS => τ 
    | MS => (sem_ty_bang τ)
  end) (at level 10) : sem_ty_scope.
Definition sem_env_bang {Σ} (Γ : env Σ) : env Σ := (map (λ xτ, (xτ.1, sem_ty_bang xτ.2)) Γ).

(* Copyable Reference Type *)
Definition tyN := nroot .@ "ty".
Definition sem_ty_ref_cpy `{heapGS Σ} (τ : sem_ty Σ): sem_ty Σ := 
  (λ v, ∃ l : loc, ⌜ v = #l ⌝ ∗ inv (tyN .@ l) (∃ w, l ↦ w ∗ τ w))%I.

(* Substructural Reference Type *)
Definition sem_ty_ref `{!heapGS Σ} (τ : sem_ty Σ): sem_ty Σ := 
  (λ v, ∃ l : loc, ⌜ v = #l ⌝ ∗ (∃ w, l ↦ w ∗ τ w))%I.

(* Product type. *)
Definition sem_ty_prod {Σ} (τ κ : sem_ty Σ) : sem_ty Σ := 
  (λ v, ∃ v₁ v₂, ⌜v = (v₁, v₂)%V⌝ ∗ τ v₁ ∗ κ v₂)%I.

(* Sum type. *)
Definition sem_ty_sum {Σ} (τ κ : sem_ty Σ) : sem_ty Σ :=
  (λ v, ∃ v', (⌜v = InjLV v'%V⌝ ∗ τ v') ∨ (⌜ v = InjRV v'⌝ ∗ κ v'))%I.

(* Arrow type. *)
Definition sem_ty_arr (m : mode) `{heapGS Σ} 
  (ρ : sem_row Σ)
  (τ : sem_ty Σ)
  (κ : sem_ty Σ) : sem_ty Σ :=
  (λ (v : val), □? m (
    ∀ (w : val),
      τ w -∗ 
      EWPW (v w) <| ρ |> {{ u, κ u}}))%I.

(* Affine Arrow type. *)
Definition sem_ty_aarr `{heapGS Σ}
  (ρ : sem_row Σ)
  (τ : sem_ty Σ)
  (κ : sem_ty Σ) : sem_ty Σ := sem_ty_arr OS ρ τ κ.

(* Unrestricted Arrow type. *)
Definition sem_ty_uarr `{heapGS Σ}
  (ρ : sem_row Σ)
  (τ : sem_ty Σ)
  (κ : sem_ty Σ) : sem_ty Σ := sem_ty_arr MS ρ τ κ.

(* Polymorphic type. *)
Definition sem_ty_forall `{heapGS Σ} 
    (m : mode) (C : sem_ty Σ → sem_ty Σ)  : sem_ty Σ := 
    (λ v, ∀ τ, □? m (EWPW (v <_>)%E {{ v, C τ v }}))%I.

(* Polymorphic effect type. *)
Definition sem_ty_row_forall `{heapGS Σ} 
  (m : mode) (A : sem_row Σ → sem_ty Σ) : sem_ty Σ := 
    (λ v, ∀ θ, □? m (EWPW (v <_>)%E {{ v, A θ v }}))%I.

(* Polymorphic type. *)
Definition sem_ty_mode_forall `{heapGS Σ} 
  (m : mode) (C : mode → sem_ty Σ) : sem_ty Σ := 
    (λ v, ∀ ν, □? m (EWPW (v <_>)%E {{ v, C ν v }}))%I.

(* Existential type. *)
Definition sem_ty_exists `{irisGS eff_lang Σ} 
  (C : sem_ty Σ → sem_ty Σ) : sem_ty Σ := (λ v, ∃ τ, C τ v)%I.

(** Recursive types *)
Definition sem_ty_rec_pre {Σ} (C : sem_ty Σ → sem_ty Σ)
  (rec : sem_ty Σ) : sem_ty Σ := (λ v, ▷ (∃ rec', rec ≡ rec' ∧ C rec' v))%I.
Global Instance sem_ty_rec_pre_contractive {Σ} (C : sem_ty Σ → sem_ty Σ) :
  Contractive (sem_ty_rec_pre C).
Proof. solve_contractive. Qed.
Definition sem_ty_rec {Σ} (C : sem_ty Σ -d> sem_ty Σ) : sem_ty Σ :=
  fixpoint (sem_ty_rec_pre C).

Lemma sem_ty_rec_unfold {Σ} (C : sem_ty Σ → sem_ty Σ) `{!NonExpansive C} v :
  (sem_ty_rec C)%T v ⊣⊢ ▷ C (sem_ty_rec C)%T v. 
Proof.
  rewrite {1}/sem_ty_rec.
  assert (fixpoint (sem_ty_rec_pre C) v ≡ sem_ty_rec_pre C (fixpoint (sem_ty_rec_pre C)) v).
  { apply non_dep_fun_equiv. apply fixpoint_unfold. }
  rewrite H. iSplit.
  - iIntros "(%rec' & #Hrec & HC) !>".
      rewrite /sem_ty_rec.
      iAssert (C rec' ≡ C (fixpoint (sem_ty_rec_pre C)))%I as "#H".
      { by iRewrite "Hrec". }
      rewrite !discrete_fun_equivI. by iRewrite - ("H" $! v).
  - iIntros "HC //=". iNext. iExists (sem_ty_rec C).
    by iFrame. 
Qed.
Notation "'Void'" := sem_ty_void : sem_ty_scope.
Notation "()" := sem_ty_unit : sem_ty_scope.
Notation "'𝔹'" := (sem_ty_bool) : sem_ty_scope.
Notation "'ℤ'" := (sem_ty_int) : sem_ty_scope.
Notation "'Str'" := (sem_ty_string) : sem_ty_scope.
Notation "⊤" := (sem_ty_top) : sem_ty_scope.
Notation "'! τ " := (sem_ty_bang τ)
  (at level 10) : sem_ty_scope.
Notation "'! Γ " := (sem_env_bang Γ)
  (at level 10) : sem_env_scope.
Notation "τ '×' κ" := (sem_ty_prod τ%T κ%T)
  (at level 120, κ at level 200) : sem_ty_scope.
Infix "+" := (sem_ty_sum) : sem_ty_scope.

Notation "'Ref' τ" := (sem_ty_ref τ%T) 
  (at level 50) : sem_ty_scope.

Notation "'Refᶜ' τ" := (sem_ty_ref_cpy τ%T) 
  (at level 50) : sem_ty_scope.

Notation "'∀T:' α , C " := (sem_ty_forall MS (λ α, C%T)) 
  (at level 180) : sem_ty_scope.

Notation "'∀R:' θ , C " := (sem_ty_row_forall MS (λ θ, C%T)) 
  (at level 180) : sem_ty_scope.

Notation "'∀M:' ν , C " := (sem_ty_mode_forall MS (λ ν, C%T)) 
  (at level 180) : sem_ty_scope.

Notation "'∀T:[' m ']' α , C " := (sem_ty_forall m (λ α, C%T)) 
  (at level 180) : sem_ty_scope.

Notation "'∀R:[' m ']' θ , C " := (sem_ty_row_forall m (λ θ, C%T)) 
  (at level 180) : sem_ty_scope.

Notation "'∀M:[' m ']' ν , C " := (sem_ty_mode_forall m (λ ν, C%T)) 
  (at level 180) : sem_ty_scope.

Notation "'∃:' α , C " := (sem_ty_exists (λ α, C%T)) 
  (at level 180) : sem_ty_scope.

Notation "'μT:' α , C " := (sem_ty_rec (λ α, C%T))
  (at level 180) : sem_ty_scope.

Notation "τ '-{' ρ '}-[' m ']->' κ" := (sem_ty_arr m ρ%R τ%T κ%T)
  (at level 100, m, ρ, κ at level 200) : sem_ty_scope.

Notation "τ '-[' m ']->' κ" := (sem_ty_arr m ⟨⟩%R τ%T κ%T)
  (at level 100, m, κ at level 200) : sem_ty_scope.

Notation "τ ⊸ κ" := (sem_ty_aarr ⟨⟩%R τ%T κ%T)
  (at level 99, κ at level 200) : sem_ty_scope.

Notation "τ '-{' ρ '}-∘' κ" := (sem_ty_aarr ρ%R τ%T κ%T)
  (at level 100, ρ, κ at level 200) : sem_ty_scope.
Notation "τ ⊸ κ" := (sem_ty_aarr ⟨⟩%R τ%T κ%T)
  (at level 99, κ at level 200) : sem_ty_scope.

Notation "τ '-{' ρ '}->' κ" := (sem_ty_uarr ρ%R τ%T κ%T)
  (at level 100, ρ, κ at level 200) : sem_ty_scope.
Notation "τ → κ" := (sem_ty_uarr ⟨⟩%R τ%T κ%T)
  (at level 99, κ at level 200) : sem_ty_scope.

(* Derived Types *)

Definition ListF {Σ} (τ : sem_ty Σ) := (λ α, () + (τ × α))%T.

(* List type. *)
Definition sem_ty_list {Σ} (τ : sem_ty Σ) : sem_ty Σ := 
    sem_ty_rec (ListF τ).

Notation "'List' τ" := (sem_ty_list τ%T) 
  (at level 50) : sem_ty_scope.

(* List type. *)
Definition sem_ty_option {Σ} (τ : sem_ty Σ) : sem_ty Σ := (() + τ)%T.

Notation "'Option' τ" := (sem_ty_option τ%T) 
  (at level 50) : sem_ty_scope.

(**  Prove that type formers are non-expansive and respect setoid equality. *)
Section types_properties.
  Context `{heapGS Σ}.

  Implicit Types σ : sem_sig Σ.

  Ltac solve_non_expansive :=
    repeat intros ?;
    unfold sem_ty_unit, sem_ty_int, sem_ty_bool, sem_ty_bang,
           sem_ty_prod, sem_ty_sum, sem_ty_arr, sem_ty_aarr, sem_ty_uarr,
           sem_ty_uarr, sem_ty_ref, sem_ty_ref_cpy, 
           sem_ty_rec, sem_ty_list, sem_ty_forall, sem_ty_exists;
    repeat (f_equiv || done || intros ? || by apply non_dep_fun_dist).

  Global Instance sem_ty_bang_ne : NonExpansive (@sem_ty_bang Σ).
  Proof. solve_non_expansive. Qed.

  Global Instance sem_ty_prod_ne : NonExpansive2 (@sem_ty_prod Σ).
  Proof. solve_non_expansive. Qed.

  Global Instance sem_ty_sum_ne : NonExpansive2 (@sem_ty_sum Σ).
  Proof. solve_non_expansive. Qed.

  Global Instance sem_ty_arr_ne m : NonExpansive3 (sem_ty_arr m).
  Proof. solve_non_expansive. Qed.

  Global Instance sem_ty_aarr_ne : NonExpansive3 sem_ty_aarr.
  Proof. rewrite /sem_ty_aarr. apply _. Qed.

  Global Instance sem_ty_uarr_ne : NonExpansive3 sem_ty_uarr.
  Proof. rewrite /sem_ty_uarr. apply _. Qed.

  Global Instance sem_ty_ref_ne : NonExpansive (@sem_ty_ref Σ _).
  Proof. solve_non_expansive. Qed.

  Global Instance sem_ty_ref_cpy_ne : NonExpansive (@sem_ty_ref_cpy Σ _).
  Proof. solve_non_expansive. Qed.

  Global Instance sem_ty_forall_ne m n :
    Proper (pointwise_relation _ (dist n) ==> dist n) (sem_ty_forall m).
  Proof. intros ????. unfold sem_ty_forall. 
         do 3 f_equiv. f_equiv. by apply non_dep_fun_dist.
  Qed.

  Global Instance sem_ty_forall_row_ne m n :
    Proper (pointwise_relation _ (dist n) ==> dist n) (sem_ty_row_forall m).
  Proof. intros ????. unfold sem_ty_row_forall. 
         do 3 f_equiv. f_equiv. by apply non_dep_fun_dist.
  Qed.

  Global Instance sem_ty_forall_mode_ne m n :
    Proper (pointwise_relation _ (dist n) ==> dist n) (sem_ty_mode_forall m).
  Proof. intros ????. unfold sem_ty_mode_forall. 
         do 3 f_equiv. f_equiv. by apply non_dep_fun_dist.
  Qed.

  Global Instance sem_ty_exist_ne n :
    Proper (pointwise_relation _ (dist n) ==> dist n) sem_ty_exists.
  Proof. 
    intros ????. unfold sem_ty_exists; repeat f_equiv. 
    by apply non_dep_fun_dist. 
  Qed.

  Global Instance sem_ty_rec_ne :
    NonExpansive (@sem_ty_rec Σ).
  Proof.
    intros ????. unfold sem_ty_rec. apply fixpoint_ne.
    intros ??. unfold sem_ty_rec_pre. do 4 f_equiv. 
    by apply non_dep_fun_dist.
  Qed.

  Global Instance sem_ty_listF_ne τ : NonExpansive (@ListF Σ τ).
  Proof. intros ?????. rewrite /ListF. 
         apply non_dep_fun_dist. by repeat f_equiv.
  Qed.

  Global Instance sem_ty_listF_ne_2 : NonExpansive2 (@ListF Σ).
  Proof. intros ???????. unfold ListF; by repeat f_equiv. Qed.

  Global Instance sem_ty_list_ne : NonExpansive (@sem_ty_list Σ).
  Proof. intros ?????. unfold sem_ty_list. 
         apply non_dep_fun_dist. f_equiv. 
         rewrite /ListF. intros ?. by repeat f_equiv.
  Qed.

  Global Instance sem_ty_bang_proper : Proper ((≡) ==> (≡)) (@sem_ty_bang Σ).
  Proof. solve_non_expansive. Qed.

  Global Instance sem_ty_prod_proper : Proper ((≡) ==> (≡) ==> (≡)) (@sem_ty_prod Σ).
  Proof. solve_non_expansive. Qed.

  Global Instance sem_ty_sum_proper : Proper ((≡) ==> (≡) ==> (≡)) (@sem_ty_sum Σ).
  Proof. solve_non_expansive. Qed.

  Global Instance sem_ty_arr_proper m : Proper ((≡) ==> (≡) ==> (≡) ==> (≡)) (sem_ty_arr m).
  Proof. solve_non_expansive. Qed.

  Global Instance sem_ty_aarr_proper : Proper ((≡) ==> (≡) ==> (≡) ==> (≡)) sem_ty_aarr.
  Proof. rewrite /sem_ty_aarr. apply _. Qed.

  Global Instance sem_ty_uarr_proper : Proper ((≡) ==> (≡) ==> (≡) ==> (≡)) sem_ty_uarr.
  Proof. rewrite /sem_ty_uarr. apply _. Qed.

  Global Instance sem_ty_ref_proper : Proper ((≡) ==> (≡)) (@sem_ty_ref Σ _).
  Proof. intros ????. unfold sem_ty_ref; by repeat f_equiv. Qed.

  Global Instance sem_ty_ref_cpy_proper : Proper ((≡) ==> (≡)) (@sem_ty_ref_cpy Σ _).
  Proof. intros ????. unfold sem_ty_ref_cpy; by repeat f_equiv. Qed.

  Global Instance sem_ty_forall_proper m :
    Proper (pointwise_relation _ (≡) ==> (≡)) (sem_ty_forall m).
  Proof. 
    intros ????. unfold sem_ty_forall; repeat f_equiv. 
    by apply non_dep_fun_equiv. 
  Qed.

  Global Instance sem_ty_row_forall_proper m :
    Proper (pointwise_relation _ (≡) ==> (≡)) (sem_ty_row_forall m).
  Proof. 
    intros ????. unfold sem_ty_row_forall; repeat f_equiv. 
    by apply non_dep_fun_equiv. 
  Qed.

  Global Instance sem_ty_mode_forall_proper m :
    Proper (pointwise_relation _ (≡) ==> (≡)) (sem_ty_mode_forall m).
  Proof. 
    intros ????. unfold sem_ty_mode_forall; repeat f_equiv. 
    by apply non_dep_fun_equiv. 
  Qed.

  Global Instance sem_ty_exist_proper :
    Proper (pointwise_relation _ (≡) ==>(≡)) sem_ty_exists.
  Proof. 
    intros ????. unfold sem_ty_exists; repeat f_equiv.
    by apply non_dep_fun_equiv.
  Qed.

  Global Instance sem_ty_rec_proper :
    Proper (pointwise_relation _ (≡) ==>(≡)) (@sem_ty_rec Σ).
  Proof.
    intros C1 C2 HA. apply equiv_dist=> n.
    apply sem_ty_rec_ne=> A. by apply equiv_dist.
  Qed.

  Global Instance sem_ty_uarr_persistent `{heapGS Σ} (τ κ : sem_ty Σ) (ρ : sem_row Σ) v :
    Persistent ((sem_ty_uarr ρ τ κ) v).
  Proof.
    rewrite /sem_ty_uarr /sem_ty_arr. simpl. apply _.
  Qed.

  Global Instance sem_ty_forall_type_persistent `{heapGS Σ} (C : sem_ty Σ → sem_ty Σ) v :
    Persistent ((sem_ty_forall MS C) v).
  Proof.
    unfold sem_ty_forall. simpl. apply _.
  Qed.

  Global Instance sem_ty_row_forall_persistent `{heapGS Σ} (C : sem_row Σ → sem_ty Σ) v :
    Persistent ((sem_ty_row_forall MS C) v).
  Proof.
    unfold sem_ty_row_forall. simpl. apply _.
  Qed.

  Global Instance sem_ty_mode_forall_persistent `{heapGS Σ} (C : mode → sem_ty Σ) v :
    Persistent ((sem_ty_mode_forall MS C) v).
  Proof.
    unfold sem_ty_mode_forall. simpl. apply _.
  Qed.

End types_properties.

Section copyable_types.
  
  Context `{heapGS Σ}.

  Implicit Types τ κ : sem_ty Σ.

  (* Copyable types *)
  
  Open Scope sem_ty_scope.

  Lemma copy_ty_void : ⊢ @copy_ty Σ Void.
  Proof. iIntros "!# %v $!". Qed.

  Lemma copy_ty_unit : ⊢ @copy_ty Σ ().
  Proof. iIntros "!# %v $!". Qed.
  
  Lemma copy_ty_bool : ⊢ @copy_ty Σ 𝔹.
  Proof. iIntros "!# %v #$". Qed.
  
  Lemma copy_ty_nat : ⊢ @copy_ty Σ ℤ.
  Proof. iIntros "!# %v #$". Qed.
  
  Lemma copy_ty_top : ⊢ @copy_ty Σ ⊤.
  Proof. iIntros "!# %v #$". Qed.

  Lemma copy_ty_bang τ : ⊢ copy_ty ('! τ).
  Proof. iIntros "!# %v #$". Qed.

  Lemma copy_ty_uarr τ σ κ : ⊢ copy_ty (τ -{ σ }-> κ).
  Proof. 
    rewrite /sem_ty_uarr /sem_ty_arr /=.
    iIntros "/= !# %v #$". 
  Qed.
  
  Lemma copy_ty_prod τ κ : copy_ty τ -∗ copy_ty κ -∗ copy_ty (τ × κ).
  Proof. 
    iIntros "#Hcpyτ #Hcpyκ !# %v (% & % & -> & Hτ & Hκ)". 
    iDestruct ("Hcpyτ" with "Hτ") as "#Hτ'".
    iDestruct ("Hcpyκ" with "Hκ") as "#Hκ'". 
    iIntros "!#". iExists v₁, v₂. by iFrame "#".
  Qed.

  Lemma copy_ty_sum τ κ : copy_ty τ -∗ copy_ty κ -∗ copy_ty (τ + κ).
  Proof.
    iIntros "#Hcpyτ #Hcpyκ !# %v (% & [(-> & Hτ)|(-> & Hκ)])". 
    - iDestruct ("Hcpyτ" with "Hτ") as "#Hτ'". iIntros "!#". 
      iExists v'. iLeft. by iFrame "#".
    - iDestruct ("Hcpyκ" with "Hκ") as "#Hκ'". iIntros "!#". 
      iExists v'. iRight. by iFrame "#".
  Qed.

  Lemma copy_ty_forallT C : ⊢ copy_ty (∀T: α, C α).
  Proof. iIntros "!# % #$". Qed.

  Lemma copy_ty_forallR C : ⊢ copy_ty (∀R: θ, C θ).
  Proof. iIntros "!# % #$". Qed.

  Lemma copy_ty_forallM C : ⊢ copy_ty (∀M: ν, C ν).
  Proof. iIntros "!# % #$". Qed.

  Lemma copy_ty_ref τ : ⊢ copy_ty (Refᶜ τ).
  Proof. iIntros "!# % #$". Qed.

  Lemma copy_ty_exists A : (∀ α, copy_ty (A α)) -∗ copy_ty (∃: α, A α).
  Proof. 
    iIntros "#H !# % [%α Hτ']". 
    iDestruct ("H" with "Hτ'") as "#Hτ".
    iIntros "!#". by iExists α.
  Qed.

  Lemma copy_ty_rec A `{NonExpansive A}: 
    □ (∀ α, (copy_ty α) -∗ copy_ty (A α)) -∗ 
    @copy_ty Σ (μT: α, A α).
  Proof. 
    iIntros "#H !# %". iLöb as "IH" forall (v). 
    rewrite {1 2} sem_ty_rec_unfold.
    iIntros "Hτ". iApply bi.later_intuitionistically.
    iNext. iApply ("H" with "[] Hτ"). 
    rewrite /copy_ty /tc_opaque. iApply "IH".
  Qed.

  Lemma copy_ty_option τ : copy_ty τ -∗ copy_ty (Option τ).
  Proof. 
    iIntros "#H". 
    iApply copy_ty_sum; [iApply copy_ty_unit|done]. 
  Qed.

  Lemma copy_ty_list τ : copy_ty τ -∗ copy_ty (List τ).
  Proof.
    iIntros "#Hτ". iApply copy_ty_rec.
    iIntros "!# % #Hα". 
    iApply copy_ty_sum; [iApply copy_ty_unit|].
    by iApply copy_ty_prod.
  Qed.

  Lemma copy_env_nil : ⊢ @copy_env Σ [].
  Proof. iIntros "!# % #$". Qed.
  
  Lemma copy_env_cons Γ x τ : 
    copy_env Γ -∗
    copy_ty τ -∗
    copy_env ((x, τ) :: Γ).
  Proof. 
    iIntros "#HΓcpy #Hτcpy !# % (% & %Hrw & Hτ & HΓ)".
    iDestruct ("Hτcpy" with "Hτ") as "#Hτ'".
    iDestruct ("HΓcpy" with "HΓ") as "#HΓ'".
    iIntros "!#". iExists v. by iFrame "#".
  Qed.

End copyable_types.

Section type_sub.

(* Subsumption relation on modes and rows wrt to types *)

Lemma row_type_sub_copy {Σ} (ρ : sem_row Σ) (τ : sem_ty Σ) : copy_ty τ -∗ ρ ≼ₜ τ.
Proof.
  iIntros "#Hτcpy %w %v %Φ !# Hρ Hτ.".
  iDestruct ("Hτcpy" with "Hτ.") as "#Hτ".
  iApply (pmono_prot_prop _ (sem_row_car ρ) with "[] Hρ").
  iIntros "!# % H". iFrame "#". iApply "H".
Qed.

Lemma row_type_sub_bang {Σ} (ρ : sem_row Σ) (τ : sem_ty Σ) : ⊢ ρ ≼ₜ ('! τ).
Proof.
  iIntros (w v Φ) "!# Hρ #Hτ".
  iApply (pmono_prot_prop _ (sem_row_car ρ) with "[] Hρ").
  iIntros "!# % $ //".
Qed.

Lemma row_type_sub_mfbang_mbang {Σ} (m : mode) (ρ : sem_row Σ) (τ : sem_ty Σ) : ⊢ ¡_[ m ] ρ ≼ₜ ('!_[ m ] τ).
Proof. destruct m; [iApply row_type_sub_fbang|iApply row_type_sub_bang]. Qed.

Lemma mode_type_sub_mbang {Σ} m (τ : sem_ty Σ) : ⊢ m ₘ≼ₜ '!_[m] τ.
Proof. 
  rewrite /mode_type_sub /=. iIntros "!# % Hτ". 
  destruct m; simpl; first done. iApply "Hτ".
Qed.

Lemma mode_type_sub_mbang_meet {Σ} (m m' : mode) (τ : sem_ty Σ) : ⊢ m ⊓ₘ m' ₘ≼ₜ ('!_[ m ] τ).
Proof. 
  destruct m; first rewrite mode_glb_os; first iApply mode_type_sub_os.
  iApply mode_type_sub_ms. iApply copy_ty_bang.
Qed.

End type_sub.

Section sub_typing.

  Context `{!heapGS Σ}.

  Lemma ty_le_refl (τ : sem_ty Σ) : ⊢ τ ≤T τ.
  Proof. iIntros "!# % $". Qed.
  
  Lemma ty_le_trans (τ₁ τ₂ τ₃ : sem_ty Σ) :
    τ₁ ≤T τ₂ -∗
    τ₂ ≤T τ₃ -∗
    τ₁ ≤T τ₃.
  Proof. 
    iIntros "#Hτ₁₂ #Hτ₂₃ !# %v Hτ₁". 
    iApply "Hτ₂₃". by iApply "Hτ₁₂".
  Qed.
  
  Lemma ty_le_void (τ : sem_ty Σ) :
    ⊢ Void ≤T τ.
  Proof. iIntros "% !# []". Qed.

  Lemma ty_le_mbang_intro m (τ : sem_ty Σ) :
    copy_ty τ -∗
    τ ≤T '!_[m] τ.
  Proof. 
    iIntros "#Hcpy".
    destruct m; simpl; first iApply ty_le_refl.
    iIntros "!# %v Hτ". 
    iDestruct ("Hcpy" with "Hτ") as "#Hτ'".
    iIntros "!# {$#Hτ'}". 
  Qed.
        
  Lemma ty_le_mbang_elim (m : mode) (τ : sem_ty Σ) :
    ⊢ ('!_[m] τ) ≤T τ.
  Proof. destruct m; first iApply ty_le_refl. iIntros "!# %v #$". Qed.

  Lemma ty_le_mbang_comp m (τ τ' : sem_ty Σ) :
    τ ≤T τ' -∗ ('!_[m] τ) ≤T ('!_[m] τ').
  Proof. 
    iIntros "#Hττ'".
    destruct m; first iApply "Hττ'".
    iIntros "!# %v #H!τ !#". 
    by iApply "Hττ'".
  Qed.

  Lemma ty_le_mbang_idemp_intro m (τ : sem_ty Σ) :
    ⊢ '!_[m] τ ≤T '!_[m] ('!_[m] τ).
  Proof. 
    destruct m; simpl; first iApply ty_le_refl.
    iApply (ty_le_mbang_intro MS). iApply copy_ty_bang.
  Qed.

  Lemma ty_le_mbang_comm m m' (τ : sem_ty Σ) :
    ⊢ '!_[m] ('!_[m'] τ) ≤T '!_[m'] ('!_[m] τ). 
  Proof. 
    destruct m, m'; iApply ty_le_refl.
  Qed.

  Lemma ty_le_mbang_mode_le m m' (τ : sem_ty Σ) :
    ⊢ m' ≤M m -∗ ('!_[m] τ) ≤T ('!_[m'] τ). 
  Proof. 
    iIntros "H". destruct m.
    - iDestruct (mode_le_OS_inv with "H") as "->".
      iApply ty_le_refl.
    - destruct m'; [iApply (ty_le_mbang_elim MS)|iApply ty_le_refl].
Qed.

  Lemma ty_le_mbang_arr_intro (τ κ : sem_ty Σ) (ρ : sem_row Σ) (m : mode) :
    ⊢ (τ -{ ρ }-[ m ]-> κ) ≤T '!_[m] (τ -{ ρ }-[ m ]-> κ).
  Proof.
    iIntros. destruct m; simpl; first iApply ty_le_refl.
    iApply (ty_le_mbang_intro MS).
    iApply copy_ty_uarr.
  Qed.

  Lemma ty_le_arr (τ₁ κ₁ τ₂ κ₂ : sem_ty Σ) (ρ ρ' : sem_row Σ) (m m' : mode) :
    m' ≤M m -∗
    ρ ≤R ρ' -∗
    τ₂ ≤T τ₁ -∗
    κ₁ ≤T κ₂ -∗
    (τ₁ -{ ρ }-[ m ]-> κ₁) ≤T (τ₂ -{ ρ' }-[ m' ]-> κ₂).
  Proof.
    iIntros "#Hm #Hρ  #Hτ₂₁ #Hκ₁₂ !# %v Hτκ₁". 
    destruct m.
    - iDestruct "Hm" as "[<-|%H]"; last inv H.  
      rewrite /sem_ty_arr /=. 
      iApply (intuitionistically_if_mono_iprop with "[] Hτκ₁").
      iIntros "!# Hτκ₁ % Hτ₂".
      iApply (ewpw_sub with "Hρ").
      iApply (ewpw_mono with "[Hτκ₁ Hτ₂]").
      { iApply ("Hτκ₁" with "[Hτ₂]"); by iApply "Hτ₂₁". }
      iIntros "!# % Hκ !>". by iApply "Hκ₁₂".
    - rewrite /sem_ty_arr /=.  
      iApply bi.intuitionistically_intuitionistically_if.
      iDestruct "Hτκ₁" as "#Hτκ₁". iIntros "!# %w Hτ₂".
      iApply (ewpw_sub with "Hρ").
      iApply (ewpw_mono with "[Hτκ₁ Hτ₂]").
      { iApply ("Hτκ₁" with "[Hτ₂]"); by iApply "Hτ₂₁". }
      iIntros "!# % Hκ !>". by iApply "Hκ₁₂".
  Qed.
      
  Lemma ty_le_u2aarr (τ κ : sem_ty Σ) (ρ : sem_row Σ) :
    ⊢ (τ -{ ρ }-> κ) ≤T (τ -{ ρ }-∘ κ).
  Proof.
    iApply ty_le_arr; [|iApply row_le_refl|iApply ty_le_refl|iApply ty_le_refl].
    iApply mode_le_MS.
  Qed.

  Lemma ty_le_aarr (τ₁ κ₁ τ₂ κ₂ : sem_ty Σ) (ρ ρ' : sem_row Σ) :
    ρ ≤R ρ' -∗
    τ₂ ≤T τ₁ -∗
    κ₁ ≤T κ₂ -∗
    (τ₁ -{ ρ }-∘ κ₁) ≤T (τ₂ -{ ρ' }-∘ κ₂).
  Proof.
    iIntros "#Hρ  #Hτ₂₁ #Hκ₁₂".
    iApply ty_le_arr; [iApply mode_le_refl|iApply "Hρ"|iApply "Hτ₂₁"|iApply "Hκ₁₂"].
  Qed.
  
  Lemma ty_le_uarr (τ₁ κ₁ τ₂ κ₂ : sem_ty Σ) (ρ ρ' : sem_row Σ) :
    ρ ≤R ρ' -∗
    τ₂ ≤T τ₁ -∗
    κ₁ ≤T κ₂ -∗
    (τ₁ -{ ρ }-> κ₁) ≤T (τ₂ -{ ρ' }-> κ₂).
  Proof.
    iIntros "#Hρ  #Hτ₂₁ #Hκ₁₂".
    iApply ty_le_arr; [iApply mode_le_refl|iApply "Hρ"|iApply "Hτ₂₁"|iApply "Hκ₁₂"].
  Qed.
  
  Lemma ty_le_ref (τ₁ τ₂ : sem_ty Σ) :
    τ₁ ≤T τ₂ -∗
    (Ref τ₁) ≤T (Ref τ₂).
  Proof.
    iIntros "#Hτ₁₂ !# %v (%l & -> & (%w & Hl & Hτw))".
    iExists l. iSplit; first done.
    iExists w. iFrame. by iApply "Hτ₁₂".
  Qed.

  Lemma ty_le_prod (τ₁ τ₂ κ₁ κ₂ : sem_ty Σ) :
    τ₁ ≤T τ₂ -∗
    κ₁ ≤T κ₂ -∗
    (τ₁ × κ₁) ≤T (τ₂ × κ₂).
  Proof.
    iIntros "#Hτ₁₂ #Hκ₁₂ !# %v (%w₁ & %w₂ & -> &Hw₁ & Hw₂)".
    iExists w₁, w₂. iSplit; first done. iSplitL "Hw₁".
    { by iApply "Hτ₁₂". }
    by iApply "Hκ₁₂".
  Qed.
  
  Lemma ty_le_mbang_prod_intro m (τ κ : sem_ty Σ) :
    τ ≤T '!_[m] τ -∗
    κ ≤T '!_[m] κ -∗
    (τ × κ) ≤T '!_[m] (τ × κ).
  Proof.
    iIntros "#Hτ #Hκ". 
    destruct m; simpl; first iApply ty_le_refl.
    iApply (ty_le_mbang_intro MS).
    iApply (copy_ty_prod with "Hτ Hκ").
  Qed.

  Lemma ty_le_sum (τ₁ τ₂ κ₁ κ₂ : sem_ty Σ) :
    τ₁ ≤T τ₂ -∗
    κ₁ ≤T κ₂ -∗
    (τ₁ + κ₁) ≤T (τ₂ + κ₂).
  Proof.
    iIntros "#Hτ₁₂ #Hκ₁₂ !# %v (%v' & [(-> & Hτ₁)|(-> & Hκ₁)])"; iExists v'. 
    - iLeft. iSplit; first done. by iApply "Hτ₁₂".
    - iRight. iSplit; first done. by iApply "Hκ₁₂". 
  Qed.

  Lemma ty_le_mbang_sum_intro m (τ κ : sem_ty Σ) :
    τ ≤T '!_[m] τ -∗
    κ ≤T '!_[m] κ -∗
    (τ + κ) ≤T '!_[m] (τ + κ).
  Proof.
    iIntros "#Hτ #Hκ". 
    destruct m; simpl; first iApply ty_le_refl.
    iApply (ty_le_mbang_intro MS).
    iApply (copy_ty_sum with "Hτ Hκ").
  Qed.

  Lemma ty_le_option (τ₁ τ₂ : sem_ty Σ) :
    τ₁ ≤T τ₂ -∗
    (Option τ₁) ≤T (Option τ₂).
  Proof. iIntros "#?". iApply ty_le_sum; last done. iIntros "!# % $". Qed.

  Lemma ty_le_forall m (τ₁ τ₂ : sem_ty Σ → sem_ty Σ) :
    (∀ α, τ₁ α ≤T τ₂ α) -∗
    (∀T:[m] α, τ₁ α)%T ≤T (∀T:[m] α, τ₂ α).
  Proof.
    iIntros "#Hτ₁₂ !# %v". destruct m; simpl. 
    - iIntros "Hτ₁ %τ /=". iApply (ewpw_mono with "[Hτ₁]"); [iApply "Hτ₁"|].
      iIntros "!# % Hτ !>". by iApply "Hτ₁₂".
    - iIntros "#Hτ₁ %τ /= !#". rewrite /sem_ty_forall /=.
      iApply (ewpw_mono with "[Hτ₁]"); [iApply "Hτ₁"|].
      iIntros "!# % Hτ !>". by iApply "Hτ₁₂".
  Qed.

  Lemma ty_le_mbang_forall_intro m (τ : sem_ty Σ → sem_ty Σ) :
    ⊢ (∀T:[m] α, τ α)%T ≤T '!_[m] (∀T:[m] α, τ α).
  Proof.
    destruct m; simpl; first iApply ty_le_refl.
    iApply (ty_le_mbang_intro MS); iApply copy_ty_forallT.
  Qed.

  Lemma ty_le_row_forall m (τ₁ τ₂ : sem_row Σ → sem_ty Σ) :
    (∀ θ, τ₁ θ ≤T τ₂ θ) -∗
    (∀R:[m] θ, τ₁ θ) ≤T (∀R:[m] θ, τ₂ θ).
  Proof.
    iIntros "#Hτ₁₂ !# %v". destruct m; simpl. 
    - iIntros "Hτ₁ %τ /=". iApply (ewpw_mono with "[Hτ₁]"); [iApply "Hτ₁"|].
      iIntros "!# % Hτ !>". by iApply "Hτ₁₂".
    - iIntros "#Hτ₁ %τ /= !#". rewrite /sem_ty_row_forall /=. 
      iApply (ewpw_mono with "[Hτ₁]"); [iApply "Hτ₁"|].
      iIntros "!# % Hτ !>". by iApply "Hτ₁₂".
  Qed.

  Lemma ty_le_mbang_row_forall_intro m (τ : sem_row Σ → sem_ty Σ) :
    ⊢ (∀R:[m] θ, τ θ)%T ≤T '!_[m] (∀R:[m] θ, τ θ).
  Proof.
    destruct m; simpl; first iApply ty_le_refl.
    iApply (ty_le_mbang_intro MS); iApply copy_ty_forallR.
  Qed.

  Lemma ty_le_mode_forall m (τ₁ τ₂ : mode → sem_ty Σ) :
    (∀ ν, τ₁ ν ≤T τ₂ ν) -∗
    (∀M:[m] ν, τ₁ ν) ≤T (∀M:[m] ν, τ₂ ν).
  Proof.
    iIntros "#Hτ₁₂ !# %v". destruct m; simpl. 
    - iIntros "Hτ₁ %τ /=". iApply (ewpw_mono with "[Hτ₁]"); [iApply "Hτ₁"|].
      iIntros "!# % Hτ !>". by iApply "Hτ₁₂".
    - iIntros "#Hτ₁ %τ /= !#". rewrite /sem_ty_mode_forall /=. 
      iApply (ewpw_mono with "[Hτ₁]"); [iApply "Hτ₁"|].
      iIntros "!# % Hτ !>". by iApply "Hτ₁₂".
  Qed.

  Lemma ty_le_mbang_mode_forall_intro m (τ : mode → sem_ty Σ) :
    ⊢ (∀M:[m] ν, τ ν)%T ≤T '!_[m] (∀M:[m] ν, τ ν).
  Proof.
    destruct m; simpl; first iApply ty_le_refl.
    iApply (ty_le_mbang_intro MS); iApply copy_ty_forallM.
  Qed.

  Lemma ty_le_exists (τ₁ τ₂ : sem_ty Σ → sem_ty Σ) :
    (∀ α, τ₁ α ≤T τ₂ α) -∗
    (∃: α, τ₁ α) ≤T (∃: α, τ₂ α).
  Proof.
    iIntros "#Hτ₁₂ !# %v (%α & Hα) //=".
    iExists α. by iApply "Hτ₁₂".
  Qed.

  Lemma ty_le_rec (τ₁ τ₂ : sem_ty Σ -> sem_ty Σ) `{NonExpansive τ₁, NonExpansive τ₂} :
    □ (∀ α α', (α ≤T α') -∗ τ₁ α ≤T τ₂ α') -∗
    (μT: α, τ₁ α) ≤T (μT: α, τ₂ α).
  Proof.
    iIntros "#Hτ₁₂ !#". iLöb as "IH". iIntros "%v Hτ₁".
    iApply sem_ty_rec_unfold.
    rewrite sem_ty_rec_unfold. iNext.
    iApply ("Hτ₁₂" with "[] Hτ₁").
    rewrite /ty_le /tc_opaque. iApply "IH".
  Qed.
  
  Lemma ty_le_rec_bang m (τ : sem_ty Σ -> sem_ty Σ) `{NonExpansive τ} :
    □ (∀ α, (α ≤T '!_[m] α) -∗ τ α ≤T '!_[m] (τ α)) -∗
    (μT: α, τ α) ≤T '!_[m] (μT: α, τ α).
  Proof. 
    iIntros "#H". 
    destruct m; simpl; first iApply ty_le_refl.
    iIntros "!# %v Hτα".
    iLöb as "IH" forall (v).
    rewrite {1} sem_ty_rec_unfold.
    assert (fixpoint (sem_ty_rec_pre τ) v ≡ sem_ty_rec_pre τ (fixpoint (sem_ty_rec_pre τ)) v).
    { apply non_dep_fun_equiv. apply fixpoint_unfold. }
    rewrite {4} /sem_ty_rec /sem_ty_bang H {1} /sem_ty_rec_pre.
    iApply bi.later_intuitionistically. iNext. iExists (fixpoint (sem_ty_rec_pre τ)).
    iSpecialize ("H" $! (μT: α, τ α)%T with "[IH]").
    { iIntros "% !# //". }
    iDestruct ("H" $! v with "Hτα") as "#Hτα'". iIntros "!#".
    iSplit; first done. iApply "Hτα'".
  Qed.

  Lemma ty_le_list (τ₁ τ₂ : sem_ty Σ) :
    τ₁ ≤T τ₂ -∗
    List τ₁ ≤T List τ₂.
  Proof.
    iIntros "#Hτ₁₂ !# %v HLτ₁". unfold sem_ty_list.
    iLöb as "IH" forall (v).
    iApply sem_ty_rec_unfold.
    rewrite sem_ty_rec_unfold. iNext.
    iDestruct "HLτ₁" as "(%v' & [(-> & Hunit)|(-> & (%w₁ & %w₂ & -> & Hτ₁ & Hμ))])".
    { iExists v'; iLeft. by iFrame. }
    iExists (w₁, w₂)%V. iRight. iSplit; first done.
    iExists w₁, w₂; iSplit; first done.
    iSplitL "Hτ₁"; [by iApply "Hτ₁₂"|by iApply "IH"].
  Qed.

  Lemma ty_le_list_bang m (τ : sem_ty Σ) :
    ⊢ List ('!_[m] τ) ≤T '!_[m] (List ('!_[m] τ)).
  Proof.
    rewrite /sem_ty_list /ListF. iIntros.
    iApply ty_le_rec_bang. iIntros "!# %α #Hle".
    iApply ty_le_mbang_sum_intro.
    { iApply ty_le_mbang_intro. iApply copy_ty_unit. }
    iApply (ty_le_mbang_prod_intro with "[] Hle").
    iApply ty_le_mbang_idemp_intro.
  Qed.
  
End sub_typing.
