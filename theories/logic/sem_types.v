
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

Global Instance sem_ty_inhabited {Σ} : Inhabited (sem_ty Σ) := populate sem_ty_void. 

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
Definition sem_ty_arr `{heapGS Σ} 
  (ρ : sem_row Σ)
  (τ : sem_ty Σ)
  (κ : sem_ty Σ) : sem_ty Σ :=
  (λ (v : val),
    ∀ (w : val),
      τ w -∗ 
      EWPW (v w) <| ρ |> {{ u, κ u}})%I.

(* Polymorphic type. *)
Definition sem_ty_forall {Σ} 
    (C : sem_ty Σ → sem_ty Σ) : sem_ty Σ := (λ v, ∀ τ, C τ v)%I.

(* Polymorphic effect type. *)
Definition sem_ty_row_forall {Σ} 
  (A : sem_row Σ → sem_ty Σ) : sem_ty Σ := (λ v, ∀ θ, A θ v)%I.

(* Polymorphic type. *)
Definition sem_ty_mode_forall {Σ} 
  (C : mode → sem_ty Σ) : sem_ty Σ := (λ v, ∀ ν, C ν v)%I.

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

Notation "'∀T:' α , C " := (sem_ty_forall (λ α, C%T)) 
  (at level 180) : sem_ty_scope.

Notation "'∀R:' θ , C " := (sem_ty_row_forall (λ θ, C%T)) 
  (at level 180) : sem_ty_scope.

Notation "'∀M:' ν , C " := (sem_ty_mode_forall (λ ν, C%T)) 
  (at level 180) : sem_ty_scope.

Notation "'∃:' α , C " := (sem_ty_exists (λ α, C%T)) 
  (at level 180) : sem_ty_scope.

Notation "'μT:' α , C " := (sem_ty_rec (λ α, C%T))
  (at level 180) : sem_ty_scope.

Notation "τ ⊸ κ" := (sem_ty_arr ⟨⟩%R τ%T κ%T)
  (at level 99, κ at level 200) : sem_ty_scope.

Notation "τ '-{' ρ '}-[' m ']->' κ" := ('!_[ m ] (sem_ty_arr ρ%R τ%T κ%T))%T
  (at level 100, m, ρ, κ at level 200) : sem_ty_scope.

Notation "τ '-[' m ']->' κ" := ('!_[ m ] (sem_ty_arr ⟨⟩%R τ%T κ%T))%T
  (at level 100, m, κ at level 200) : sem_ty_scope.

Notation "τ '-{' ρ '}-∘' κ" := (sem_ty_arr ρ%R τ%T κ%T)
  (at level 100, ρ, κ at level 200) : sem_ty_scope.
Notation "τ ⊸ κ" := (sem_ty_arr ⟨⟩%R τ%T κ%T)
  (at level 99, κ at level 200) : sem_ty_scope.

Notation "τ '-{' ρ '}->' κ" := (sem_ty_bang (sem_ty_arr ρ%R τ%T κ%T))
  (at level 100, ρ, κ at level 200) : sem_ty_scope.
Notation "τ → κ" := (sem_ty_bang (sem_ty_arr ⟨⟩%R τ%T κ%T))
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
           sem_ty_prod, sem_ty_sum, sem_ty_arr,
           sem_ty_ref, sem_ty_ref_cpy, 
           sem_ty_rec, sem_ty_list, sem_ty_forall, sem_ty_exists;
    repeat (f_equiv || done || intros ? || by apply non_dep_fun_dist).

  Global Instance sem_ty_bang_ne : NonExpansive (@sem_ty_bang Σ).
  Proof. solve_non_expansive. Qed.

  Global Instance sem_ty_prod_ne : NonExpansive2 (@sem_ty_prod Σ).
  Proof. solve_non_expansive. Qed.

  Global Instance sem_ty_sum_ne : NonExpansive2 (@sem_ty_sum Σ).
  Proof. solve_non_expansive. Qed.

  Global Instance sem_ty_arr_ne : NonExpansive3 sem_ty_arr.
  Proof. solve_non_expansive. Qed.

  Global Instance sem_ty_ref_ne : NonExpansive (@sem_ty_ref Σ _).
  Proof. solve_non_expansive. Qed.

  Global Instance sem_ty_ref_cpy_ne : NonExpansive (@sem_ty_ref_cpy Σ _).
  Proof. solve_non_expansive. Qed.

  Global Instance sem_ty_forall_ne n :
    Proper (pointwise_relation _ (dist n) ==> dist n) (@sem_ty_forall Σ).
  Proof.
    intros ????. unfold sem_ty_forall; repeat f_equiv. 
    by apply non_dep_fun_dist.
  Qed.

  Global Instance sem_ty_forall_row_ne n :
    Proper (pointwise_relation _ (dist n) ==> dist n) (@sem_ty_row_forall Σ).
  Proof.
    intros ????. unfold sem_ty_row_forall; repeat f_equiv.
    by apply non_dep_fun_dist.
  Qed.

  Global Instance sem_ty_forall_mode_ne n :
    Proper (pointwise_relation _ (dist n) ==> dist n) (@sem_ty_mode_forall Σ).
  Proof.
    intros ????. unfold sem_ty_mode_forall; repeat f_equiv. 
    by apply non_dep_fun_dist.
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

  Global Instance sem_ty_arr_proper : Proper ((≡) ==> (≡) ==> (≡) ==> (≡)) sem_ty_arr.
  Proof. solve_non_expansive. Qed.

  Global Instance sem_ty_ref_proper : Proper ((≡) ==> (≡)) (@sem_ty_ref Σ _).
  Proof. intros ????. unfold sem_ty_ref; by repeat f_equiv. Qed.

  Global Instance sem_ty_ref_cpy_proper : Proper ((≡) ==> (≡)) (@sem_ty_ref_cpy Σ _).
  Proof. intros ????. unfold sem_ty_ref_cpy; by repeat f_equiv. Qed.

  Global Instance sem_ty_forall_proper :
    Proper (pointwise_relation _ (≡) ==> (≡)) (@sem_ty_forall Σ).
  Proof. 
    intros ????. unfold sem_ty_forall; repeat f_equiv. 
    by apply non_dep_fun_equiv. 
  Qed.

  Global Instance sem_ty_row_forall_proper :
    Proper (pointwise_relation _ (≡) ==> (≡)) (@sem_ty_row_forall Σ).
  Proof. 
    intros ????. unfold sem_ty_row_forall; repeat f_equiv. 
    by apply non_dep_fun_equiv. 
  Qed.

  Global Instance sem_ty_mode_forall_proper :
    Proper (pointwise_relation _ (≡) ==> (≡)) (@sem_ty_mode_forall Σ).
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

  Global Instance sem_ty_forall_type_persistent `{heapGS Σ} (C : sem_ty Σ → sem_ty Σ) v :
    (∀ τ w, Persistent (C τ w)) →
    Persistent ((sem_ty_forall C) v). 
  Proof.
    unfold sem_ty_forall. simpl. apply _.
  Qed.

  Global Instance sem_ty_row_forall_persistent `{heapGS Σ} (C : sem_row Σ → sem_ty Σ) v :
    (∀ τ w, Persistent (C τ w)) →
    Persistent ((sem_ty_row_forall C) v).
  Proof.
    unfold sem_ty_row_forall. simpl. apply _.
  Qed.

  Global Instance sem_ty_mode_forall_persistent `{heapGS Σ} (C : mode → sem_ty Σ) v :
    (∀ τ w, Persistent (C τ w)) →
    Persistent ((sem_ty_mode_forall C) v).
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
  Proof. apply copy_ty_bang. Qed.
  
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

  Lemma copy_ty_forallT (C : _ → sem_ty Σ) :
    (∀ α, copy_ty (C α)) -∗ copy_ty (∀T: α, C α).
  Proof. iIntros "#H !# % HC /= %T". by iApply "H". Qed.

  Lemma copy_ty_forallR (C : _ → sem_ty Σ) :
    (∀ θ, copy_ty (C θ)) -∗ copy_ty (∀R: θ, C θ).
  Proof. iIntros "#H !# % HC /= %T". by iApply "H". Qed.

  Lemma copy_ty_forallM (C : _ → sem_ty Σ) :
    (∀ ν, copy_ty (C ν)) -∗ copy_ty (∀M: ν, C ν).
  Proof. iIntros "#H !# % HC /= %T". by iApply "H". Qed.

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

  Lemma ty_le_bang_elim (τ : sem_ty Σ) :
    ⊢ ('! τ) ≤T τ.
  Proof. iIntros "!# %v #$". Qed.


  Lemma ty_le_mbang_elim (m : mode) (τ : sem_ty Σ) :
    ⊢ ('!_[m] τ) ≤T τ.
  Proof. destruct m; first iApply ty_le_refl. iApply ty_le_bang_elim. Qed.

  Lemma ty_le_bang_comp (τ1 τ2 : sem_ty Σ) :
    τ1 ≤T τ2 -∗ ('! τ1) ≤T ('! τ2).
  Proof. iIntros "#Hττ' !# %v #H!τ !#". by iApply "Hττ'". Qed.

  Lemma ty_le_mbang_comp m (τ τ' : sem_ty Σ) :
    τ ≤T τ' -∗ ('!_[m] τ) ≤T ('!_[m] τ').
  Proof. iIntros "#Hττ'". destruct m; [done|by iApply ty_le_bang_comp]. Qed.

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

  Lemma ty_le_arr (τ₁ κ₁ τ₂ κ₂ : sem_ty Σ) (ρ ρ' : sem_row Σ) :
    ρ ≤R ρ' -∗
    τ₂ ≤T τ₁ -∗
    κ₁ ≤T κ₂ -∗
    (τ₁ -{ ρ }-∘ κ₁) ≤T (τ₂ -{ ρ' }-∘ κ₂).
  Proof.
    iIntros "#Hρ  #Hτ₂₁ #Hκ₁₂ !# %v Hτκ₁". 
    rewrite /sem_ty_arr /=. iIntros "% Hτ₂".
    iApply (ewpw_sub with "Hρ").
    iApply (ewpw_mono with "[Hτκ₁ Hτ₂]").
    { iApply ("Hτκ₁" with "[Hτ₂]"); by iApply "Hτ₂₁". }
    iIntros "!# % Hκ !>". by iApply "Hκ₁₂".
  Qed.

  Lemma ty_le_uarr (τ₁ κ₁ τ₂ κ₂ : sem_ty Σ) (ρ ρ' : sem_row Σ) :
    ρ ≤R ρ' -∗
    τ₂ ≤T τ₁ -∗
    κ₁ ≤T κ₂ -∗
    (τ₁ -{ ρ }-> κ₁) ≤T (τ₂ -{ ρ' }-> κ₂).
  Proof.
    iIntros "#Hρ  #Hτ₂₁ #Hκ₁₂". iApply ty_le_bang_comp. by iApply ty_le_arr.
  Qed.
      
  Lemma ty_le_u2aarr (τ κ : sem_ty Σ) (ρ : sem_row Σ) :
    ⊢ (τ -{ ρ }-> κ) ≤T (τ -{ ρ }-∘ κ).
  Proof. apply ty_le_bang_elim. Qed.

  Lemma ty_le_aarr (τ₁ κ₁ τ₂ κ₂ : sem_ty Σ) (ρ ρ' : sem_row Σ) :
    ρ ≤R ρ' -∗
    τ₂ ≤T τ₁ -∗
    κ₁ ≤T κ₂ -∗
    (τ₁ -{ ρ }-∘ κ₁) ≤T (τ₂ -{ ρ' }-∘ κ₂).
  Proof.
    iIntros "#Hρ  #Hτ₂₁ #Hκ₁₂ !# %v Hτκ₁". 
    rewrite /sem_ty_arr /=. iIntros "% Hτ₂".
    iApply (ewpw_sub with "Hρ").
    iApply (ewpw_mono with "[Hτκ₁ Hτ₂]").
    { iApply ("Hτκ₁" with "[Hτ₂]"); by iApply "Hτ₂₁". }
    iIntros "!# % Hκ !>". by iApply "Hκ₁₂".
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

  Lemma ty_le_forall (τ₁ τ₂ : sem_ty Σ → sem_ty Σ) :
    (∀ α, τ₁ α ≤T τ₂ α) -∗
    (∀T: α, τ₁ α)%T ≤T (∀T: α, τ₂ α).
  Proof. iIntros "#Hτ₁₂ !# %v Hτ₁ %τ /=". by iApply "Hτ₁₂". Qed.

  Lemma ty_le_bang_forall (τ : sem_ty Σ → sem_ty Σ) :
    ⊢ (∀T: α, '! (τ α))%T ≤T '! (∀T: α, τ α).
  Proof. iIntros "!# %v #Hτ !> %σ". iApply "Hτ". Qed.

  Lemma ty_le_forall_bang (τ : sem_ty Σ → sem_ty Σ) :
    ⊢ '! (∀T: α, τ α) ≤T (∀T: α, '! (τ α))%T.
  Proof. iIntros "!# %v #Hτ %σ !>". iApply "Hτ". Qed.

  Lemma ty_le_row_forall (τ₁ τ₂ : sem_row Σ → sem_ty Σ) :
    (∀ θ, τ₁ θ ≤T τ₂ θ) -∗
    (∀R: θ, τ₁ θ) ≤T (∀R: θ, τ₂ θ).
  Proof. iIntros "#Hτ₁₂ !# %v Hτ₁ %τ /=". by iApply "Hτ₁₂". Qed.

  Lemma ty_le_bang_row_forall (τ : sem_row Σ → sem_ty Σ) :
    ⊢ (∀R: θ, '! (τ θ))%T ≤T '! (∀R: θ, τ θ).
  Proof. iIntros "!# %v #Hτ !> %θ". iApply "Hτ". Qed.
  Lemma ty_le_row_forall_bang (τ : sem_row Σ → sem_ty Σ) :
    ⊢ '! (∀R: θ, τ θ) ≤T (∀R: θ, '! (τ θ))%T.
  Proof. iIntros "!# %v #Hτ %θ !>". iApply "Hτ". Qed.

  Lemma ty_le_mode_forall (τ₁ τ₂ : mode → sem_ty Σ) :
    (∀ ν, τ₁ ν ≤T τ₂ ν) -∗
    (∀M: ν, τ₁ ν) ≤T (∀M: ν, τ₂ ν).
  Proof. iIntros "#Hτ₁₂ !# %v Hτ₁ %τ /=". by iApply "Hτ₁₂". Qed.

  Lemma ty_le_bang_mode_forall (τ : mode → sem_ty Σ) :
    ⊢ (∀M: ν, '! (τ ν))%T ≤T '! (∀M: ν, τ ν).
  Proof. iIntros "!# %v #Hτ !> %ν". iApply "Hτ". Qed.
  Lemma ty_le_mode_forall_bang (τ : mode → sem_ty Σ) :
    ⊢ '! (∀M: ν, τ ν) ≤T (∀M: ν, '! (τ ν))%T.
  Proof. iIntros "!# %v #Hτ %ν !>". iApply "Hτ". Qed.

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
