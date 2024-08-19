
(* sem_row.v *)

(* This file contains the definition of semantic rows. *)

From iris.proofmode Require Import base tactics.
From iris.algebra Require Import ofe gmap.
From iris.base_logic Require Export iprop upred invariants.

From hazel.program_logic Require Import protocols.

(* Local imports *)
From affect.lib Require Import logic.
From affect.lang Require Import affect.
From affect.logic Require Import sem_def.
From affect.logic Require Import mode.
From affect.logic Require Import sem_sig.

(* Nil Row *)
Program Definition sem_row_nil {Σ} : sem_row Σ := @SemRow Σ ⊥ _. 
Next Obligation. iIntros (???) "[]". Qed.

Global Instance sem_row_bottom {Σ} : Bottom (sem_row Σ) := sem_row_nil.

(* Cons Row *)
Program Definition sem_row_cons {Σ} (op : operation) : sem_sig Σ -d> sem_row Σ -d> sem_row Σ :=
    λ σ ρ, (@SemRow Σ (@PMonoProt Σ (IEff 
              (λ v, λne Φ, ∃ (op' : operation) (v' : val), 
                           ⌜ v = (effect op', v')%V ⌝ ∗
                            if decide (op = op') then 
                                ▷ (iEff_car σ v' Φ)
                            else
                                iEff_car ρ (effect op', v')%V Φ)%I) _) _).
Next Obligation. 
  intros ?????????. repeat f_equiv; last done. simpl. 
  destruct a0; by repeat f_equiv. 
Qed.
Next Obligation. 
  iIntros (???????) "#HPost (%op' & %v' & -> & H)". simpl.
  iExists op', v'. iSplit; first done.
  destruct (decide (op = op')).
  - iApply (pmono_prot_prop Σ σ with "HPost H").
  - iApply (pmono_prot_prop Σ ρ with "HPost H").
Qed.
Next Obligation.
  iIntros (??????) "(%op' & %v' & -> & H)". by iExists op', v'.
Qed.

(* Recursive Row *)
Definition sem_row_rec {Σ} (R : sem_row Σ → sem_row Σ) `{Contractive R} : sem_row Σ :=
  fixpoint R.

Lemma sem_row_rec_unfold {Σ} (R : sem_row Σ → sem_row Σ) `{Contractive R} :
  sem_row_rec R ≡ R (sem_row_rec R).
Proof. rewrite /sem_row_rec {1} fixpoint_unfold //. Qed.

Lemma sem_row_rec_unfold_iEff {Σ} (R : sem_row Σ → sem_row Σ) `{Contractive R} v Φ:
  iEff_car (sem_row_rec R) v Φ ≡ iEff_car (R (sem_row_rec R)) v Φ.
Proof. f_equiv. apply non_dep_fun_equiv. rewrite {1}sem_row_rec_unfold //. Qed.

(* Flip-Bang Row *)
Program Definition sem_row_flip_mbang {Σ} (m : mode) (ρ : sem_row Σ) : sem_row Σ := 
  @SemRow Σ (@PMonoProt Σ (upcl m ρ) _) _.
Next Obligation.
  iIntros (??????) "#HΦ Hσ". 
  destruct m.
  - pose proof (upcl_mono_prot ρ) as []. 
    iApply (monotonic_prot with "HΦ Hσ").
  - pose proof (pers_upcl_pers_mono_prot ρ) as [].
    iApply (pers_monotonic_prot with "HΦ Hσ").
Qed.
Next Obligation.
  iIntros (?????) "(%Φ' & Hρ & _)".
  iApply (sem_row_prop _ ρ with "Hρ").
Qed.

(* Notations. *)
Notation "⟨⟩" := (sem_row_nil) : sem_row_scope.
Notation "opσ · ρ" := (sem_row_cons opσ.1%S opσ.2%S ρ%R) (at level 80, right associativity) : sem_row_scope.
Notation "¡[ m ] ρ" := (sem_row_flip_mbang m ρ) (at level 10) : sem_row_scope.
Notation "¡ ρ" := (sem_row_flip_mbang OS ρ) (at level 10) : sem_row_scope.
Notation "'μᵣ' θ , ρ " := (sem_row_rec (λ θ, ρ%R)) (at level 50) : sem_row_scope.

Section row_properties.

  Global Instance sem_row_cons_ne {Σ} op : NonExpansive2 (@sem_row_cons Σ op).
  Proof. 
    intros ???????. rewrite /sem_row_cons. 
    intros ??. simpl. do 7 f_equiv; first f_equiv; apply non_dep_fun_dist; by f_equiv.  
  Qed.
  Global Instance sem_row_cons_Proper {Σ} op : Proper ((≡) ==> (≡) ==> (≡)) (@sem_row_cons Σ op).
  Proof. apply ne_proper_2. apply _. Qed.
  
  Global Instance sem_row_cons_contractive {Σ} op n : Proper (dist_later n ==> dist n ==> dist n) (@sem_row_cons Σ op).
  Proof. 
    intros ???????. rewrite /sem_row_cons. 
    intros ?. simpl. do 6 f_equiv; first f_contractive; f_equiv; apply non_dep_fun_dist; by f_equiv.
  Qed.
  
  Global Instance sem_row_flip_mbang_ne {Σ} m : NonExpansive (@sem_row_flip_mbang Σ m).
  Proof. intros ?????. rewrite /sem_row_flip_mbang. intros ?. simpl. 
         do 4 f_equiv. apply non_dep_fun_dist; by f_equiv. Qed.
  Global Instance sem_row_flip_bang_Proper {Σ} m : Proper ((≡) ==> (≡)) (@sem_row_flip_mbang Σ m).
  Proof. apply ne_proper. apply _. Qed.
  
  Global Instance sem_row_flip_mbang_rec_contractive {Σ} m (R : sem_row Σ -d> sem_row Σ) `{Contractive R} : 
    Contractive (λ θ, sem_row_flip_mbang m (R θ)).
  Proof.
    intros ??????. rewrite /sem_row_flip_mbang. simpl.
    do 4 f_equiv. apply non_dep_fun_dist. by apply Contractive0.
  Qed. 

End row_properties.

Section once_row.

  (* Once Constraint *)
  
  Class OnceR {Σ} (ρ : sem_row Σ) := {
    row_le_mfbang_elim : (⊢ (¡ ρ%R) ≤ᵣ ρ%R)
  }.
  
  Global Instance monoprot_once {Σ} (ρ : sem_row Σ) `{! OnceR ρ } : MonoProt ρ.
  Proof.
    constructor. iIntros (???) "HP Hρ".
    inv OnceR0. iApply row_le_mfbang_elim0.
    iExists Φ. simpl. iFrame.
  Qed.

End once_row.

Section row_sub_typing.

  (* Subtyping on Rows *)
  
  Lemma row_le_refl {Σ} (ρ : sem_row Σ) :
    ⊢ ρ ≤ᵣ ρ.
  Proof. iApply iEff_le_refl. Qed.
  
  Lemma row_le_trans {Σ} (ρ₁ ρ₂ ρ₃ : sem_row Σ) :
    ρ₁ ≤ᵣ ρ₂ -∗ 
    ρ₂ ≤ᵣ ρ₃ -∗
    ρ₁ ≤ᵣ ρ₃.
  Proof. iApply iEff_le_trans. Qed.
  
  Lemma row_le_nil {Σ} (ρ : sem_row Σ) : 
    ⊢ ⟨⟩ ≤ᵣ ρ.
  Proof. iApply iEff_le_bottom. Qed.
  
  Lemma row_le_cons_comp {Σ} (ρ ρ' : sem_row Σ) (op : operation) (σ σ' : sem_sig Σ) : 
    σ ≤ₛ σ' -∗ ρ ≤ᵣ ρ' -∗ 
    (op, σ) · ρ ≤ᵣ (op, σ') · ρ'.
  Proof.
    iIntros "#Hσσ' #Hρρ'". rewrite /sem_row_cons /=. 
    iIntros (??) "!# (%op' & %v' & -> & H)".
    iExists op', v'; iSplit; first done.
    destruct (decide (op = op')); first (by iApply "Hσσ'"). 
    by iApply "Hρρ'".
  Qed.
  
  Lemma row_le_swap_second {Σ} (op op' : operation) (σ σ' : sem_sig Σ) (ρ : sem_row Σ) : 
    op ≠ op' →
    ⊢ (op, σ) · (op', σ') · ρ ≤ᵣ (op', σ') · (op, σ) · ρ. 
  Proof. 
    iIntros (Hneq). rewrite /sem_row_cons /=.
    iIntros (??) "!# (%op'' & %v'' & %Heq & H)". simpl.
    destruct (decide (op = op'')) as [->|].
    - iExists op'', v''. iSplit; first done.
      rewrite decide_False; last done.
      iExists op'', v''; iSplit; first done.
      rewrite decide_True //.
    - iDestruct "H" as "(%op''' & %v''' & %Heq' & H)".
      destruct (decide (op' = op''')) as [->|].
      + iExists op'', v''; iSplit; first done.
        simplify_eq. rewrite decide_True //.
      + iExists op''', v''; iSplit; first by simplify_eq.
        simplify_eq. rewrite decide_False //.
        iExists op''', v'''. iSplit; first done.
        rewrite decide_False //.
  Qed.
  
  Corollary row_le_swap_third {Σ} (op op' op'' : operation) (σ σ' σ'' : sem_sig Σ) (ρ : sem_row Σ) : 
    op ≠ op' → op' ≠ op'' → op'' ≠ op →
    ⊢ (op, σ) · (op', σ') · (op'', σ'') · ρ ≤ᵣ (op'', σ'') · (op, σ) · (op', σ') · ρ. 
  Proof. 
    iIntros (???). 
    iApply row_le_trans; first iApply row_le_cons_comp; [iApply sig_le_refl|by iApply row_le_swap_second|].
    by iApply row_le_swap_second.
  Qed.
  
  Corollary row_le_swap_fourth {Σ} (op op' op'' op''' : operation) (σ σ' σ'' σ''': sem_sig Σ) (ρ : sem_row Σ) : 
    op ≠ op' → op ≠ op'' → op ≠ op''' → op' ≠ op'' → op' ≠ op''' → op'' ≠ op''' → 
    ⊢ (op, σ) · (op', σ') · (op'', σ'') · (op''', σ''') · ρ ≤ᵣ 
      (op''', σ''') · (op, σ) · (op', σ') · (op'', σ'') · ρ.
  Proof. 
    iIntros (??????). 
    iApply row_le_trans; first iApply row_le_cons_comp; [iApply sig_le_refl|by iApply row_le_swap_third|].
    by iApply row_le_swap_second.
  Qed.
  
  Lemma row_le_rec_unfold {Σ} (R : sem_row Σ → sem_row Σ) `{Contractive R} :
    ⊢ (μᵣ θ, R θ) ≤ᵣ R (μᵣ θ, R θ).
  Proof. rewrite {1} sem_row_rec_unfold //. iApply row_le_refl. Qed.
  
  Lemma row_le_rec_fold {Σ} (R : sem_row Σ → sem_row Σ) `{ Contractive R }:
    ⊢ R (μᵣ θ, R θ) ≤ᵣ (μᵣ θ, R θ).
  Proof. rewrite - {1} sem_row_rec_unfold. iApply row_le_refl. Qed.
  
  Lemma row_le_mfbang_intro {Σ} (m : mode) (ρ : sem_row Σ) :
    ⊢ ρ ≤ᵣ ¡[ m ] ρ. 
  Proof. 
    rewrite /sem_row_flip_mbang. iIntros (??) "!# Hρ". simpl.
    iExists Φ. iFrame. iApply bi.intuitionistically_intuitionistically_if. 
    iIntros "!# % $ //".
  Qed.
  
  Lemma row_le_mfbang_elim_ms {Σ} (ρ : sem_row Σ) :
    ⊢ ¡[MS] ρ ≤ᵣ ρ. 
  Proof. 
    rewrite /sem_sig_flip_mbang. 
    iIntros (v Φ) "!# (%Φ' & Hρ & HPost)". simpl.
    by iApply (@pmono_prot_prop Σ ρ with "HPost").
  Qed.
  
  Lemma row_le_mfbang_comp {Σ} m m' (ρ ρ' : sem_row Σ) :
    m' ≤ₘ m -∗ ρ ≤ᵣ ρ' -∗
    (¡[m] ρ) ≤ᵣ (¡[m'] ρ').
  Proof. 
    iIntros "#Hlem #Hleσ". destruct m.
    - iDestruct (mode_le_OS_inv with "Hlem") as "->".
      rewrite /row_le /sem_row_flip_mbang /tc_opaque.
      by iApply iEff_le_upcl.
    - iApply row_le_trans; first iApply row_le_mfbang_elim_ms. 
      iApply row_le_trans; first iApply (row_le_mfbang_intro m').
      rewrite /row_le /sem_row_flip_mbang /tc_opaque.
      by iApply iEff_le_upcl.
  Qed.
  
  Lemma row_le_mfbang_elim_cons {Σ} op m σ (ρ : sem_row Σ) :
    ⊢ ¡[ m ] ((op, σ) · ρ) ≤ᵣ (op, ¡[ m ] σ)%S · (¡[ m ] ρ).
  Proof. 
    rewrite /sem_row_flip_mbang. 
    iIntros (??) "!# (%Φ' & (%op' & %v' & -> & H) & Hpost)". simpl.
    iExists op', v'. iSplit; first done.
    destruct (decide (op = op')); first iNext; iExists Φ'; iFrame. 
  Qed.

  Global Instance row_cons_once {Σ} (ρ : sem_row Σ) op (σ : sem_sig Σ) `{! OnceS σ, ! OnceR ρ } :
    OnceR ((op, σ) · ρ)%R.
  Proof.
    constructor. inv OnceS0. inv OnceR0.
    iApply row_le_trans; first iApply row_le_mfbang_elim_cons.
    iApply row_le_cons_comp; [iApply sig_le_mfbang_elim|iApply row_le_mfbang_elim0].
  Qed.
  
  Lemma row_le_mfbang_idemp {Σ} m (ρ : sem_row Σ) :
    ⊢ (¡[ m ] (¡[ m ] ρ)) ≤ᵣ ((¡[ m ] ρ)).
  Proof. 
    iIntros (v Φ) "!# (%Φ' & (%Φ'' & H & HPost') & HPost)". 
    rewrite /sem_row_flip_mbang /=.
    iDestruct (bi.intuitionistically_if_sep_2 with "[HPost HPost']") as "HP"; first iFrame.
    iExists Φ''. iFrame.
    iApply (bi.intuitionistically_if_mono with "HP").
    iIntros "[H1 H2] % HΦ''". iApply ("H2" with "[H1 HΦ'']"). 
    by iApply "H1".
  Qed.

  Global Instance row_fbang_once {Σ} (ρ : sem_row Σ) : OnceR (¡ ρ)%R.
  Proof. constructor. iApply row_le_mfbang_idemp. Qed.
  
  Lemma row_le_mfbang_comm {Σ} m m' (ρ : sem_row Σ) :
    ⊢ (¡[ m ] (¡[ m' ] ρ)) ≤ᵣ (¡[ m' ] (¡[ m ] ρ)).
  Proof. 
    destruct m, m'.
    - iApply row_le_refl.
    - iApply row_le_trans; first iApply row_le_mfbang_comp.
      { iApply mode_le_refl. }
      { iApply row_le_mfbang_elim_ms. }
      iApply row_le_mfbang_intro.
    - iApply row_le_trans; first iApply row_le_mfbang_elim_ms.
      iApply row_le_mfbang_comp; first iApply mode_le_refl. iApply row_le_mfbang_intro.
    - iApply row_le_refl.
  Qed.
  
  Lemma row_le_mfbang_elim_nil {Σ} m :
     ⊢ ¡[m] ⟨⟩%R ≤ᵣ (⟨⟩%R : sem_row Σ).
  Proof. 
    destruct m; simpl; last iApply row_le_mfbang_elim_ms.
    iIntros (??) "!# (% & [] & _)".
  Qed.
  
  Global Instance row_nil_once {Σ} : OnceR (⟨⟩ : sem_row Σ)%R.
  Proof. constructor. iApply row_le_mfbang_elim_nil. Qed.
  
  Lemma row_le_mfbang_elim_rec {Σ} (m : mode) (R : sem_row Σ → sem_row Σ) `{ Contractive R }: 
    (∀ θ, ¡[ m ] (R θ) ≤ᵣ (R θ)) -∗ ¡[ m ] (μᵣ θ, R θ) ≤ᵣ (μᵣ θ, R θ).
  Proof. 
    iIntros "#Hle". destruct m; last iApply row_le_mfbang_elim_ms.
    iIntros (??) "!# (%Φ' & H & HP)". simpl.
    iApply sem_row_rec_unfold_iEff. rewrite sem_row_rec_unfold_iEff.
    iApply "Hle". iExists Φ'. simpl. iFrame.
  Qed.
  
  Global Instance row_rec_once {Σ} (R : sem_row Σ → sem_row Σ) `{Contractive R} :
    (∀ θ, OnceR (R θ)) → OnceR (μᵣ θ, R θ)%R.
  Proof.
    intros H. constructor. 
    iApply row_le_mfbang_elim_rec. iIntros (θ). 
    destruct (H θ). iApply row_le_mfbang_elim0.
  Qed.

End row_sub_typing.
  
Section row_type_sub.

  (* Substructurality relation on rows wrt to types and environments *)
  
  Definition mono_prot_on_prop {Σ} (Ψ : iEff Σ) (P : iProp Σ) : iProp Σ :=
    □ (∀ v Φ, iEff_car Ψ v Φ -∗ P -∗ iEff_car Ψ v (λ w, Φ w ∗ P))%I.
  
  (* For semantic signatures, being monotonic on all propositions is the same as being monotonic
     because semantic signatures are persistently monotonic by definition *)
  Lemma mono_prot_on_prop_monotonic {Σ} (σ : sem_sig Σ) : 
    (⊢ ∀ P, mono_prot_on_prop σ P) ↔ MonoProt σ.
  Proof.
    split.
    - iIntros (H). constructor. iIntros (v Φ Φ') "Hpost HΨ".
      iDestruct (H with "HΨ Hpost") as "H".
      iApply (pmono_prot_prop _ σ with "[] H").
      { iIntros "!# % [HΦ HPost]". by iApply "HPost". }
    - iIntros (H) "%P %v %Φ !# Hσ HP". inv H.
      iApply (monotonic_prot with "[HP] Hσ"). iIntros (?) "$ //".
  Qed.
  
  Class RowTypeSub {Σ} (ρ : sem_row Σ) (τ : sem_ty Σ) := {
    row_type_sub : ⊢ (∀ v, mono_prot_on_prop ρ (τ v))
  }.
  
  Global Instance row_type_sub_once {Σ} (ρ : sem_row Σ) (τ : sem_ty Σ) `{! OnceR ρ} : RowTypeSub ρ τ.
  Proof.
    constructor.
    iIntros (w v Φ) "!# Hρ Hτ". 
    iApply (monotonic_prot v Φ (λ w', Φ w' ∗ τ w)%I with "[Hτ] Hρ").
    iIntros "% $ //".
  Qed.
  
End row_type_sub.

Section row_env_sub.

  Class RowEnvSub {Σ} (ρ : sem_row Σ) (Γ : env Σ) := {
    row_env_sub : ⊢ (∀ γ, mono_prot_on_prop ρ (Γ ⊨ₑ γ))
  }.
  
  Global Instance row_env_sub_once {Σ} (ρ : sem_row Σ) (Γ : env Σ) `{! OnceR ρ} : RowEnvSub ρ Γ.
  Proof.
    constructor.
    iIntros (γ v Φ) "!# Hρ HΓ".
    iApply (monotonic_prot v Φ (λ w', Φ w' ∗ Γ ⊨ₑ γ)%I with "[HΓ] Hρ").
    iIntros "% $ //".
  Qed.
  
End row_env_sub.

(* Notations *)
Notation "ρ ᵣ⪯ₑ Γ" := (RowEnvSub ρ%R Γ%T) (at level 80).
Notation "ρ ᵣ⪯ₜ τ" := (RowTypeSub ρ%R τ%T)%I (at level 80).
