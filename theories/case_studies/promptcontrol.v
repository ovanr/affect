From stdpp Require Import base list.
From iris.proofmode Require Import base tactics.
From iris.algebra Require Import excl_auth.


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
From haffel.logic Require Import sem_env.
From haffel.logic Require Import sem_sig.
From haffel.logic Require Import sem_row.
From haffel.logic Require Import sem_types.
From haffel.logic Require Import ewpw.
From haffel.logic Require Import sem_judgement.
From haffel.logic Require Import copyable.
From haffel.logic Require Import sem_operators.
From haffel.logic Require Import compatibility.
From haffel.logic Require Import tactics.

Definition deep_try_alt_ls : val := (
  rec: "H" "e" "l" "h" "r" :=
    shallow_try_ls "e" "l" (λ: "x" "k", "H" (λ: <>, "h" "x" "k") "l" "h" "r") "r"
)%V.

Arguments deep_try_alt_ls : simpl never.

Definition DeepTryAltLS (e : expr) (l : label) (h r : expr) : expr :=
  deep_try_alt_ls (λ: <>, e)%E (effect l)%V h r.

Definition DeepTryAltLSV (e : expr) (l : label) (h r : expr) : expr :=
  deep_try_alt_ls (λ: <>, e)%V (effect l)%V h r.

Notation "'deep-try-alt-ls:' e 'handle' l 'with' 'effect' h | 'return' r 'end'" :=
  (DeepTryAltLS e l h r)
  (e, l, h, r at level 200, only parsing) : expr_scope.

Definition control : val := (Λ: Λ: λ: "f", perform: (effect "ctrl", "f"))%V.
Definition controlₘ : val := (Λ: Λ: λ: "f", performₘ: (effect "ctrl", "f"))%V.

Definition prompt : val := 
  (Λ: λ: "e", 
    deep-try-alt-ls: "e" #() handle "ctrl" with 
                effect (λ: "x" "k", "x" "k")
              | return (λ: "x", "x")
             end
  )%V.

Section deep_handler_alt.

  Context `{!heapGS Σ}.
  
  Notation deep_handler_alt_ls_type Σ :=
    (coPset -d> label-d> sem_sig Σ -d> sem_row Σ -d> mode -d> (val -d> iPropO Σ) 
            -d> expr -d> expr
            -d> sem_row Σ -d> (val -d> iPropO Σ) -d> iPropO Σ) (only parsing).
  
    (* Correctness of the effect branch. *)
  Definition deep_handler_alt_ls `{irisGS eff_lang Σ} : deep_handler_alt_ls_type Σ := (
    λ E l σ ρ m Φ h r ρ' Φ',
    
    (* Subsumption on row *)
    (ρ ≤R ρ') ∗
  
    (* One-Shot Row *)
    (⌜ m = OS → OSRow ρ ⌝) ∗
  
    (* Correctness of the return branch. *)
    □?m (
      ∀ (v : val), Φ v -∗ EWPW r v @ E <| ρ' |> {{ Φ' }}
    ) ∧
  
    (* Correctness of the effect branch. *)
    □ (
      ∀ (v k : val),
        iEff_car (upcl σ.1 σ.2) v (λ w, EWPW k w @ E <| (l, σ) ·: ρ |> {{ Φ }}) -∗
        EWPW h v k @ E <| (l, σ) ·: ρ |> {{ Φ }}
    ))%I.
  
  Lemma ewpw_deep_try_alt_ls E (l : label) m σ ρ ρ' e (h r : val) Φ Φ' :
    EWPW e @ E <| (l, σ) ·: ρ |> {{ Φ }} -∗
    deep_handler_alt_ls E l σ ρ m Φ h r ρ' Φ' -∗
    EWPW (DeepTryAltLSV e l h r) @E <| ρ' |> {{ Φ' }}.
  Proof.
    iIntros "He H". rewrite /DeepTryAltLSV. 
    iLöb as "IH" forall (e). rewrite /deep_try_alt_ls /ewpw. 
    rewrite /deep_handler_alt_ls.
    do 10 ewp_value_or_step. ewp_pure_steps. 
    iApply (ewpw_shallow_try_ls _ l m  with "He").
    iDestruct "H" as "(#H1 & %H2 & H3 & #H4)".
    rewrite /shallow_handler_ls. iFrame "#%".
    destruct m; simpl.
    - iSplit; first iApply "H3".
      iIntros (v k) "(%Φ'' & Hσ & HPost)".
      rewrite /ewpw; do 6 ewp_value_or_step. 
      rewrite -/deep_try_alt_ls. iApply ("IH" with "[Hσ HPost]").
      { iApply "H4". iExists Φ''. iFrame. }
      iFrame "#%∗".
    - iDestruct "H3" as "#H3". iIntros "!#".
      iFrame "#". iIntros (v k) "(%Φ'' & Hσ & HPost)".
      rewrite /ewpw; do 6 ewp_value_or_step. 
      rewrite -/deep_try_alt_ls. iApply ("IH" with "[Hσ HPost]").
      { iApply "H4". iExists Φ''. iFrame. }
      iFrame "#%∗".
  Qed.
  
  Lemma sem_typed_deep_try_alt_os m l A B τ τ' ρ' ρ'' Γ₁ Γ₂ Γ₃ Γ' x k e h r `{NonExpansive A, NonExpansive B}:
      x ∉ env_dom Γ₂ → x ∉ env_dom Γ' → x ∉ env_dom Γ₃ → x ∉ env_dom Γ₂ → k ∉ env_dom Γ₂ → k ∉ env_dom Γ₃ → k ∉ env_dom Γ' → x ≠ k →
      let σ := (∀S: α, A α ⇒ B α | m)%S in
      let ρ := ((l, σ) ·: ρ')%R in
      copy_env Γ' -∗
      ρ' ≤R ρ'' -∗
      Γ₁ ⊨ e : ρ : τ ⊨ Γ₂ -∗
      (∀ α, (x, A α) :: (k, B α -{ ρ }-∘ τ) :: Γ' ⊨ h : ρ : τ ⊨ Γ₂) -∗
      (x, τ) :: Γ₂ ++ Γ' ⊨ r : ρ'' : τ' ⊨ Γ₃ -∗
      Γ₁ ++ Γ' ⊨ (deep-try-alt-ls: e handle l with
                          effect  (λ: x k, h)
                        | return  (λ: x, r) end)%E : ρ'' : τ' ⊨ Γ₃.
    Proof.
      iIntros (??????????) "#Hcpy #Hle #He #Hh #Hr !# %vs HΓ₁Γ' /=".
      iDestruct (env_sem_typed_app with "HΓ₁Γ'") as "[HΓ₁ HΓ'']". 
      iDestruct ("Hcpy" with "HΓ''") as "#HΓ'". iClear "HΓ''".
      do 4 ewpw_value_or_step. iDestruct "He" as "-#He".
      iSpecialize ("He" $! vs with "HΓ₁").
      iRevert "He". iLöb as "IH" forall (e). iIntros "He".
      ewpw_pure_steps. 
      iApply (ewpw_deep_try_alt_ls _ _ MS with "He [HΓ']").
      rewrite /deep_handler_alt_ls.
      repeat iSplit; eauto. simpl. iIntros "!#". 
      - iIntros (v) "[Hτ HΓ₂]". ewpw_pure_steps. rewrite - subst_map_insert. 
        iApply (ewpw_mono with "[HΓ₂ HΓ' Hτ]").
        { iApply "Hr". solve_env. iApply env_sem_typed_app; solve_env. }
        iIntros "!# %w [$ HΓ₃] !>". solve_env.
      - iIntros (v k') "!# (%Φ & Hρ & HPost)".
        rewrite sem_sig_eff_eq. iDestruct "Hρ" as "(%α & %a & <- & Ha & Hκb)".
        ewpw_pure_steps. solve_dec. 
        rewrite delete_commute - subst_map_insert. 
        rewrite - delete_insert_ne // - subst_map_insert.
        iApply (ewpw_mono with "[Hh Ha Hκb HPost]").
        + iApply "Hh". solve_env. 
          iSplitL; last (do 2 (rewrite - env_sem_typed_insert; solve_env)).
          rewrite ! bi.intuitionistically_if_elim.
          iIntros "% HB". iApply (ewpw_mono with "[HB Hκb HPost]").
          { iApply "HPost". iApply "Hκb". by iNext. }
          iIntros "!# % [$ _] //".
        + iIntros "!# /= % [$ H] !>". do 2 (rewrite - env_sem_typed_insert //).
    Qed.
  
  Lemma sem_typed_deep_try_alt_ms l A B τ τ' ρ' ρ'' Γ₁ Γ₂ Γ₃ Γ' x k e h r `{NonExpansive A, NonExpansive B}:
      x ∉ env_dom Γ₂ → x ∉ env_dom Γ' → x ∉ env_dom Γ₃ → x ∉ env_dom Γ₂ → k ∉ env_dom Γ₂ → k ∉ env_dom Γ₃ → k ∉ env_dom Γ' → x ≠ k →
      let σ := (∀S: α, A α ⇒ B α | MS)%S in
      let ρ := ((l, σ) ·: ρ')%R in
      copy_env Γ' -∗
      ρ' ≤R ρ'' -∗
      Γ₁ ⊨ e : ρ : τ ⊨ Γ₂ -∗
      (∀ α, (x, A α) :: (k, B α -{ ρ }-> τ) :: Γ' ⊨ h : ρ : τ ⊨ Γ₂) -∗
      (x, τ) :: Γ₂ ++ Γ' ⊨ r : ρ'' : τ' ⊨ Γ₃ -∗
      Γ₁ ++ Γ' ⊨ (deep-try-alt-ls: e handle l with
                          effect  (λ: x k, h)
                        | return  (λ: x, r) end)%E : ρ'' : τ' ⊨ Γ₃.
    Proof.
      iIntros (??????????) "#Hcpy #Hle #He #Hh #Hr !# %vs HΓ₁Γ' /=".
      iDestruct (env_sem_typed_app with "HΓ₁Γ'") as "[HΓ₁ HΓ'']". 
      iDestruct ("Hcpy" with "HΓ''") as "#HΓ'". iClear "HΓ''".
      do 4 ewpw_value_or_step. iDestruct "He" as "-#He".
      iSpecialize ("He" $! vs with "HΓ₁").
      iRevert "He". iLöb as "IH" forall (e). iIntros "He".
      ewpw_pure_steps. 
      iApply (ewpw_deep_try_alt_ls _ _ MS with "He [HΓ']").
      rewrite /deep_handler_alt_ls.
      repeat iSplit; eauto. simpl. iIntros "!#". 
      - iIntros (v) "[Hτ HΓ₂]". ewpw_pure_steps. rewrite - subst_map_insert. 
        iApply (ewpw_mono with "[HΓ₂ HΓ' Hτ]").
        { iApply "Hr". solve_env. iApply env_sem_typed_app; solve_env. }
        iIntros "!# %w [$ HΓ₃] !>". solve_env.
      - iIntros (v k') "!# (%Φ & Hρ & HPost)".
        rewrite sem_sig_eff_eq. iDestruct "Hρ" as "(%α & %a & <- & Ha & Hκb)".
        ewpw_pure_steps. solve_dec. 
        rewrite delete_commute - subst_map_insert. 
        rewrite - delete_insert_ne // - subst_map_insert.
        iApply (ewpw_mono with "[Hh Ha Hκb HPost]").
        + iApply "Hh". solve_env; last (do 2 (rewrite - env_sem_typed_insert; solve_env)).
          iDestruct "Hκb" as "#Hκb". iDestruct "HPost" as "#HPost".
          iIntros "!# % HB". iApply (ewpw_mono with "[HB Hκb HPost]").
          { iApply "HPost". iApply "Hκb". by iNext. }
          iIntros "!# % [$ _] //".
        + iIntros "!# /= % [$ H] !>". do 2 (rewrite - env_sem_typed_insert //).
    Qed.

End deep_handler_alt.

Section typing.

  Context `{!heapGS Σ}.

  Definition ctrl_sig (β : sem_ty Σ) (ctrl : sem_row Σ) : label * sem_sig Σ := 
      ("ctrl", ∀S: α , (α -{ ctrl }-∘ β) -{ ctrl }-∘ β ⇒ α | OS)%S.

  Definition ctrl_pre (β : sem_ty Σ) (ctrl : sem_row Σ) : sem_row Σ := 
      (ctrl_sig β ctrl ·: ⟨⟩)%R.

  Local Instance contractive_ctrl_pre β : Contractive (ctrl_pre β).
  Proof.
    intros ????. rewrite /ctrl_pre. rewrite /sem_row_cons /= /sem_row_ins.
    intros ?. destruct (decide (i = ("ctrl", 0))) as [->|Hneg].
    - rewrite !lookup_insert. f_equiv.
      rewrite /sem_sig_eff. f_equiv. f_equiv. intros ??. 
      apply non_dep_fun_dist. do 4 f_equiv. f_contractive.
      apply non_dep_fun_dist. f_equiv; first done. 
      rewrite /sem_ty_aarr. intros ?. by do 4 f_equiv.
    - rewrite (lookup_insert_ne _ ("ctrl", 0) i _) //. 
      rewrite (lookup_insert_ne _ ("ctrl", 0) i _) //.
  Qed.

  Definition ctrl β : sem_row Σ := (μR: θ, ctrl_pre β θ)%R.

  Local Instance ctrl_sig_ne β θ : NonExpansive (λ α : sem_ty Σ, (α -{ θ }-∘ β) -{ θ}-∘ β).
  Proof. intros ????. by do 2 f_equiv. Qed.

  Local Instance ctrl_os_row β : OSRow (ctrl β).
  Proof.
    rewrite /ctrl. apply row_rec_os_row. iIntros (θ).
    rewrite /ctrl_pre. apply row_ins_os_row.
    { rewrite /ctrl_sig. apply sig_eff_os_os_sig; apply _. }
    simpl. apply row_tun_os_row. apply row_nil_os_row.
  Qed.

  Definition ctrl_ty : sem_ty Σ := 
    (∀T: α, ∀T: β, ((α -{ ctrl β }-∘ β) -{ ctrl β }-∘ β) -{ ctrl β }-> α)%T.

  Definition prompt_ty : sem_ty Σ := 
    (∀T: α, (() -{ ctrl α }-∘ α) → α)%T.

  Lemma ctrl_typed : ⊢ ⊨ᵥ control : ctrl_ty.
  Proof.
    iIntros. rewrite /control /ctrl_ty.
    iApply sem_typed_Tclosure; solve_sidecond. iIntros (α).
    rewrite - (app_nil_l []).
    iApply sem_typed_TLam; solve_sidecond. iIntros (β).
    rewrite - (app_nil_l []).
    iApply sem_typed_ufun; solve_sidecond. simpl.
    iApply sem_typed_sub_row; first iApply row_le_rec_fold.
    rewrite /ctrl_pre -/(ctrl β).
    iApply (sem_typed_perform_os α _ "ctrl" _ (λ α, α)).
    iApply sem_typed_var'.
  Qed.

  Lemma prompt_typed : ⊢ ⊨ᵥ prompt : prompt_ty.
  Proof.
    iIntros. rewrite /prompt /prompt_ty.
    iApply sem_typed_Tclosure; solve_sidecond. iIntros (β).
    rewrite - (app_nil_l []).
    iApply sem_typed_ufun; solve_sidecond. simpl.
    rewrite - (app_nil_r [("e", _)]).
    set Γ₁ := [("e", () -{ ctrl β }-∘ β)].
    iApply (sem_typed_deep_try_alt_os OS "ctrl" (λ α, (α -{ ctrl β }-∘ β) -{ ctrl β }-∘ β) (λ α,  α) β β ⟨⟩%R ⟨⟩%R Γ₁ [] [] []); solve_sidecond.  
    { iApply row_le_nil. }
    - rewrite /Γ₁. iApply sem_typed_sub_row. 
      { iApply (row_le_rec_unfold (λ θ, ctrl_pre β θ)). }
      iApply sem_typed_app_os; last iApply sem_typed_unit'.
      iApply sem_typed_var'.
    - iIntros (α). iApply sem_typed_swap_second. 
      iApply sem_typed_app_os; last iApply sem_typed_var'.
      iApply sem_typed_sub_nil.
      iApply sem_typed_sub_ty.
      + iApply ty_le_aarr; [|iApply ty_le_aarr|]; try iApply ty_le_refl;
        first iApply (row_le_rec_unfold (λ θ, ctrl_pre β θ)).
        iApply (row_le_rec_fold (λ θ, ctrl_pre β θ)).
      + iApply sem_typed_var'.
    - iApply sem_typed_var.
  Qed.

End typing.
