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
From affect.lib Require Import base.
From affect.lang Require Import affect.
From affect.logic Require Import sem_def.
From affect.logic Require Import sem_env.
From affect.logic Require Import sem_sig.
From affect.logic Require Import sem_row.
From affect.logic Require Import sem_types.
From affect.logic Require Import ewpw.
From affect.logic Require Import sem_judgement.
From affect.logic Require Import copyable.
From affect.logic Require Import sem_operators.
From affect.logic Require Import compatibility.
From affect.logic Require Import tactics.

Definition handler_alt (m : mode) : val := (
  rec: "H" "e" "op" "h" "r" :=
    shandler m "e" "op" (λ: "x" "k", "H" (λ: <>, "h" "x" "k") "op" "h" "r") "r"
)%V.

Arguments handler_alt : simpl never.

Definition HandlerAlt (m : mode) (e : expr) (op : operation) (h r : expr) : expr :=
  handler_alt m (λ: <>, e)%E (effect op) h r.

Definition HandlerAltV (m : mode) (e : expr) (op : operation) (h r : expr) : expr :=
  handler_alt m (λ: <>, e)%V (effect op) h r.

Notation "'handle-alt[' m ']:' e 'by' op '=>' h | 'ret' => r 'end'" :=
  (HandlerAlt m e op h r)
  (e, op, h, r at level 200, only parsing) : expr_scope.

Notation "'handle-alt:' e 'by' op '=>' h | 'ret' => r 'end'" :=
  (HandlerAlt OS e op h r)
  (e, op, h, r at level 200, only parsing) : expr_scope.

Notation "'handle-altₘ:' e 'by' op '=>' h | 'ret' => r 'end'" :=
  (HandlerAlt MS e op h r)
  (e, op, h, r at level 200, only parsing) : expr_scope.

Definition control : val := (Λ: Λ: λ: "f", perform: "ctrl" "f")%V.

Definition prompt : val := 
  (Λ: λ: "e", 
    handle-alt: "e" #() by 
      "ctrl" => (λ: "x" "k", "x" "k")
    |  ret   => (λ: "x", "x")
    end)%V.

Section handler_alt.

  Context `{!heapGS Σ}.
  
  Notation handler_alt_spec_type Σ :=
    (coPset -d> operation-d> sem_sig Σ -d> sem_row Σ -d> mode -d> (val -d> iPropO Σ) 
            -d> expr -d> expr
            -d> sem_row Σ -d> (val -d> iPropO Σ) -d> iPropO Σ) (only parsing).
  
    (* Correctness of the effect branch. *)
  Definition handler_alt_spec `{irisGS eff_lang Σ} : handler_alt_spec_type Σ := (
    λ E op σ ρ mh Φ h r ρ' Φ',
    
    (* Subsumption on row *)
    (ρ ≤R ρ') ∗
  
    □ (
    (* Correctness of the return branch. *)
      (∀ (v : val), Φ v -∗ EWPW r v @ E <| ρ' |> {{ Φ' }}) ∧
  
    (* Correctness of the effect branch. *)
      ∀ (v k : val),
        iEff_car (upcl mh σ) v (λ w, EWPW k w @ E <| (op, σ) · ρ |> {{ Φ }}) -∗
        EWPW h v k @ E <| (op, σ) · ρ |> {{ Φ }}
    ))%I.
  
  Lemma ewpw_handler_alt E (op : operation) mh σ ρ ρ' e (h r : val) Φ Φ' :
    EWPW e @ E <| (op, σ) · ρ |> {{ Φ }} -∗
    handler_alt_spec E op σ ρ mh Φ h r ρ' Φ' -∗
    EWPW (HandlerAltV mh e op h r) @E <| ρ' |> {{ Φ' }}.
  Proof.
    iIntros "He H". rewrite /HandlerAltV. 
    iLöb as "IH" forall (e). rewrite /handler_alt /ewpw. 
    rewrite /handler_alt_spec.
    do 10 ewp_value_or_step. ewp_pure_steps. 
    iApply (ewpw_shandler _ op mh MS with "He").
    iDestruct "H" as "(#H1 & #Hbr)".
    rewrite /shandler. iFrame "#%".
    iSplit; first done. simpl. iModIntro. iSplit.
    { iDestruct "Hbr" as "[$ _]". }
    iIntros (v k) "(%Φ'' & Hσ & HPost)".
    rewrite /ewpw; do 6 ewp_value_or_step. 
    rewrite -/handler_alt. iApply ("IH" with "[Hσ HPost]").
    { iDestruct "Hbr" as "[_ H]". iApply "H". iExists Φ''. iFrame. }
    iFrame "#%∗".
  Qed.
  
  Lemma sem_typed_handler_alt {TT : tele} m op (A B : TT → sem_ty Σ) τ τ' ρ' ρ'' Γ₁ Γ₂ Γ₃ Γ' x k e h r :
      x ∉ env_dom Γ₂ → x ∉ env_dom Γ' → x ∉ env_dom Γ₃ → x ∉ env_dom Γ₂ → k ∉ env_dom Γ₂ → k ∉ env_dom Γ₃ → k ∉ env_dom Γ' → x ≠ k →
      let σ := (∀S..: αs, A αs =[ m ]=> B αs)%S in
      let ρ := ((op, σ) · ρ')%R in
      copy_env Γ' -∗
      ρ' ≤R ρ'' -∗
      Γ₁ ⊨ e : ρ : τ ⊨ Γ₂ -∗
      (∀.. αs, (x, A αs) :: (k, B αs -{ ρ }-[m]-> τ) :: Γ' ⊨ h : ρ : τ ⊨ Γ₂) -∗
      (x, τ) :: Γ₂ ++ Γ' ⊨ r : ρ'' : τ' ⊨ Γ₃ -∗
      Γ₁ ++ Γ' ⊨ (handle-alt[m]: e by 
                     op => (λ: x k, h)
                  | ret => (λ: x, r) end)%E : ρ'' : τ' ⊨ Γ₃.
    Proof.
      iIntros (??????????) "#Hcpy #Hle #He #Hh #Hr !# %vs HΓ₁Γ' /=".
      iDestruct (env_sem_typed_app with "HΓ₁Γ'") as "[HΓ₁ HΓ'']". 
      iDestruct ("Hcpy" with "HΓ''") as "#HΓ'". iClear "HΓ''".
      do 4 ewpw_value_or_step. iDestruct "He" as "-#He".
      iSpecialize ("He" $! vs with "HΓ₁").
      iRevert "He". iLöb as "IH" forall (e). iIntros "He".
      ewpw_pure_steps. 
      iApply (ewpw_handler_alt _ _ m with "He [HΓ']").
      rewrite /handler_alt.
      repeat iSplit; first done. iModIntro. iSplit. 
      - iIntros (v) "[Hτ HΓ₂]". ewpw_pure_steps. rewrite - subst_map_insert. 
        iApply (ewpw_mono with "[HΓ₂ HΓ' Hτ]").
        { iApply "Hr". solve_env. iApply env_sem_typed_app; solve_env. }
        iIntros "!# %w [$ HΓ₃] !>". solve_env.
      - iIntros (v k') "(%Φ & Hρ & HPost)".
        rewrite sem_sig_eff_eq. iDestruct "Hρ" as "(%αs & %a & <- & Ha & Hκb)".
        ewpw_pure_steps. solve_dec. 
        rewrite delete_commute - subst_map_insert. 
        rewrite - delete_insert_ne // - subst_map_insert.
        iApply (ewpw_mono with "[Hh Ha Hκb HPost]").
        + iApply "Hh". solve_env. 
          iSplitL; last (do 2 (rewrite - env_sem_typed_insert; solve_env)).
          destruct m; simpl.
          * rewrite /sem_ty_aarr /sem_ty_arr /=. iIntros (?) "HB". 
            iApply (ewpw_mono with "[Hκb HPost HB]").
            { iApply ("HPost" with "[Hκb HB]"). by iApply "Hκb". }
            iIntros "!# % [$ _] //".
          * rewrite /sem_ty_uarr /sem_ty_arr /=. 
            iDestruct "Hκb" as "#Hκb". iDestruct "HPost" as "#HPost". 
            iIntros "!# % HB". 
            iApply (ewpw_mono with "[Hκb HPost HB]").
            { iApply ("HPost" with "[Hκb HB]"). by iApply "Hκb". }
            iIntros "!# % [$ _] //".
        + iIntros "!# /= % [$ H] !>". do 2 (rewrite - env_sem_typed_insert //).
    Qed.
  
End handler_alt.

Section typing.

  (* Make all the definitions opaque so that we do not rely on their definition in the model to show that the programs are well-typed terms. *)
  Opaque sem_typed sem_typed_val ty_le row_le sig_le row_type_sub row_env_sub.
  Opaque sem_ty_void sem_ty_unit sem_ty_bool sem_ty_int sem_ty_string sem_ty_top sem_ty_cpy sem_env_cpy sem_ty_ref_cpy sem_ty_ref sem_ty_prod sem_ty_sum sem_ty_arr sem_ty_aarr sem_ty_uarr sem_ty_forall sem_ty_row_forall sem_ty_exists sem_ty_rec sem_ty_option sem_ty_list.
  Opaque sem_sig_eff sem_sig_os.
  Opaque sem_row_nil sem_row_os sem_row_cons sem_row_rec.

  Context `{!heapGS Σ}.

  Definition ctrl_sig (β : sem_ty Σ) (ctrl : sem_row Σ) : sem_sig Σ := 
      (∀S: α , (α -{ ctrl }-∘ β) -{ ctrl }-∘ β =[ OS ]=> α)%S.

  Definition ctrl_pre (β : sem_ty Σ) (ctrl : sem_row Σ) : sem_row Σ := 
      (("ctrl", ctrl_sig β ctrl) · ⟨⟩)%R.

  Global Instance ctrl_sig_ne β : NonExpansive (ctrl_sig β).
  Proof.
    rewrite /ctrl_sig. intros ????. f_equiv.
    rewrite /tele_app. intros ?. destruct x0; simpl. f_equiv; first done. 
    by f_equiv. 
  Qed.

  Local Instance contractive_ctrl_pre β : Contractive (ctrl_pre β).
  Proof.
    intros ????. rewrite /ctrl_pre. do 3 f_equiv. 
    destruct n; first apply dist_later_0.
    apply dist_later_S. rewrite - dist_later_S in H.
    by f_equiv.
  Qed.

  Definition ctrl β : sem_row Σ := (μR: θ, ctrl_pre β θ)%R.

  Local Instance ctrl_os_row β : Once (ctrl β).
  Proof.
    rewrite /ctrl. apply row_rec_once. iIntros (θ).
    rewrite /ctrl_pre. apply row_cons_once.
    { rewrite /ctrl_sig. apply sig_eff_os_once; apply _. }
    simpl. apply row_nil_once.
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
    iApply (sem_typed_perform_os (TT:=[tele _]) [tele_arg (α : sem_ty Σ)] _ "ctrl" _ (tele_app (λ α, α))).
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
    iApply (sem_typed_handler_alt (TT:=[tele _]) OS "ctrl" (tele_app (λ α, (α -{ ctrl β }-∘ β) -{ ctrl β }-∘ β)) (tele_app (λ α,  α)) β β ⟨⟩%R ⟨⟩%R Γ₁ [] [] []); solve_sidecond.  
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
