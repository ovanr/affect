
From stdpp Require Import base list.
From iris.proofmode Require Import base tactics.
From iris.algebra Require Import excl_auth.

(* Local imports *)
From affect.lib Require Import base.
From affect.lang Require Import affect.
From affect.logic Require Import sem_def.
From affect.logic Require Import sem_env.
From affect.logic Require Import sem_sig.
From affect.logic Require Import sem_row.
From affect.logic Require Import mode.
From affect.logic Require Import sem_types.
From affect.logic Require Import sem_judgement.
From affect.logic Require Import sem_operators.
From affect.logic Require Import compatibility.
From affect.logic Require Import tactics.

(* Make all the definitions opaque so that we do not rely on their definition in the model to show that the programs are well-typed terms. *)
Opaque sem_typed sem_typed_val ty_le row_le sig_le row_type_sub row_env_sub.
Opaque sem_ty_bot sem_ty_unit sem_ty_bool sem_ty_int sem_ty_top sem_ty_mbang env_mbang sem_ty_ref_cpy sem_ty_ref sem_ty_prod sem_ty_sum sem_ty_arr sem_ty_type_forall sem_ty_row_forall sem_ty_exists sem_ty_rec sem_ty_option sem_ty_list.
Opaque sem_sig_eff sem_sig_flip_mbang.
Opaque sem_row_nil sem_row_flip_mbang sem_row_cons sem_row_rec.

Definition yield := (λ: "n", perform: "yield" "n")%V.
Definition choose := (λ: <>, perform: "choose" #())%V.

Definition step : val := (rec: "step" "n" := 
  if: ("n" = #0) then #()
  else if: ("n" = #1) then yield #1
       else if: choose #() then yield #1;; "step" ("n" - #1) 
                           else yield #2;; "step" ("n" - #2) 
)%V.

Definition handle_yield : val := (λ: "f",
    handle[OS]: "f" #() by
      "yield" => λ: "x" "k", CONS "x" ("k" #())
    | ret     => λ: "x", NIL
    end
)%V.

Definition append : val := (rec: "append" "l1" := λ: "l2",
  list-match: "l1" with 
      CONS "x" => "xs" => CONS "x" ("append" "xs" "l2")
    | NIL => "l2"
  end
)%V.

Definition handle_choose : val := (λ: "f",
    handle[MS]: "f" #() by
      "choose" => λ: "x" "k", (append ("k" #true) ("k" #false))
    | ret     => λ: "x", CONS "x" NIL
    end
)%V.

Definition steps : expr := handle_choose (λ: <>, handle_yield (λ: <>, step #4)%V)%V.

Section typing.

  Context `{!heapGS Σ}.

  Definition yieldsig (τ : sem_ty Σ) : operation * sem_sig Σ := ("yield", τ =[OS]=> 𝟙)%S.
  Definition choosesig : operation * sem_sig Σ := ("choose", 𝟙 =[MS]=> 𝔹)%S.
  Definition eff : sem_row Σ := (yieldsig ℤ · choosesig · ⟨⟩)%R.

  Definition yield_ty : sem_ty Σ := ℤ -{ eff }-> 𝟙. 
  Definition choose_ty : sem_ty Σ := 𝟙 -{ eff }-> 𝔹.
  Definition append_ty : sem_ty Σ := (∀ₜ α, List α → List α ⊸ List α).
  Definition step_ty : sem_ty Σ := ℤ -{ eff }-> 𝟙.

  Definition handle_yield_ty_gen : sem_ty Σ := 
    (∀ₜ α, ∀ᵣ θ, ∀ₘ ν, (𝟙 -{ yieldsig (![ν] α) · ¡[ν] θ }-∘ 𝟙) -{ ¡[ν] θ }-> List (![ν] α)).
  Definition handle_choose_ty_gen : sem_ty Σ := 
    (∀ₜ α, ∀ᵣ θ, ∀ₘ ν, (𝟙 -{ choosesig · ¡[ν] θ }-∘ ![ν] α) -{ ¡[ν] θ }-> List (![ν] α))%T.

  Definition handle_yield_ty : sem_ty Σ := ((𝟙 -{ eff }-∘ 𝟙) -{ choosesig · ⟨⟩ }-> List ℤ).
  Definition handle_choose_ty : sem_ty Σ := ((𝟙 -{ choosesig · ⟨⟩ }-∘ (List ℤ)) → List (List ℤ))%T.

  Lemma append_typed : ⊢ ⊨ᵥ append : append_ty.
  Proof.
    iIntros. rewrite /append /append_ty.
    iApply sem_typed_Tclosure. iIntros (α).
    iApply sem_typed_closure; first done. simpl.
    rewrite - (app_nil_r [("l1", _); ("append", _)]).
    smart_apply sem_typed_afun. simpl.
    iApply sem_typed_swap_second.
    smart_apply (sem_typed_match_list α ⟨⟩%R (List α) _ [("l2", _); ("append", _)] []).
    - iApply sem_typed_var.
    - iApply sem_typed_swap_second. iApply sem_typed_weaken. iApply sem_typed_var.
    - iApply sem_typed_cons; first iApply sem_typed_var.
      iApply sem_typed_frame. iApply sem_typed_swap_second.
      smart_apply sem_typed_app_nil; last iApply sem_typed_var.
      smart_apply sem_typed_app_nil; last iApply sem_typed_var.
      iApply sem_typed_sub_u2aarr. iApply sem_typed_var.
  Qed.

  Lemma yield_typed : ⊢ ⊨ᵥ yield : yield_ty.
  Proof.
    iIntros. rewrite /yield /yield_ty.
    iApply sem_typed_closure; first done. simpl.
    iApply (sem_typed_perform_os (TT:=[tele ]) [tele_arg] _ "yield" with "[]").
    iApply sem_typed_var'.
  Qed.

  Lemma choose_typed : ⊢ ⊨ᵥ choose : choose_ty.
  Proof.
    iIntros. rewrite /choose /choose_ty.
    iApply sem_typed_closure; first done. simpl.
    iApply sem_typed_sub_row.
    { iApply row_le_trans; [|iApply row_le_swap_second; first done].
      iApply row_le_cons_comp; [iApply sig_le_refl|iApply row_le_nil]. }
    iApply (sem_typed_perform_ms (TT:=[tele ]) [tele_arg] _ "choose" with "[]").
    iApply sem_typed_unit'.
  Qed.

  Lemma step_typed : ⊢ ⊨ᵥ step : step_ty.
  Proof.
    iIntros. rewrite /step /step_ty.
    iApply sem_typed_closure; first done. simpl.
    iApply sem_typed_contraction.
    iApply (sem_typed_if 𝟙 eff _ [("n", _); ("step", _)]).
    - iApply (sem_typed_bin_op ℤ ℤ); first constructor.
      { iApply sem_typed_var'. }
      iApply sem_typed_int'.
    - do 2 iApply sem_typed_weaken. iApply sem_typed_unit'.
    - iApply sem_typed_contraction. 
      iApply (sem_typed_if 𝟙 eff _ [("n", _); ("step", _)]).
      + iApply (sem_typed_bin_op ℤ ℤ); first constructor.
        { iApply sem_typed_var'. }
        iApply sem_typed_int'.
      + do 2 iApply sem_typed_weaken.
        iApply sem_typed_app_nil; last iApply sem_typed_int'.
        iApply sem_typed_sub_u2aarr. iApply sem_typed_val. iApply yield_typed.
      + iApply (sem_typed_if 𝟙 eff _ [("n", _); ("step", _)]).
        * do 2 iApply sem_typed_frame_ms. iApply sem_typed_app_nil; last iApply sem_typed_unit'.
          iApply sem_typed_sub_u2aarr.
          iApply sem_typed_val. iApply choose_typed.
        * iApply (sem_typed_seq 𝟙 eff _ _ [("n", _); ("step", _)]).
          { do 2 iApply sem_typed_frame_ms. iApply sem_typed_app_nil; last iApply sem_typed_int'.
            iApply sem_typed_sub_u2aarr. iApply sem_typed_val. iApply yield_typed. }
          iApply sem_typed_app_nil.
          { iApply sem_typed_sub_u2aarr. iApply sem_typed_var'. }
          iApply (sem_typed_bin_op ℤ ℤ ℤ); first constructor; last iApply sem_typed_int'.
          iApply sem_typed_var'.
        * iApply (sem_typed_seq 𝟙 eff _ _ [("n", _); ("step", _)]).
          { do 2 iApply sem_typed_frame_ms. iApply sem_typed_app_nil; last iApply sem_typed_int'.
            iApply sem_typed_sub_u2aarr. iApply sem_typed_val. iApply yield_typed. }
          iApply sem_typed_app_nil.
          { iApply sem_typed_sub_u2aarr. iApply sem_typed_var'. }
          iApply (sem_typed_bin_op ℤ ℤ ℤ); first constructor; last iApply sem_typed_int'.
          iApply sem_typed_var'.
    Qed.

    Lemma handle_yield_typed_gen : ⊢ ⊨ᵥ handle_yield : handle_yield_ty_gen.
    Proof.
      iIntros. rewrite /handle_yield /handle_yield_ty_gen.
      iApply sem_typed_Tclosure. iIntros (α).
      iApply sem_typed_Rclosure. iIntros (θ).
      iApply sem_typed_Mclosure. iIntros (ν).
      iApply sem_typed_closure; first done. simpl.
      rewrite -(app_nil_r [("f", _)]).
      smart_apply (sem_typed_handler (TT:=[tele]) OS "yield" (tele_app (![ν] α)) (tele_app 𝟙) _ _ (¡[ν] θ)%R _ _ []).
      - iApply row_le_refl.
      - iApply sem_typed_app_nil; last iApply sem_typed_unit'. iApply sem_typed_var'.
      - iApply sem_typed_cons_gen. 
        + apply (row_type_sub_ty_equiv (¡[ν] θ)%R (![ν] (List α))%T (List (![ν] α))%T).
          * iApply ty_le_list_mbang.
          * iApply ty_le_trans; first (iApply ty_le_mbang_intro_list; iApply ty_le_mbang_idemp).
            iApply ty_le_mbang_comp; first iApply mode_le_refl.
            iApply ty_le_list. iApply ty_le_mbang_elim.
          * apply row_type_sub_mfbang_mbang.
        + iApply sem_typed_var'.
        + iApply sem_typed_frame_gen. iApply sem_typed_app_nil; last iApply sem_typed_unit'.
          iApply sem_typed_var'.
      - simpl. iApply sem_typed_sub_nil. iApply sem_typed_weaken. iApply sem_typed_nil.
    Qed.

    Lemma handle_choose_typed_gen : ⊢ ⊨ᵥ handle_choose : handle_choose_ty_gen.
    Proof.
      iIntros. rewrite /handle_choose /handle_choose_ty.
      iApply sem_typed_Tclosure. iIntros (α).
      iApply sem_typed_Rclosure. iIntros (θ).
      iApply sem_typed_Mclosure. iIntros (ν).
      iApply sem_typed_closure; first done. simpl.
      assert (Hsub : ¡[ ν] θ ᵣ⪯ₜ List ![ ν] α).
      { apply (row_type_sub_ty_equiv (¡[ν] θ)%R (![ν] (List α))%T (List (![ν] α))%T);
        [iApply ty_le_list_mbang| |apply row_type_sub_mfbang_mbang].
        iApply ty_le_trans; first (iApply ty_le_mbang_intro_list; iApply ty_le_mbang_idemp).
        iApply ty_le_mbang_comp; first iApply mode_le_refl.
        iApply ty_le_list. iApply ty_le_mbang_elim. }
      rewrite -(app_nil_r [("f", _)]).
      smart_apply (sem_typed_handler (TT:=[tele]) MS "choose" (tele_app 𝟙) (tele_app 𝔹) _ _ (¡[ν] θ)%R _ _ []).
      - iApply row_le_refl.
      - iApply sem_typed_app_nil; last iApply sem_typed_unit'. iApply sem_typed_var'.
      - iApply (sem_typed_app_gen (List (![ν] α))%T (¡[ν] θ)%R (¡[ν] θ)%R ⟨⟩%R).
        + iApply row_le_refl.
        + iApply row_le_nil.
        + iApply (sem_typed_app_gen (List (![ν] α))%T ⟨⟩%R (¡[ν] θ)%R ⟨⟩%R).
          * iApply row_le_nil.
          * iApply row_le_nil.
          * iApply sem_typed_sub_u2aarr.
            iApply (sem_typed_TApp (λ α, List α → List α ⊸ List α))%T.
            iApply sem_typed_val. iApply append_typed.
          * iApply sem_typed_app_nil; [|iApply sem_typed_bool'].
            iApply sem_typed_sub_u2aarr. iApply sem_typed_var.
        + iApply sem_typed_weaken. iApply sem_typed_contraction. 
          iApply sem_typed_frame_gen. iApply sem_typed_app_nil; last iApply sem_typed_bool'.
          iApply sem_typed_sub_u2aarr. iApply sem_typed_var.
      - simpl. iApply sem_typed_cons_gen. iApply sem_typed_var'.
        iApply sem_typed_sub_nil. iApply sem_typed_nil.
    Qed.

    Corollary handle_yield_typed : ⊢ ⊨ handle_yield : ⟨⟩ : handle_yield_ty.
    Proof.
      rewrite /handle_yield_ty.
      iApply sem_typed_sub_ty.
      iApply ty_le_uarr; [iApply row_le_mfbang_elim_ms| |iApply ty_le_list; iApply (ty_le_mbang_elim MS)].
      iApply ty_le_arr; try iApply ty_le_refl. iApply row_le_cons_comp; last iApply (row_le_mfbang_intro MS).
      iApply sig_le_mfbang_comp; first iApply mode_le_refl.
      iApply (sig_le_eff (TT:=[tele ]) _ (tele_app (![MS] ℤ)%T) _ (tele_app 𝟙)); iIntros "!#". 
      { iApply ty_le_mbang_intro_int. }
      { iApply ty_le_refl. }
      rewrite -/(yieldsig (![MS] ℤ))%T.
      iApply (sem_typed_MApp (λ m, (𝟙 -{ yieldsig (![m] ℤ) · ¡[m] (choosesig · ⟨⟩) }-∘ 𝟙) -{
   ¡[m] (choosesig · ⟨⟩) }-> List (![m] ℤ))).
      iApply (sem_typed_RApp (λ θ, ∀ₘ ν, (𝟙 -{ yieldsig (![ ν] ℤ) · (¡[ ν] θ) }-∘ 𝟙) -{ ¡[ ν] θ }-> List (![ ν] ℤ))).
      iApply (sem_typed_TApp (λ α, ∀ᵣ θ, ∀ₘ ν, (𝟙 -{ yieldsig (![ ν] α) · (¡[ ν] θ) }-∘ 𝟙) -{ ¡[ ν] θ }-> List (![ ν] α))).
      iApply sem_typed_val. iApply handle_yield_typed_gen.
    Qed.

    Corollary handle_choose_typed : ⊢ ⊨ handle_choose : ⟨⟩ : handle_choose_ty.
    Proof.
      rewrite /handle_choose_ty.
      iApply sem_typed_sub_ty.
      iApply ty_le_uarr; [iApply row_le_mfbang_elim_ms| |iApply ty_le_list; iApply (ty_le_mbang_elim MS)].
      { iApply ty_le_arr; [|iApply ty_le_refl|iApply (ty_le_mbang_intro_list); iApply (ty_le_mbang_intro_int MS)].
        iApply row_le_cons_comp;[iApply sig_le_refl|iApply (row_le_mfbang_intro MS)]. }
      rewrite -/choosesig.
      iApply (sem_typed_MApp (λ m, (𝟙 -{ choosesig · ¡[m] ⟨⟩ }-∘ ![m] (List ℤ)) -{ ¡[m] ⟨⟩ }-> List (![m] (List ℤ)))).
      iApply (sem_typed_RApp (λ θ, ∀ₘ ν, (𝟙 -{ choosesig · ¡[ν] θ }-∘ ![ν] (List ℤ)) -{ ¡[ν] θ }-> List (![ν] (List ℤ)))).
      iApply (sem_typed_TApp (λ α, ∀ᵣ θ, ∀ₘ ν, (𝟙 -{ choosesig · ¡[ν] θ }-∘ ![ν] α) -{ ¡[ν] θ }-> List (![ν] α))).
      iApply sem_typed_val. iApply handle_choose_typed_gen.
    Qed.

    Lemma steps_typed : ⊢ ⊨ steps : ⟨⟩ : List (List ℤ).
    Proof.
      rewrite /steps. iApply sem_typed_app_nil.
      { iApply sem_typed_sub_u2aarr. iApply handle_choose_typed. }
      iApply sem_typed_sub_u2aarr. iApply sem_typed_val. iApply sem_typed_closure; first done.
      simpl. iApply sem_typed_app_nil.
      { iApply sem_typed_sub_u2aarr. iApply handle_yield_typed. }
      iApply sem_typed_sub_u2aarr. iApply sem_typed_sub_nil. iApply sem_typed_val. 
      iApply sem_typed_closure; first done. simpl.
      iApply sem_typed_app_nil; last iApply sem_typed_int'.
      iApply sem_typed_sub_u2aarr. iApply sem_typed_val.
      iApply step_typed.
    Qed.

End typing.
