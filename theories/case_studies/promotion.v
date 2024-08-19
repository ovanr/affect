
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
From affect.logic Require Import sem_judgement.
From affect.logic Require Import sem_operators.
From affect.logic Require Import compatibility.
From affect.logic Require Import tactics.

(* Make all the definitions opaque so that we do not rely on their definition in the model to show that the programs are well-typed terms. *)
Opaque sem_typed sem_typed_val ty_le row_le sig_le row_type_sub row_env_sub.
Opaque sem_ty_bot sem_ty_unit sem_ty_bool sem_ty_int sem_ty_string sem_ty_top sem_ty_mbang env_mbang sem_ty_ref_cpy sem_ty_ref sem_ty_prod sem_ty_sum sem_ty_arr sem_ty_type_forall sem_ty_row_forall sem_ty_exists sem_ty_rec sem_ty_option sem_ty_list.
Opaque sem_sig_eff sem_sig_flip_mbang.
Opaque sem_row_nil sem_row_flip_mbang sem_row_cons sem_row_rec.

Definition mk_one_shot : val := (λ: <>, 
    shandle: (perform: "op" #()) by 
      "op" => (λ: "x" "k", "k")
    | ret  => (λ: "x", (λ: "y", "y")) 
    end)%V.

  Definition mk_one_shot_dp : val := (λ: <>, 
      let: "r" := ref (λ: <>, #()) in
        handle: (perform: "op" #()) by
        "op" => (λ: "x" "k", "r" <!- "k";; #())
        | ret  => (λ: "x", "x")
        end ;; "r" <!- (λ: <>, #())
  )%V.

Section typing.

  Context `{!heapGS Σ}.

  Definition op_eff : operation * sem_sig Σ := ("op", ∀ₛ (_ : sem_ty Σ), 𝟙 =[OS]=> 𝟙)%S.
  Definition op_row : sem_row Σ := (op_eff · ⟨⟩)%R.
  Definition mk_os_ty : sem_ty Σ := (𝟙 → (𝟙 -{ op_row }-∘ 𝟙))%T.
  Definition mk_os_dp_ty : sem_ty Σ := (𝟙 → (𝟙 ⊸ 𝟙))%T.

  Lemma mk_one_shot_typed : 
    ⊢ (⊨ᵥ mk_one_shot : mk_os_ty).
  Proof.
    iIntros. rewrite /mk_one_shot /mk_os_ty.
    iApply sem_typed_closure; first done. simpl.
    smart_apply (sem_typed_shandler (TT:=[tele _]) OS "op" (tele_app (λ (_ : sem_ty Σ), 𝟙)) (tele_app (λ _, 𝟙)) 𝟙 (𝟙 -{ op_row }-∘ 𝟙) ⟨⟩%R ⟨⟩%R [] [] [] [] "x" "k" with "[] []").
    { iApply row_le_refl. }
    - iApply (sem_typed_perform_os (TT:=[tele _]) [tele_arg 𝟙] with "[]"). 
      iApply sem_typed_unit'.
    - simpl. iIntros (?). iApply sem_typed_weaken.
      rewrite -/op_eff -/op_row. iApply sem_typed_var. 
    - simpl. iApply sem_typed_weaken. 
      rewrite - {1} (app_nil_r []).
      smart_apply sem_typed_afun. simpl.
      iApply sem_typed_var'.
  Qed.

  Lemma mk_one_shot_typed_dp : 
    ⊢ (⊨ᵥ mk_one_shot_dp : mk_os_dp_ty).
  Proof.
    iIntros. rewrite /mk_one_shot_dp /mk_os_ty.
    iApply sem_typed_closure; first done. simpl.
    smart_apply (sem_typed_let (Refᶜ (𝟙 ⊸ 𝟙)) _ _ _ []).
    { iApply sem_typed_alloc_cpy. 
      rewrite - {1} (app_nil_r []). smart_apply sem_typed_afun. iApply sem_typed_unit. }
    iApply sem_typed_contraction.
    set r := ("r", Refᶜ (𝟙 ⊸ 𝟙)).
    iApply (sem_typed_seq 𝟙 _ _ _ [r]). iApply sem_typed_frame.
    - replace [r] with ([] ++ [r]) by done.
      smart_apply (sem_typed_handler (TT:=[tele _]) OS "op" (tele_app (λ (_ : sem_ty Σ), 𝟙)) (tele_app (λ _, 𝟙)) 𝟙 𝟙 ⟨⟩%R ⟨⟩%R [] [] [] [r] "x" "k" with "[] []").
      + iApply row_le_refl.
      + iApply (sem_typed_perform_os (TT:=[tele _]) [tele_arg 𝟙] with "[]"). 
        iApply sem_typed_unit'.
      + simpl. iIntros (?). iApply sem_typed_weaken.
        iApply (sem_typed_seq (𝟙 ⊸ 𝟙) ⟨⟩%R 𝟙 _ []); last iApply sem_typed_unit.
        iApply sem_typed_replace_cpy_os; iApply sem_typed_var.
      + simpl. iApply sem_typed_swap_second. iApply sem_typed_weaken.
        iApply sem_typed_var.
    - iApply sem_typed_replace_cpy_os; first iApply sem_typed_var.
      replace [r] with ([] ++ [r]) by done.
      smart_apply sem_typed_afun. simpl. iApply sem_typed_unit.
  Qed.

End typing.
