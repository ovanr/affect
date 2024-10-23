
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

Definition handle_counter : val := (λ: "f", 
          handle: "f" #() by
            "inc" => (λ: "x" "k", λ: "m", "k" "m" ("x" + "m"))
          | ret => (λ: "x", λ: "m", "x")
          end #0
)%V.

Section typing.

  Context `{!heapGS Σ}.

  Definition countersig : operation * sem_sig Σ := ("inc", ℤ =[OS]=> ℤ)%S.

  Definition handle_counter_ty : sem_ty Σ := 
    (∀ₜ α, ∀ᵣ θ, (𝟙 -{ countersig · θ }-∘ α) -{ θ }-> α)%T.

  Lemma handle_counter_typed : ⊢ ⊨ᵥ handle_counter : handle_counter_ty.
  Proof.
    iIntros. rewrite /handle_counter /handle_counter_ty.
    iApply sem_typed_Tclosure. iIntros (α).
    iApply sem_typed_Rclosure. iIntros (θ).
    iApply sem_typed_closure; first done. simpl.
    rewrite - (app_nil_r [("f", _)]).
    iApply (sem_typed_app_ms ℤ); last iApply sem_typed_int'.
    smart_apply (sem_typed_handler (TT:=[tele]) OS "inc" (tele_app ℤ) (tele_app ℤ) α (ℤ -{ θ }-∘ α) _ _ _ [] []). 
    - iApply row_le_refl.
    - iApply sem_typed_app_nil; first iApply sem_typed_var'.
      iApply sem_typed_unit'.
    - rewrite - (app_nil_r [("x", _); ("k", _)]).
      iApply sem_typed_sub_nil.
      smart_apply sem_typed_afun. simpl.
      iApply (sem_typed_app_ms ℤ).
      { iApply sem_typed_app_nil; iApply sem_typed_var'. }
      iApply (sem_typed_bin_op ℤ ℤ ℤ); first constructor.
      { iApply sem_typed_var'. }
      iApply sem_typed_contraction. iApply sem_typed_swap_third.
      iApply sem_typed_swap_second. iApply sem_typed_var'.
    - simpl. rewrite - (app_nil_r [("x", _)]).
      iApply sem_typed_sub_nil.
      smart_apply sem_typed_afun. 
      iApply sem_typed_weaken. iApply sem_typed_var'.
  Qed.

End typing.
