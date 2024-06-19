
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
From affect.logic Require Import copyable.
From affect.logic Require Import sem_operators.
From affect.logic Require Import compatibility.
From affect.logic Require Import tactics.

(* Make all the definitions opaque so that we do not rely on their definition in the model to show that the programs are well-typed terms. *)
Opaque sem_typed sem_typed_val ty_le row_le sig_le row_type_sub row_env_sub.
Opaque sem_ty_void sem_ty_unit sem_ty_bool sem_ty_int sem_ty_string sem_ty_top sem_ty_cpy sem_env_cpy sem_ty_ref_cpy sem_ty_ref sem_ty_prod sem_ty_sum sem_ty_arr sem_ty_aarr sem_ty_uarr sem_ty_forall sem_ty_row_forall sem_ty_exists sem_ty_rec sem_ty_option sem_ty_list.
Opaque sem_sig_eff sem_sig_os.
Opaque sem_row_nil sem_row_ins sem_row_os sem_row_tun sem_row_cons sem_row_rec.


Definition handler2 (m : mode) (op1 op2 : operation) (x k : string) (h1 h2 r : expr) : expr := (
  rec: "H" "e" :=
    handle[m]: (
      handle[m]: "e" #() by
        op1 => (λ: x k, h1 x (λ: x, "H" (λ: <>, k x)))
      | ret => (λ: x, r x)
      end
    ) by
     op2 => (λ: x k, h2 x (λ: x, "H" (λ: <>, k x)))
    | ret => (λ: x, x)
    end
)%E.

Section typing.

  Context `{!heapGS Σ}.

  Lemma sem_typed_handler2_alt {TT: tele} m op1 op2 (A1 B1 A2 B2 : TT → sem_ty Σ)τ τ' ρ' ρ'' Γ₁ Γ₂ Γ' x k e h1 h2 r :
    x ∉ env_dom Γ₂ → x ∉ env_dom Γ' → k ∉ env_dom Γ' → x ≠ k →
"e" ∉ env_dom Γ' →
"H" ∉ env_dom Γ' →
    op1 ≠ op2 →
    let σ1 := (∀S..: αs, A1 αs =[m]=> B1 αs)%S in
    let σ2 := (∀S..: αs, A2 αs =[m]=> B2 αs)%S in
    let ρ := ((op1, σ1) ·: (op2, σ2) ·: ρ')%R in
    copy_env Γ' -∗
    ρ' ≤R ρ'' -∗
    Γ₁ ⊨ e : ρ : τ ⊨ Γ₂ -∗
    (∀.. αs, (x, A1 αs) :: (k, B1 αs -{ ρ'' }-[m]-> τ') :: Γ' ⊨ h1 : ρ'' : τ' ⊨ []) -∗
    (∀.. αs, (x, A2 αs) :: (k, B2 αs -{ ρ'' }-[m]-> τ') :: Γ' ⊨ h2 : ρ'' : τ' ⊨ []) -∗
    (x, τ) :: Γ₂ ++ Γ' ⊨ r : ρ'' : τ' ⊨ [] -∗
    Γ₁ ++ Γ' ⊨ (handler2 m op1 op2 x k (λ: x k, h1) (λ: x k, h2) (λ: x, r)) (λ: <>, e) : ρ'' : τ' ⊨ [].
  Proof.
    iIntros (??????????) "#HcpyΓ' #Hρ'ρ'' #He #Hh1 #Hh2 #Hr". rewrite /handler2.
    iApply (sem_typed_app_gen (() -{ ρ }-∘ τ) (¡ ⟨⟩)%R ρ'' _ _ Γ'); try done.
    - iApply row_le_nil. 
    - iApply row_type_sub_os.
    - iApply row_env_sub_cpy. solve_copy.
    - rewrite - {5} (app_nil_r Γ'). 
      iApply sem_typed_sub_ty; first iApply ty_le_u2aarr.
      iApply sem_typed_ufun; [done|done|done|done|simpl].
      assert (("e", _) :: ("H", _) :: Γ' = [("e", _)] ++ (("H", _) :: Γ')).
      Search app.
      iApply sem_typed_handler.
      
