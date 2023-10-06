
From stdpp Require Import base list.
From iris.proofmode Require Import base tactics.
From iris.algebra Require Import excl_auth.


(* Hazel Reasoning *)
From program_logic Require Import weakest_precondition 
                                  tactics 
                                  shallow_handler_reasoning 
                                  deep_handler_reasoning 
                                  state_reasoning.

(* Local imports *)
From affine_tes.lib Require Import base.
From affine_tes.lang Require Import hazel.
From affine_tes.logic Require Import sem_def.
From affine_tes.logic Require Import sem_env.
From affine_tes.logic Require Import sem_types.
From affine_tes.logic Require Import reasoning.
From affine_tes.logic Require Import sem_sub_typing.
From affine_tes.logic Require Import sem_operators.
From affine_tes.logic Require Import compatibility.
From affine_tes.logic Require Import tactics.

Definition impossible : expr := ((rec: "f" <> := "f" #()) #())%E.

Definition async : val := (Λ: λ: "c", perform: (InjL "c"))%V.
Definition await : val := (Λ: λ: "p", (perform: (InjR "p")))%V.
Definition yield : val := 
  (λ: <>, match: async <_> (λ: <>, #()) with
            InjL "p" => await <_> "p" ;; #()
          | InjR <>  => impossible
          end)%V.

Definition iter  : val:= 
  (rec: "f" "g" "xs" := 
    list-match: "xs" with
        CONS "x" => "xxs" => "g" "x" ;; "f" "xxs"
      | NIL => #()
    end)%V.

Definition runner : val :=
  (λ: "main", 
    let: "q" := ref NIL in  

    let: "next" := 
        (λ: <>, list-match: "q" <!- NIL with
                    CONS "x" => "xs" => "q" <!- "xs" ;; "x" #()
                  | NIL => #()
                end)%E in
    let: "add" := (λ: "f", "q" <!- CONS "f" ("q" <!- NIL))%E in
    let: "resume_task" := (λ: "v" "k", "add" ("k" "v"))%E in

    let: "fulfill" := 
      (rec: "fulfill" <> := λ: "promise" "comp",   
        deep-try: "comp" #() with
          effect (λ: "x" "k", 
            match: "x" with 
              InjL "x" => 
                (* async effect *) 
                let: "new_prom" := ref (InjR NIL) in
                "add" (λ: <>, "fulfill" #() "new_prom" "x") ;;
                "k" (InjL "new_prom")
            | InjR "p" =>
                (* await effect *) 
                match: "p" <!- (InjR NIL) with
                  InjL "v" => "p" <!- (InjL "v") ;; "k" "v"
                | InjR "ks" => "p" <!- InjR (CONS "k" "ks") ;; "next" #()
                end
            end
          )%E
        | return (λ: "x", 
            let: "v" := "promise" <- InjR NIL in
            match: "v" with
              InjL <> => impossible
            | InjR "ks" =>
                "promise" <- InjL "v" ;;
                iter ("resume_task" "v") "ks" ;;
                "next" #()
            end
          )%E
        end
      )%E in
      let: "pmain" := ref (InjR NIL) in
      "fulfill" "pmain" "main" ;;
      match: "pmain" <!- InjR NIL with
        InjL "v" => "v"
      | InjR <> => impossible
      end
  )%V.

Section typing.

  Context `{!heapGS Σ}.

  Definition Queue := Refᶜ (List (() ⊸ ())).

  Definition Status τ := τ + List (() ⊸ ()).

  Definition Promise τ := Refᶜ (Status τ).

  Definition asig := (∀μTS: θ, α, ( () -{ θ }-∘ '! α ) + Promise ('! α) ⇒ 
                                  Promise ('! α)       + '! α)%R. 

  Lemma impossible_typed τ :
    ⊢ ⊨ impossible : ⟨⟩ : τ.
  Proof.
    iIntros. rewrite /impossible.
    iApply sem_typed_app; last (iApply sem_typed_unit).
    rewrite - {1} (app_nil_r []).
    iApply sem_typed_sub_ty; [apply ty_le_u2aarr|].
    iApply sem_typed_ufun; solve_sidecond. simpl.
    iApply sem_typed_app; last (iApply sem_typed_unit).
    iApply sem_typed_sub_ty; [apply ty_le_u2aarr|].
    iApply sem_typed_var.
  Qed.

  Lemma async_typed :
    ⊢ ⊨ᵥ async : (∀T: α ,, (() -{ asig }-∘ '! α) -{ asig }-> Promise ('! α) + '! α).
  Proof.
    rewrite /async. iIntros.
    iApply sem_typed_Tclosure. iIntros (α).
    rewrite - {1} (app_nil_r []).
    iApply sem_typed_ufun; solve_sidecond. simpl.
    iApply (sem_typed_perform with "[]");
      try (rewrite /Promise /Status; intros ???????; by repeat f_equiv).
    iApply sem_typed_left_inj.
    iApply sem_typed_sub_nil.
    iApply sem_typed_var.
  Qed.

  Lemma await_typed :
    ⊢ ⊨ᵥ await : (∀T: α ,, Promise ('! α) -{ asig }-> Promise ('! α) + '! α).
  Proof.
    rewrite /await. iIntros.
    iApply sem_typed_Tclosure. iIntros (α).
    rewrite - {1} (app_nil_r []).
    iApply sem_typed_ufun; solve_sidecond. simpl.
    iApply (sem_typed_perform with "[]");
      try (rewrite /Promise /Status; intros ???????; by repeat f_equiv).
      iApply sem_typed_sub_nil.
      iApply sem_typed_right_inj.
      iApply sem_typed_var. 
  Qed.

  Lemma yield_typed :
    ⊢ ⊨ᵥ yield : ( () -{ asig }-> () ).
  Proof.
    iIntros. iApply sem_typed_closure; try done. simpl.
    iApply (sem_typed_match [] [] [] _ _ _ _ _ (Promise ( '! () )) _ ('! ())); solve_sidecond.
    - iApply (sem_typed_app _ [] _ _ _ (() -{ asig }-∘ '! ())).
      + iApply sem_typed_sub_nil. 
        iApply sem_typed_sub_ty; [apply ty_le_u2aarr|].
        set C := (λ α, (() -{ asig }-∘ '! α) -{ asig }-> Promise ('! α) + ('! α)).
        rewrite -/(C ()). iApply sem_typed_TApp.
        iApply sem_typed_val. iApply async_typed.
      + iApply sem_typed_sub_nil.
        rewrite - {1} (app_nil_r []).
        iApply sem_typed_afun; solve_sidecond. simpl.
        iApply sem_typed_sub_nil.
        iApply sem_typed_sub_ty.
        { apply ty_le_cpy. solve_copy. }
        iApply sem_typed_unit.
    - simpl. iApply sem_typed_seq; [|iApply sem_typed_sub_nil; iApply sem_typed_unit].
      iApply (sem_typed_app _ [] _ _ _ (Promise ('! ())) _ (Promise ('! ()) + '!())).
      + iApply sem_typed_sub_nil. 
        iApply sem_typed_sub_ty; [apply ty_le_u2aarr|].
        set C := (λ α, (Promise ('! α)) -{ asig }-> Promise ('! α) + ('! α)).
        rewrite -/(C ()). iApply sem_typed_TApp.
        iApply sem_typed_val. iApply await_typed.
      + iApply sem_typed_sub_nil. iApply sem_typed_var.
    - simpl. iApply sem_typed_sub_nil. 
      iApply impossible_typed.
  Qed.

End typing.
