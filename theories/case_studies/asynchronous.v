
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
From haffel.lang Require Import hazel.
From haffel.logic Require Import sem_def.
From haffel.logic Require Import sem_env.
From haffel.logic Require Import sem_types.
From haffel.logic Require Import sem_sub_typing.
From haffel.logic Require Import sem_operators.
From haffel.logic Require Import compatibility.
From haffel.logic Require Import tactics.

Definition impossible : expr := ((rec: "f" <> := "f" #()) #())%E.

Definition async : val := (Λ: λ: "c", perform: (InjL "c"))%V.
Definition await : val := (Λ: λ: "p", (perform: (InjR "p")))%V.
Definition yield : val := 
  (λ: <>, match: async <_> (λ: <>, #()) with
            InjL "p" => await <_> "p" ;; #()
          | InjR <>  => impossible
          end)%V.

Definition iter  : val:= 
  (Λ: rec: "f" "g" "xs" := 
    list-match: "xs" with
        CONS "x" => "xxs" => "g" "x" ;; "f" "g" "xxs"
      | NIL => #()
    end)%V.

Definition next : val :=
  (λ: "q" <>, list-match: "q" <!- NIL with
              CONS "x" => "xs" => "q" <!- "xs" ;; "x" #()
            | NIL => #()
          end)%V.

Definition add : val := 
  (λ: "q" "f", "q" <!- CONS "f" ("q" <!- NIL) ;; #())%V.

Definition resume_task : val := 
  (λ: "add", Λ: λ: "v" "k", "add" (λ: <>, "k" "v"))%V.

Definition runner : val :=
  (Λ: λ: "main", 
    let: "q" := ref NIL in  

    let: "add" := add "q" in
    let: "next" := next "q" in
    let: "resume_task" := resume_task "add" in

    let: "fulfill" := 
      (rec: "fulfill" <> := λ: "promise" "comp",   
        deep-try-os: "comp" #() with
          effect (λ: "x" "k", 
            match: "x" with 
              InjL "x" => 
                (* async effect *) 
                let: "new_prom" := ref (InjR NIL) in
                "add" (λ: <>, "fulfill" <_> "new_prom" "x") ;;
                "k" (InjL "new_prom")
            | InjR "p" =>
                (* await effect *) 
                match: "p" <!- (InjR NIL) with
                  InjL "v" => "p" <!- (InjL "v") ;; "k" (InjR "v")
                | InjR "ks" => "p" <!- InjR (CONS (λ: "v", "k" (InjR "v")) "ks") ;; "next" #()
                end
            end
          )%E
        | return (λ: "x", 
            let: "v" := "promise" <!- InjR NIL in
            match: "v" with
              InjL <> => impossible
            | InjR "ks" =>
                "promise" <!- InjL "x" ;;
                iter <_> ("resume_task" <_> "x") "ks" ;;
                "next" #()
            end
          )%E
        end
      )%E in
      let: "pmain" := ref (InjR NIL) in
      "fulfill" <_> "pmain" "main" ;;
      match: "pmain" <!- InjR NIL with
        InjL "v" => "v"
      | InjR <> => impossible
      end
  )%V.

Section typing.

  Context `{!heapGS Σ}.

  Definition Queue := Refᶜ (List (() ⊸ ())).

  Definition Status τ := τ + List (τ ⊸ ()).

  Definition Promise τ := Refᶜ (Status τ).

  Definition asig := ⟨μ∀TS: θ, α, ( () -{ ⟨θ,⟩ }-∘ '! α ) + Promise ('! α) ⇒ 
                                     Promise ('! α)       + '! α, @sem_sig_nil Σ⟩%R. 

  Definition iter_ty τ := (∀R: θ, (τ -{ ⟨θ.1,⟩ }-> ()) → List τ -{ ⟨θ.1,⟩ }-∘ ())%T.
  
  Definition next_ty := (() → ())%T.

  Definition add_ty := ((() ⊸ ()) → ())%T.

  Definition resume_task_ty := (∀T: α,, '! α → ('! α ⊸ ()) → ())%T.
  
  Definition runner_ty := (∀T: α,, (() -{ asig }-∘ '! α) → '! α)%T.

  Lemma impossible_typed τ :
    ⊢ ⊨ impossible : ⟨⟩ : τ.
  Proof.
    iIntros. rewrite /impossible.
    iApply sem_typed_app; first solve_copy; last (iApply sem_typed_unit).
    rewrite - {1} (app_nil_r []).
    iApply sem_typed_sub_ty; [iApply ty_le_u2aarr|].
    iApply sem_typed_ufun; solve_sidecond. simpl.
    iApply sem_typed_app; first solve_copy; last (iApply sem_typed_unit).
    iApply sem_typed_sub_ty; [iApply ty_le_u2aarr|].
    iApply sem_typed_var.
  Qed.

  Lemma async_typed :
    ⊢ ⊨ᵥ async : (∀T: α ,, (() -{ asig }-∘ '! α) -{ asig }-> Promise ('! α) + '! α).
  Proof.
    rewrite /async. iIntros.
    iApply sem_typed_Tclosure. iIntros (α).
    rewrite - {1} (app_nil_r []).
    iApply sem_typed_ufun; solve_sidecond. simpl.
    iApply (sem_typed_perform_os with "[]");
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
    iApply (sem_typed_perform_os with "[]");
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
    - iApply (sem_typed_app _ [] _ _ _ (() -{ asig }-∘ '! ())); first solve_copy.
      + iApply sem_typed_sub_nil. 
        iApply sem_typed_sub_ty; [iApply ty_le_u2aarr|].
        set C := (λ α, (() -{ asig }-∘ '! α) -{ asig }-> Promise ('! α) + ('! α)).
        rewrite -/(C ()). iApply sem_typed_TApp; first solve_copy.
        iApply sem_typed_val. iApply async_typed.
      + iApply sem_typed_sub_nil.
        rewrite - {1} (app_nil_r []).
        iApply sem_typed_afun; solve_sidecond. simpl.
        iApply sem_typed_sub_nil.
        iApply sem_typed_sub_ty.
        { iApply ty_le_cpy. solve_copy. }
        iApply sem_typed_unit.
    - simpl. iApply sem_typed_seq; [|iApply sem_typed_sub_nil; iApply sem_typed_unit].
      iApply (sem_typed_app _ [] _ _ _ (Promise ('! ())) _ (Promise ('! ()) + '!())); first solve_copy.
      + iApply sem_typed_sub_nil. 
        iApply sem_typed_sub_ty; [iApply ty_le_u2aarr|].
        set C := (λ α, (Promise ('! α)) -{ asig }-> Promise ('! α) + ('! α)).
        rewrite -/(C ()). iApply sem_typed_TApp; first solve_copy.
        iApply sem_typed_val. iApply await_typed.
      + iApply sem_typed_sub_nil. iApply sem_typed_var.
    - simpl. iApply sem_typed_sub_nil. 
      iApply impossible_typed.
  Qed.

  Lemma iter_typed τ :
    ⊢ ⊨ᵥ iter : iter_ty τ.
  Proof.
    iApply sem_typed_Rclosure. iIntros (ρ).
    iApply sem_typed_sub_nil.
    rewrite - {1} (app_nil_r []). 
    iApply sem_typed_ufun; solve_sidecond. simpl.
    rewrite - [[("g", _); ("f", _)]]app_nil_r. 
    iApply sem_typed_afun; solve_sidecond. simpl.
    set Γ₂ := [("g", τ -{ ⟨ρ.1,⟩ }-> ());
               ("f", ((τ -{ ⟨ρ.1,⟩ }-> ()) → List τ -{ ⟨ρ.1,⟩ }-∘ ())%T)].
    iApply (sem_typed_match_list _ Γ₂); solve_sidecond.
    - iApply sem_typed_sub_nil. rewrite - !/Γ₂.
      iApply (sem_typed_var Γ₂).
    - iApply sem_typed_sub_nil. 
      do 2 iApply sem_typed_weaken.
      iApply sem_typed_unit.
    - iApply sem_typed_seq.
      + iApply sem_typed_swap_third. iApply sem_typed_swap_second. 
        iApply sem_typed_app_os; last (iApply sem_typed_sub_nil; iApply sem_typed_var).
        iApply sem_typed_contraction; solve_sidecond.
        simpl. iApply sem_typed_sub_ty; [iApply ty_le_u2aarr|].
        iApply sem_typed_sub_nil; iApply sem_typed_var.
      + iApply sem_typed_swap_second. rewrite -/Γ₂.
        do 2 (iApply sem_typed_app_os;
          last (iApply sem_typed_sub_nil; iApply sem_typed_var)).
        iApply sem_typed_sub_nil.
        iApply sem_typed_sub_ty. 
        { iApply ty_le_trans; [|iApply ty_le_u2aarr].
          iApply ty_le_uarr. { simpl. iApply sigs_le_nil. }
          iApply ty_le_refl. iApply ty_le_refl. }
        iApply sem_typed_var.
  Qed.

  Definition add_typed :
    ⊢ ⊨ᵥ add : (Queue → add_ty).
  Proof.
    iIntros. rewrite /add_ty.
    iApply sem_typed_closure; solve_sidecond. simpl.
    set q := ("q", Queue). rewrite -(app_nil_r [q]).
    iApply sem_typed_ufun; solve_sidecond. simpl.
    set f := ("f", () ⊸ ()).
    iApply (sem_typed_seq _ []); [|iApply sem_typed_unit].
    iApply (sem_typed_replace_cpy _ [q]); [iApply sem_typed_var|].
    iApply (sem_typed_cons _ [q;f]). 
    { iApply sem_typed_swap_second. iApply sem_typed_var. }
    iApply sem_typed_swap_second.
    iApply sem_typed_replace_cpy; [|iApply sem_typed_nil].
    iApply sem_typed_contraction; solve_sidecond.
    iApply sem_typed_var.
  Qed.

  Definition next_typed :
    ⊢ ⊨ᵥ next : (Queue → next_ty).
  Proof.
    iIntros. rewrite /next_ty.
    iApply sem_typed_closure; solve_sidecond. simpl.
    set q := ("q", Queue). rewrite -(app_nil_r [q]).
    iApply sem_typed_ufun; solve_sidecond. simpl.
    iApply (sem_typed_match_list _ [q]); solve_sidecond.
    - iApply sem_typed_replace_cpy; [|iApply sem_typed_nil].
      iApply sem_typed_contraction; solve_sidecond.
      iApply sem_typed_var.
    - iApply sem_typed_weaken. iApply sem_typed_unit.
    - iApply sem_typed_swap_second.
      iApply sem_typed_swap_third.
      iApply sem_typed_swap_second.
      set x := ("x", () ⊸ ()).
      set xs := ("xs", List (() ⊸ ())).
      rewrite -/q.
      iApply (sem_typed_seq _ [x]). 
      { iApply sem_typed_replace_cpy; iApply sem_typed_var. }
      iApply sem_typed_app_os; [iApply sem_typed_var|iApply sem_typed_unit].
  Qed.

  Definition resume_task_typed :
    ⊢ ⊨ᵥ resume_task : (add_ty → resume_task_ty).
  Proof.
    iIntros. rewrite /resume_task_ty.
    iApply sem_typed_closure; solve_sidecond. simpl.
    set add := ("add", add_ty)%T. rewrite -(app_nil_r [add]).
    iApply sem_typed_TLam; solve_sidecond. iIntros (α).
    rewrite -(app_nil_r [add]).
    iApply sem_typed_ufun; solve_sidecond. simpl.
    rewrite -(app_nil_r [("v", '! α); add]).
    set v := ("v", '! α).
    iApply sem_typed_ufun; solve_sidecond. simpl.
    set k := ("k", '! α ⊸ ()).
    iApply (sem_typed_app_os _ [add]). 
    { iApply sem_typed_sub_ty; [iApply ty_le_u2aarr|].
      iApply sem_typed_var. }
    replace ([k; v; add]) with ([k;v] ++ [add]) by done.
    iApply sem_typed_afun; solve_sidecond. simpl.
    iApply sem_typed_swap_second.
    iApply sem_typed_app_os; iApply sem_typed_var.
  Qed.

  Definition runner_typed :
    ⊢ ⊨ᵥ runner : runner_ty.
  Proof.
    iIntros. iApply sem_typed_Tclosure. iIntros (α).
    rewrite - {1} (app_nil_r []).
    iApply sem_typed_ufun; solve_sidecond. simpl.
    set main := ("main", () -{ asig }-∘ '! α).
    iApply (sem_typed_let _ [main]); solve_sidecond.
    { iApply (sem_typed_alloc_cpy _ _ _ _ (List (() ⊸ ()))). 
      iApply sem_typed_nil. }
    iApply sem_typed_contraction; solve_sidecond.
    set q := ("q", Queue).
    iApply (sem_typed_let _ [q; main]); solve_sidecond.
    { iApply sem_typed_app_os; [|iApply sem_typed_var].
      iApply sem_typed_sub_ty; [iApply ty_le_u2aarr|].
      iApply sem_typed_val. iApply add_typed. }
    set add := ("add", add_ty).
    iApply sem_typed_swap_second. 
    iApply (sem_typed_let _ [add; main]); solve_sidecond. 
    { rewrite /next. iApply sem_typed_app_os; [|iApply sem_typed_var].
      iApply sem_typed_sub_ty; [iApply ty_le_u2aarr|].
      iApply sem_typed_val. iApply next_typed. }
    set next := ("next", next_ty).
    iApply sem_typed_swap_second. 
    iApply sem_typed_contraction; solve_sidecond.
    iApply (sem_typed_let _ [add; next; main]); solve_sidecond.
    { iApply sem_typed_app_os; [|iApply sem_typed_var].
      iApply sem_typed_sub_ty; [iApply ty_le_u2aarr|].
      iApply sem_typed_val. iApply resume_task_typed. }
    set resume_task := ("resume_task", resume_task_ty).
    rewrite -/next -/resume_task -/add.
    iApply (sem_typed_let _ [main]); solve_sidecond.
    - assert (Hrw : [resume_task;add;next;main] = [resume_task;add;next] ++ [main]) by done.
      rewrite Hrw. clear Hrw.
      iApply (sem_typed_ufun_poly_rec _ _ _ _ _ (λ β, Promise ('! β)) (λ _, ⟨⟩%R) (λ β, (() -{ asig }-∘ '! β) ⊸ ())); 
        solve_sidecond. simpl.
     iIntros (β) "/=". 
     set promise := ("promise", Promise ('! β)).
     set fulfill := ("fulfill", ∀T: β',, Promise ('! β') → (() -{ asig }-∘ '! β') ⊸ ()).
     rewrite -(app_nil_r [promise;fulfill;resume_task;add;next]).
     iApply sem_typed_afun; solve_sidecond. simpl.
     set comp := ("comp", () -{ asig }-∘ '! β)%T.
     replace ([comp; promise; fulfill; resume_task; add;next]) with
             ([comp] ++ [promise; fulfill; resume_task; add;next]) by done.
     set A := λ (θ : sem_sig Σ) α, ( () -{ ⟨ θ, ⟩ }-∘ '! α ) + Promise ('! α).
     set B := (λ (θ : sem_sig Σ) α, Promise ('! α) + '! α).
     iApply (sem_typed_deep_try_os' _ [] _ _ _ _ _ _ _ A B _ _ ⊥); solve_sidecond.
     + iApply sem_typed_app_os; [iApply sem_typed_sub_nil; iApply sem_typed_var|].
       iApply sem_typed_sub_nil. iApply sem_typed_unit. 
     + iIntros (β').
       iApply sem_typed_swap_third. iApply sem_typed_weaken.
       iApply sem_typed_swap_fourth. iApply sem_typed_weaken.
       set k := ("k", B (μ∀TS: θ, α0, A θ α0 ⇒ B θ α0)%R β' ⊸ ()).
       rewrite -/k -/fulfill -/add -/next.
       iApply (sem_typed_match _ [k; fulfill; add; next]); solve_sidecond; first iApply sem_typed_var.
       * simpl. set x := ("x", () -{ ⟨ μ∀TS: θ, α0, A θ α0 ⇒ B θ α0, ⟩ }-∘ '! β').
         iApply (sem_typed_let _ [x; k; fulfill; add; next] _ _ _ _ (Promise ('! β'))); solve_sidecond.
         { iApply sem_typed_alloc_cpy. iApply sem_typed_right_inj. iApply sem_typed_nil. }
         set new_prom := ("new_prom", Promise ('! β')).
         iApply (sem_typed_seq _ [new_prom; k; next]).
         ** iApply (sem_typed_app_os _ [new_prom; k; add; next]).
            { iApply sem_typed_swap_third.
              iApply sem_typed_sub_ty; [iApply ty_le_u2aarr|iApply sem_typed_var]. }
            iApply sem_typed_swap_fourth. iApply sem_typed_swap_second.
            iApply sem_typed_contraction; solve_sidecond.
            do 2 iApply sem_typed_swap_fourth.
            assert (Hrw : [fulfill; x; new_prom; new_prom; k; add; next] = 
                          [fulfill; x; new_prom] ++ [new_prom; k; add; next]) by done.
            rewrite Hrw. clear Hrw.
            iApply sem_typed_afun; solve_sidecond. simpl.
            do 2 (iApply sem_typed_swap_second; iApply sem_typed_app_os; [|iApply sem_typed_var]).
            rewrite -/asig.
            iApply sem_typed_sub_ty; [iApply ty_le_u2aarr|]. 
            set C := (λ β, Promise ('! β) → (() -{ asig }-∘ '! β) ⊸ ())%T.
            rewrite -/(C β').
            iApply sem_typed_TApp; first solve_copy. iApply sem_typed_var.
         ** iApply (sem_typed_app_os _ [k]); [iApply sem_typed_var|].
            iApply sem_typed_swap_third. iApply sem_typed_weaken.
            iApply sem_typed_left_inj. iApply sem_typed_var.
      * simpl.
        set p := ("p", Promise ('! β')).
        do 2 (iApply sem_typed_swap_third; iApply sem_typed_weaken).
        rewrite -/p -/k.
        iApply (sem_typed_match _ [p;k;next]); solve_sidecond.
        ** iApply sem_typed_replace_cpy; [iApply sem_typed_var|].
           iApply sem_typed_contraction; solve_sidecond.
           iApply sem_typed_right_inj. iApply sem_typed_nil.
        ** simpl. set v := ("v", '! β').
           iApply sem_typed_swap_fourth. iApply sem_typed_weaken.
           iApply sem_typed_contraction; solve_sidecond.
           iApply sem_typed_swap_third.
           iApply sem_typed_swap_second.
           iApply (sem_typed_seq _ [v; k]).
           {  iApply sem_typed_replace_cpy; [iApply sem_typed_var|].
             iApply sem_typed_left_inj. iApply sem_typed_var. }
           iApply sem_typed_app_os; [iApply sem_typed_var|].
           iApply sem_typed_right_inj. iApply sem_typed_var.
        ** simpl. set ks := ("ks", List ('! β' ⊸ ())).
           iApply (sem_typed_seq _ [next] _ _ _ (Status ('! β'))).
           *** iApply sem_typed_swap_third. iApply (sem_typed_replace_cpy _ [p; next]).
               { iApply sem_typed_var. }
               iApply sem_typed_right_inj. 
               rewrite /B /=. iApply sem_typed_swap_second.
               iApply sem_typed_cons; [|iApply sem_typed_var]. 
               assert (Hrw : [k; p; next] = [k] ++ [p;next]) by done.
               rewrite Hrw. clear Hrw.
               iApply sem_typed_afun; solve_sidecond. simpl.
               iApply sem_typed_app_os; [iApply sem_typed_var|].
               iApply sem_typed_right_inj. iApply sem_typed_var.
           *** iApply sem_typed_app_os; [|iApply sem_typed_unit].
               iApply sem_typed_sub_ty; [iApply ty_le_u2aarr|iApply sem_typed_var].
    + simpl. 
      iApply sem_typed_swap_third. iApply sem_typed_weaken.
      iApply sem_typed_swap_fourth; iApply sem_typed_weaken.
      iApply sem_typed_swap_second.
      set x := ("x", '!β). rewrite -/resume_task -/promise.
      iApply (sem_typed_let _ [promise; x; resume_task; next]); solve_sidecond.
      * iApply sem_typed_replace_cpy; [|iApply sem_typed_right_inj; iApply sem_typed_nil].
        iApply sem_typed_contraction; solve_sidecond.
        iApply sem_typed_var.
      * set v := ("v", '! β + (List ('! β ⊸ ()))).
        iApply (sem_typed_match _ [promise; x; resume_task; next]); solve_sidecond;
          [iApply sem_typed_var| |].
        { simpl. do 4 (iApply sem_typed_weaken). iApply impossible_typed. }
        simpl. iApply sem_typed_swap_second. 
        iApply sem_typed_swap_third. iApply sem_typed_contraction; solve_sidecond.
        iApply sem_typed_swap_third. iApply sem_typed_swap_second.
        set ks := ("ks", List ('! β ⊸ ())).
        iApply (sem_typed_seq _ [x; ks; resume_task; next]).
        ** iApply sem_typed_replace_cpy; [iApply sem_typed_var|].
           iApply sem_typed_left_inj. iApply sem_typed_var.
        ** iApply (sem_typed_seq _ [next]).
           2: { iApply sem_typed_app_os; [|iApply sem_typed_unit].
                iApply sem_typed_sub_ty; [iApply ty_le_u2aarr|iApply sem_typed_var]. }
           iApply sem_typed_swap_second.
           iApply (sem_typed_app_os _ _ _ _ _ (List ('! β ⊸ ())) _ ()); [|iApply sem_typed_var].
           iApply (sem_typed_app_os _ [next] _ _ _ (('! β ⊸ ()) → ())%T).
           2: { iApply sem_typed_app_os; [|iApply sem_typed_var]. 
                iApply sem_typed_sub_ty; [iApply ty_le_u2aarr|].
                set C := λ β, ('! β → ('! β ⊸ ()) → ())%T. rewrite -/(C β). simpl.
                iApply sem_typed_TApp; first solve_sidecond. iApply sem_typed_var. }
           iApply sem_typed_sub_ty; [iApply ty_le_u2aarr|].
           set C := (λ (θ : sem_sigs Σ), (('! β ⊸ ()) -{ ⟨θ.1,⟩ }-> ()) → List ('! β ⊸ ()) -{ ⟨θ.1,⟩ }-∘ ())%T.
           rewrite -/(C ⟨⟩%R).
           iApply sem_typed_SApp; first solve_copy. 
           iApply sem_typed_val. iApply iter_typed.
  - set fulfill := ("fulfill", ∀T: α,, Promise ('! α) → (() -{ asig }-∘ '! α) ⊸ ()).
    iApply (sem_typed_let _ [fulfill; main]); solve_sidecond.
    { iApply (sem_typed_alloc_cpy _ _ _ _ (Status ('! α))). 
      iApply sem_typed_right_inj. iApply sem_typed_nil. }
    set pmain := ("pmain", Refᶜ Status ('! α)).
    iApply sem_typed_contraction; solve_sidecond.
    iApply sem_typed_swap_third. iApply sem_typed_swap_second. iApply sem_typed_swap_fourth.
    iApply (sem_typed_seq _ [pmain]).
    + iApply (sem_typed_app_os _ _ _ _ _ _ _ ()); [|iApply sem_typed_var]. 
      iApply sem_typed_app_os; [|iApply sem_typed_var]. 
      iApply sem_typed_sub_ty; [iApply ty_le_u2aarr|].
      set C := (λ α, Promise ('! α) → (() -{ asig }-∘ '! α) ⊸ ())%T.
      rewrite -/(C α).
      iApply sem_typed_TApp; first solve_copy. iApply sem_typed_var.
    + iApply (sem_typed_match _ []); solve_sidecond; simpl; [|iApply sem_typed_var|].
      { iApply sem_typed_replace_cpy; [iApply sem_typed_var|].
        iApply sem_typed_right_inj. iApply sem_typed_nil. }
      iApply impossible_typed. 
      Unshelve.
      { rewrite /A /Promise /Status. intros ???????. by repeat f_equiv. }
      { rewrite /B /Promise /Status. intros ???????. by repeat f_equiv. }
  Qed.
                  
End typing.
