
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
From haffel.logic Require Import copyable.
From haffel.logic Require Import sem_judgement.
From haffel.logic Require Import sem_operators.
From haffel.logic Require Import compatibility.
From haffel.logic Require Import tactics.

Definition impossible : expr := ((rec: "f" <> := "f" #()) #())%E.

Definition async : val := (Λ: λ: "c", perform: (effect "async", "c"))%V.

Definition await : val := (Λ: λ: "p", perform: (effect "await", "p"))%V.

Definition yield : val := 
  (λ: <>, await <_> (async <_> (λ: <>, #())))%V. 

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
          deep-try-ls2: "comp" #() with
            effect "async" => (λ: "x" "k", 
                  let: "new_prom" := ref (InjR NIL) in
                  "add" (λ: <>, "fulfill" <_> "new_prom" "x") ;;
                  "k" "new_prom"
            )
          | effect "await" => (λ: "x" "k", 
                  match: "x" <!- (InjR NIL) with
                    InjL "v" => "x" <!- (InjL "v") ;; "k" "v"
                  | InjR "ks" => "x" <!- InjR (CONS "k" "ks") ;; "next" #()
                  end
                )
          | return (λ: "x", 
              let: "v" := "promise" <!- InjR NIL in
              match: "v" with
                InjL <> => impossible
              | InjR "ks" =>
                  "promise" <!- InjL "x" ;;
                  iter <_> ("resume_task" <_> "x") "ks" ;;
                  "next" #()
              end)%E
          end)
      in
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

  Definition await_sig : sem_sig Σ := (∀S: α, Promise ('! α) ⇒ '! α | OS)%S.

  Definition async_sig (θ : sem_row Σ) : sem_sig Σ := 
    (∀S: α, ( () -{ θ }-∘ '! α ) ⇒ Promise ('! α) | OS)%S. 

  Definition arow_pre (θ : sem_row Σ) : sem_row Σ := 
    (("async", async_sig θ) ·: ("await", await_sig) ·: ⟨⟩)%R.
  
  Local Instance contractive_arow_pre : Contractive arow_pre.
  Proof.
    intros ????. rewrite /arow_pre. rewrite /sem_row_cons /= /sem_row_ins.
    intros ?. destruct (decide (i = ("async", 0))) as [->|Hneg].
    - rewrite !lookup_insert. f_equiv. rewrite /async_sig.
      rewrite /sem_sig_eff. f_equiv. f_equiv. intros ??. 
      apply non_dep_fun_dist. do 4 f_equiv. f_contractive.
      rewrite /sem_ty_aarr. by do 4 f_equiv.
    - rewrite (lookup_insert_ne _ ("async", 0) i (async_sig y)) //. 
      rewrite (lookup_insert_ne _ ("async", 0) i (async_sig x)) //. 
  Qed.

  Definition arow : sem_row Σ := (μR: θ, arow_pre θ)%R.

  Local Instance await_res_sig_ne :
    NonExpansive
      (λ (α : sem_ty Σ), '! α).
  Proof.
    intros ????. by repeat f_equiv.
  Qed.

  Local Instance await_sig_ne :
    NonExpansive 
    (λ (α : sem_ty Σ), Promise ('! α)).
  Proof.
    rewrite /Promise /Status. intros ?????.
    apply non_dep_fun_dist. by repeat f_equiv.
  Qed.

  Local Instance async_sig_ne θ :
    NonExpansive
      (λ (α : sem_ty Σ), () -{ θ }-∘ '! α).
  Proof.
    intros ?????. apply non_dep_fun_dist.
    do 2 f_equiv; try done. 
  Qed.

  Local Instance arow_os_row : OSRow arow.
  Proof.
    rewrite /arow. apply row_rec_os_row. iIntros (θ).
    rewrite /arow_pre. apply row_ins_os_row.
    { rewrite /async_sig. apply sig_eff_os_os_sig; apply _. }
    simpl. apply row_tun_os_row. apply row_cons_os_row; last apply row_nil_os_row.
    apply sig_eff_os_os_sig; apply _.
  Qed.

  Definition iter_ty τ := (∀R: θ, (τ -{ ¡ θ }-> ()) → List τ -{ ¡ θ }-∘ ())%T.
  
  Definition next_ty := (() → ())%T.

  Definition add_ty := ((() ⊸ ()) → ())%T.

  Definition resume_task_ty := (∀T: α, '! α → ('! α ⊸ ()) → ())%T.
  
  Definition runner_ty := (∀T: α, (() -{ arow }-∘ '! α) → '! α)%T.

  Lemma impossible_typed τ :
    ⊢ ⊨ impossible : ⊥ : τ.
  Proof.
    iIntros. rewrite /impossible.
    iApply sem_typed_app; [|iApply sem_typed_unit].
    rewrite - {1} (app_nil_r []).
    iApply sem_typed_sub_u2aarr.
    iApply sem_typed_ufun; solve_sidecond. simpl.
    iApply sem_typed_app; [|iApply sem_typed_unit].
    iApply sem_typed_sub_u2aarr.
    iApply sem_typed_var.
  Qed.

  Lemma async_typed :
    ⊢ ⊨ᵥ async : (∀T: α, (() -{ arow }-∘ '! α) -{ arow }-> Promise ('! α)).
  Proof.
    rewrite /async. iIntros.
    iApply sem_typed_Tclosure. iIntros (α).
    rewrite - {1} (app_nil_r []).
    iApply sem_typed_ufun; solve_sidecond. simpl. rewrite /arow.
    iApply sem_typed_sub_row; first iApply row_le_rec_fold.
    rewrite /arow_pre -/arow.
    iApply (sem_typed_perform_os α _ "async" (λ α, () -{ arow }-∘ '! α) (λ α, Promise ('! α))).
    iApply sem_typed_var'.
  Qed.

  Lemma await_typed :
    ⊢ ⊨ᵥ await : (∀T: α, Promise ('! α) -{ arow }-> '! α).
  Proof.
    rewrite /await. iIntros.
    iApply sem_typed_Tclosure. iIntros (α).
    rewrite - {1} (app_nil_r []).
    iApply sem_typed_ufun; solve_sidecond. simpl.
    iApply sem_typed_sub_row; first iApply row_le_rec_fold.
    rewrite /arow_pre -/arow. 
    iApply sem_typed_sub_row; first iApply row_le_swap_second; first done.
    iApply (sem_typed_perform_os α _ "await" (λ α, Promise ('! α)) (λ α, '! α)).
    iApply sem_typed_var'.
  Qed.

  Lemma yield_typed :
    ⊢ ⊨ᵥ yield : ( () -{ arow }-> () ).
  Proof.
    iIntros. iApply sem_typed_closure; try done. simpl.
    iApply (sem_typed_app (Promise ('! ()))).
    - iApply sem_typed_sub_u2aarr.
      iApply sem_typed_sub_ty; [iApply ty_le_uarr|]; 
        [iApply row_le_refl|iApply ty_le_refl|iApply ty_le_cpy_elim|].
      iApply sem_typed_sub_nil. simpl. rewrite -/arow.
      set C := (λ α, (Promise ('! α)) -{ arow }-> ('! α)).
      rewrite -/(C ()). iApply sem_typed_TApp; first solve_copy.
      iApply sem_typed_val. iApply await_typed.
    - iApply (sem_typed_app (() -{ arow }-∘ '! ())).
      + iApply sem_typed_sub_nil. iApply sem_typed_sub_u2aarr.
        set C := (λ α, (() -{ arow }-∘ '! α) -{ arow }-> Promise ('! α)).
        rewrite -/(C ()). iApply sem_typed_TApp; first solve_copy.
        iApply sem_typed_val. iApply async_typed.
      + iApply sem_typed_sub_nil.
        rewrite - {1} (app_nil_r []).
        iApply sem_typed_afun; solve_sidecond. simpl.
        iApply sem_typed_sub_ty; [iApply ty_le_cpy_intro; solve_copy|].
        iApply sem_typed_unit'.
  Qed.

  Lemma iter_typed τ :
    ⊢ ⊨ᵥ iter : iter_ty τ.
  Proof.
    iApply sem_typed_Rclosure. iIntros (σ).
    iApply sem_typed_sub_nil.
    rewrite - {1} (app_nil_r []). 
    iApply sem_typed_ufun; solve_sidecond. simpl.
    rewrite - [[("g", _); ("f", _)]]app_nil_r. 
    iApply sem_typed_afun; solve_sidecond. simpl.
    set Γ₂ := [("g", τ -{ ¡ σ }-> ());
               ("f", ((τ -{ ¡ σ }-> ()) → List τ -{ ¡ σ }-∘ ())%T)].
    iApply (sem_typed_match_list _ _ _ _ Γ₂); solve_sidecond.
    - iApply sem_typed_var'.
    - do 2 iApply sem_typed_weaken. iApply sem_typed_unit'.
    - iApply sem_typed_seq.
      + iApply sem_typed_swap_third. iApply sem_typed_swap_second. 
        iApply sem_typed_app; [|iApply sem_typed_var'].
        iApply sem_typed_contraction; solve_sidecond.
        simpl. iApply sem_typed_sub_u2aarr.
        iApply sem_typed_var'.
      + iApply sem_typed_swap_second. rewrite -/Γ₂.
        do 2 (iApply sem_typed_app; [|iApply sem_typed_var']).
        iApply sem_typed_sub_ty. 
        { iApply ty_le_trans; [|iApply ty_le_u2aarr].
          iApply ty_le_uarr. { simpl. iApply row_le_nil. }
          iApply ty_le_refl. iApply ty_le_refl. }
        iApply sem_typed_var'.
  Qed.

  Definition add_typed :
    ⊢ ⊨ᵥ add : (Queue → add_ty).
  Proof.
    iIntros. rewrite /add_ty.
    iApply sem_typed_closure; solve_sidecond. simpl.
    set q := ("q", Queue). rewrite -(app_nil_r [q]).
    iApply sem_typed_ufun; solve_sidecond. simpl.
    set f := ("f", () ⊸ ()).
    iApply sem_typed_seq; [|iApply sem_typed_unit].
    iApply sem_typed_replace_cpy_os; [iApply sem_typed_var|].
    iApply sem_typed_cons.
    { iApply sem_typed_swap_second. iApply sem_typed_var. }
    iApply sem_typed_swap_second.
    iApply sem_typed_replace_cpy_os; [|iApply sem_typed_nil].
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
    iApply (sem_typed_match_list _ _ _ _ [q]); solve_sidecond.
    - iApply sem_typed_replace_cpy_os; [|iApply sem_typed_nil].
      iApply sem_typed_contraction; solve_sidecond.
      iApply sem_typed_var.
    - iApply sem_typed_weaken. iApply sem_typed_unit.
    - iApply sem_typed_swap_second.
      iApply sem_typed_swap_third.
      iApply sem_typed_swap_second.
      set x := ("x", () ⊸ ()).
      set xs := ("xs", List (() ⊸ ())).
      rewrite -/q.
      iApply sem_typed_seq.
      { iApply sem_typed_replace_cpy_os; iApply sem_typed_var. }
      iApply sem_typed_app; [iApply sem_typed_var|iApply sem_typed_unit].
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
    iApply sem_typed_app.
    { iApply sem_typed_sub_u2aarr. iApply sem_typed_var. }
    replace ([k; v; add]) with ([k;v] ++ [add]) by done.
    iApply sem_typed_afun; solve_sidecond. simpl.
    iApply sem_typed_swap_second.
    iApply sem_typed_app; iApply sem_typed_var.
  Qed.

  Definition runner_typed :
    ⊢ ⊨ᵥ runner : runner_ty.
  Proof.
    iIntros. iApply sem_typed_Tclosure. iIntros (α).
    rewrite - {1} (app_nil_r []).
    iApply sem_typed_ufun; solve_sidecond. simpl.
    set main := ("main", () -{ arow }-∘ '! α).
    iApply (sem_typed_let _ _ _ _  [main]); solve_sidecond.
    { iApply (sem_typed_alloc_cpy (List (() ⊸ ()))). iApply sem_typed_nil. }
    iApply sem_typed_contraction; solve_sidecond.
    set q := ("q", Queue).
    iApply (sem_typed_let _ _ _ _ [q; main]); solve_sidecond.
    { iApply sem_typed_app; [|iApply sem_typed_var].
      iApply sem_typed_sub_u2aarr.
      iApply sem_typed_val. iApply add_typed. }
    set add := ("add", add_ty).
    iApply sem_typed_swap_second. 
    iApply (sem_typed_let _ _ _ _ [add; main]); solve_sidecond. 
    { rewrite /next. iApply sem_typed_app; [|iApply sem_typed_var].
      iApply sem_typed_sub_u2aarr.
      iApply sem_typed_val. iApply next_typed. }
    set next := ("next", next_ty).
    iApply sem_typed_swap_second. 
    iApply sem_typed_contraction; solve_sidecond.
    iApply (sem_typed_let _ _ _ _ [add; next; main]); solve_sidecond.
    { iApply sem_typed_app; [|iApply sem_typed_var].
      iApply sem_typed_sub_u2aarr.
      iApply sem_typed_val. iApply resume_task_typed. }
    set resume_task := ("resume_task", resume_task_ty).
    rewrite -/next -/resume_task -/add.
    iApply (sem_typed_let _ _ _ _ [main]); solve_sidecond.
    - assert (Hrw : [resume_task;add;next;main] = [resume_task;add;next] ++ [main]) by done.
      rewrite Hrw. clear Hrw.
      iApply (sem_typed_ufun_poly_rec (λ β, Promise ('! β)) (λ _, ⊥) (λ β, (() -{ arow }-∘ '! β) ⊸ ())); 
        solve_sidecond. simpl.
     iIntros (β) "/=". 
     set promise := ("promise", Promise ('! β)).
     set fulfill := ("fulfill", ∀T: β', Promise ('! β') → (() -{ arow }-∘ '! β') ⊸ ()).
     rewrite -(app_nil_r [promise;fulfill;resume_task;add;next]).
     iApply sem_typed_afun; solve_sidecond. simpl.
     set comp := ("comp", () -{ arow }-∘ '! β)%T.
     replace ([comp; promise; fulfill; resume_task; add;next]) with
             ([comp] ++ [promise; fulfill; resume_task; add;next]) by done.
     iApply (sem_typed_deep_try_2_os OS "async" "await" (λ α, () -{ arow }-∘ '! α) (λ α, Promise ('! α)) (λ α, Promise ('! α)) (λ α, '! α)  _ _ _ _ [comp] []); solve_sidecond.
     { iApply row_le_refl. }
     + iApply (sem_typed_app () _ ('! β)); [iApply sem_typed_var'|]. 
       rewrite -/await_sig -/(async_sig arow) -/arow. 
       iApply sem_typed_sub_env_final; first iApply env_le_cons; first iApply env_le_refl; 
       [iApply ty_le_aarr; try iApply ty_le_refl; iApply (row_le_rec_unfold arow_pre)|].
       rewrite -/arow. iApply sem_typed_unit'.
     + iIntros (β').
       iApply sem_typed_swap_third. iApply sem_typed_weaken.
       iApply sem_typed_swap_fourth. iApply sem_typed_weaken.
       set x := ("x", () -{ arow }-∘ '! β').
       set k := ("k", Promise ('!β') ⊸ ()).
       rewrite -/x -/k -/fulfill -/add -/next.
       iApply (sem_typed_let (Promise ('! β')) _ _ _ [x;k;fulfill;add;next]); solve_sidecond. 
       { iApply sem_typed_alloc_cpy. iApply sem_typed_right_inj. iApply sem_typed_nil. }
       set new_prom := ("new_prom", Promise ('! β')). 
       iApply (sem_typed_seq _ _ _ _ [new_prom; k; next]).
       * iApply (sem_typed_app (() ⊸ ())%T _ () _ [new_prom; k; add; next]).
         { iApply sem_typed_swap_third. iApply sem_typed_sub_u2aarr. iApply sem_typed_var'. }
         iApply sem_typed_swap_fourth. iApply sem_typed_swap_second.
         iApply sem_typed_contraction; solve_sidecond.
         do 2 iApply sem_typed_swap_fourth.
         assert (Hrw : [fulfill; x; new_prom; new_prom; k; add; next] = 
                       [fulfill; x; new_prom] ++ [new_prom; k; add; next]) by done.
         rewrite Hrw. clear Hrw.
         iApply sem_typed_afun; solve_sidecond. simpl.
         do 2 (iApply sem_typed_swap_second; iApply sem_typed_app; [|iApply sem_typed_var]).
         set C := (λ β, Promise ('! β) → (() -{ arow }-∘ '! β) ⊸ ())%T.
         iApply sem_typed_sub_u2aarr. rewrite -/(C β').
         iApply sem_typed_TApp; first solve_copy. iApply sem_typed_var.
      * simpl.
        iApply sem_typed_swap_third. iApply sem_typed_weaken.
        iApply sem_typed_app; iApply sem_typed_var'.
     + iIntros (β').
       set x := ("x", Promise ('! β')).
       set k := ("k", '! β' ⊸ ()).
       do 4 (iApply sem_typed_swap_third; iApply sem_typed_weaken).
       iApply (sem_typed_match ('! β') _ _  _ _ [x;k;next]); solve_sidecond.
       * iApply sem_typed_replace_cpy_os; first iApply sem_typed_var.
         iApply sem_typed_contraction; solve_sidecond.
         iApply sem_typed_right_inj. iApply sem_typed_nil.
       * simpl. set v := ("v", '! β').
         iApply sem_typed_swap_fourth. iApply sem_typed_weaken.
         iApply sem_typed_contraction; solve_sidecond.
         iApply sem_typed_swap_third. iApply sem_typed_swap_second.
         iApply (sem_typed_seq _ _ _ _ [v; k]).
         { iApply sem_typed_replace_cpy_os; [iApply sem_typed_var|].
           iApply sem_typed_left_inj. iApply sem_typed_var. }
         iApply sem_typed_app; [iApply sem_typed_var|].
         iApply sem_typed_var.
       * simpl. set ks := ("ks", List ('! β' ⊸ ())).
         iApply (sem_typed_seq (Status ('! β'))).
         ** iApply sem_typed_swap_third. 
            iApply sem_typed_replace_cpy_os; first iApply sem_typed_var.
            iApply sem_typed_right_inj. 
            iApply sem_typed_swap_second.
            iApply sem_typed_cons; [|iApply sem_typed_var]. 
            assert (Hrw : [k; x; next] = [k] ++ [x;next]) by done.
            rewrite Hrw. clear Hrw.
            iApply sem_typed_var.
          ** iApply sem_typed_app; [|iApply sem_typed_unit].
             iApply sem_typed_sub_u2aarr; iApply sem_typed_var.
    + simpl. 
      iApply sem_typed_swap_third. iApply sem_typed_weaken.
      iApply sem_typed_swap_fourth; iApply sem_typed_weaken.
      iApply sem_typed_swap_second.
      set x := ("x", '!β). rewrite -/resume_task -/promise.
      iApply (sem_typed_let _ _ _ _ [promise; x; resume_task; next]); solve_sidecond.
      * iApply sem_typed_replace_cpy_os; [|iApply sem_typed_right_inj; iApply sem_typed_nil].
        iApply sem_typed_contraction; solve_sidecond.
        iApply sem_typed_var.
      * set v := ("v", '! β + (List ('! β ⊸ ()))).
        iApply (sem_typed_match  _ _ _ _ _ [promise; x; resume_task; next]); solve_sidecond;
          [iApply sem_typed_var| |].
        { simpl. do 4 (iApply sem_typed_weaken). iApply impossible_typed. }
        simpl. iApply sem_typed_swap_second. 
        iApply sem_typed_swap_third. iApply sem_typed_contraction; solve_sidecond.
        iApply sem_typed_swap_third. iApply sem_typed_swap_second.
        set ks := ("ks", List ('! β ⊸ ())).
        iApply (sem_typed_seq _ _ _ _ [x; ks; resume_task; next]).
        ** iApply sem_typed_replace_cpy_os; [iApply sem_typed_var|].
           iApply sem_typed_left_inj. iApply sem_typed_var.
        ** iApply (sem_typed_seq ()).
           2: { iApply sem_typed_app; [|iApply sem_typed_unit].
                iApply sem_typed_sub_u2aarr; iApply sem_typed_var. }
           iApply sem_typed_swap_second.
           iApply sem_typed_app; [|iApply sem_typed_var].
           iApply (sem_typed_app (('! β ⊸ ()) → ())%T).
           2: { iApply sem_typed_app; [|iApply sem_typed_var]. 
                iApply sem_typed_sub_u2aarr.
                set C := λ β, ('! β → ('! β ⊸ ()) → ())%T. rewrite -/(C β). simpl.
                iApply sem_typed_TApp; first solve_sidecond. iApply sem_typed_var. }
           iApply sem_typed_sub_u2aarr.
           iApply sem_typed_sub_ty; first iApply ty_le_uarr; 
            [iApply row_le_refl|iApply ty_le_uarr|iApply ty_le_refl|];
            [iApply row_le_os_intro|iApply ty_le_refl|iApply ty_le_refl|].
           iApply sem_typed_sub_ty; first iApply ty_le_uarr; 
            [iApply row_le_refl|iApply ty_le_refl|iApply ty_le_aarr|];
            [iApply row_le_os_elim|iApply ty_le_refl|iApply ty_le_refl|].
           set C := (λ (θ : sem_row Σ), (('! β ⊸ ()) -{ ¡ θ }-> ()) → List ('! β ⊸ ()) -{ ¡ θ }-∘ ())%T.
           rewrite -/(C ⊥).
           iApply sem_typed_RApp; first solve_copy. 
           iApply sem_typed_val. iApply iter_typed.
  - set fulfill := ("fulfill", ∀T: α, Promise ('! α) → (() -{ arow }-∘ '! α) ⊸ ()).
    iApply (sem_typed_let _ _ _ _ [fulfill; main]); solve_sidecond.
    { iApply (sem_typed_alloc_cpy (Status ('! α))). 
      iApply sem_typed_right_inj. iApply sem_typed_nil. }
    set pmain := ("pmain", Refᶜ Status ('! α)).
    iApply sem_typed_contraction; solve_sidecond.
    iApply sem_typed_swap_third. iApply sem_typed_swap_second. iApply sem_typed_swap_fourth.
    iApply (sem_typed_seq ()).
    + do 2 (iApply sem_typed_app; [|iApply sem_typed_var]). 
      iApply sem_typed_sub_u2aarr. 
      set C := (λ α, Promise ('! α) → (() -{ arow }-∘ '! α) ⊸ ())%T.
      rewrite -/(C α).
      iApply sem_typed_TApp. rewrite /C /Promise.
      iApply sem_typed_var.
    + iApply (sem_typed_match _ _ _ _ _ []); solve_sidecond; simpl; [|iApply sem_typed_var|].
      { iApply sem_typed_replace_cpy_os; [iApply sem_typed_var|].
        iApply sem_typed_right_inj. iApply sem_typed_nil. }
      iApply impossible_typed. 
  Qed.
                  
End typing.
