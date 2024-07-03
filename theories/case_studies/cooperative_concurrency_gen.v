
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
From affect.logic Require Import copyable.
From affect.logic Require Import sem_judgement.
From affect.logic Require Import sem_operators.
From affect.logic Require Import compatibility.
From affect.logic Require Import tactics.

(* Make all the definitions opaque so that we do not rely on their definition in the model to show that the programs are well-typed terms. *)
Opaque sem_typed sem_typed_val ty_le row_le sig_le row_type_sub row_env_sub.
Opaque sem_ty_void sem_ty_unit sem_ty_bool sem_ty_int sem_ty_string sem_ty_top sem_ty_cpy sem_env_cpy sem_ty_ref_cpy sem_ty_ref sem_ty_prod sem_ty_sum sem_ty_arr sem_ty_aarr sem_ty_uarr sem_ty_forall sem_ty_row_forall sem_ty_exists sem_ty_rec sem_ty_option sem_ty_list.
Opaque sem_sig_eff sem_sig_os.
Opaque sem_row_nil sem_row_os sem_row_tun sem_row_cons sem_row_rec.

Definition impossible : expr := ((rec: "f" <> := "f" #()) #())%E.

Definition async : val := (Λ: Λ: λ: "c", perform: "async" "c")%V.

Definition await : val := (Λ: Λ: λ: "p", perform: "await" "p")%V.

Definition yield : val := 
  (λ: <>, await <_> <_> (async <_> <_> (λ: <>, #())))%V. 

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
  (Λ: Λ: λ: "main", 
    let: "q" := ref NIL in  

    let: "add" := add "q" in
    let: "next" := next "q" in
    let: "resume_task" := resume_task "add" in

    let: "fulfill" := 
      (rec: "fulfill" <> := λ: "promise" "comp",   
          handle2: "comp" #() by
            "async" => (λ: "x" "k", 
                  let: "new_prom" := ref (InjR NIL) in
                  "add" (λ: <>, "fulfill" <_> "new_prom" "x") ;;
                  "k" "new_prom"
            )
          | "await" => (λ: "x" "k", 
                  match: "x" <!- (InjR NIL) with
                    InjL "v" => "x" <!- (InjL "v") ;; "k" "v"
                  | InjR "ks" => "x" <!- InjR (CONS "k" "ks") ;; "next" #()
                  end
                )
          | ret => (λ: "x", 
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

  Definition Queue θ' := Refᶜ (List (() -{ θ' }-∘ ())).

  Definition Status τ θ' := τ + List (τ -{ θ' }-∘ ()).

  Definition Promise τ θ' := Refᶜ (Status τ θ').

  Definition await_sig θ' : sem_sig Σ := (∀S: α, Promise ('! α) θ' =[ OS ]=> '! α)%S.

  Definition async_sig (θ' θ : sem_row Σ) : sem_sig Σ := 
    (∀S: α, ( () -{ θ }-∘ '! α ) =[ OS ]=> Promise ('! α) θ')%S. 

  Definition coop_pre (θ' θ : sem_row Σ) : sem_row Σ := 
    (("async", async_sig θ' θ) · ("await", await_sig θ') · θ')%R.

  Local Instance promise_ne τ :
    NonExpansive (Promise τ).
  Proof.
    intros ?????. rewrite /Promise. apply non_dep_fun_dist.
    f_equiv. rewrite /Status. by do 3 f_equiv.
  Qed.

  Local Instance await_arg_sig_ne θ' :
    NonExpansive (λ (α : sem_ty Σ), Promise ('! α) θ').
  Proof.
    rewrite /Promise /Status. intros ?????.
    apply non_dep_fun_dist. by repeat f_equiv.
  Qed.

  Local Instance await_res_sig_ne :
    NonExpansive
      (λ (α : sem_ty Σ), '! α).
  Proof.
    intros ????. by repeat f_equiv.
  Qed.

  Local Instance await_sig_ne :
    NonExpansive await_sig.
  Proof.
    rewrite /await_sig. intros ????. 
    apply non_dep_fun_dist. f_equiv.
    rewrite /tele_app; intros ?; destruct x0. by f_equiv.
  Qed.

  Local Instance async_arg_sig_ne θ :
    NonExpansive
      (λ (α : sem_ty Σ), () -{ θ }-∘ '! α).
  Proof.
    intros ?????. apply non_dep_fun_dist.
    do 2 f_equiv; try done. 
  Qed.

  Local Instance async_sig_ne θ' : NonExpansive (async_sig θ').
  Proof.
    intros ????. rewrite /async_sig. f_equiv;
    rewrite /tele_app; intros ?; destruct x0; by f_equiv.
  Qed.

  Local Instance contractive_coop_pre θ' : Contractive (coop_pre θ').
  Proof. 
    intros ????. rewrite /coop_pre. f_equiv. f_equiv. f_equiv. 
    destruct n; first apply dist_later_0.
    apply dist_later_S. rewrite - dist_later_S in H.
    by f_equiv. 
  Qed.

  Definition coop θ' : sem_row Σ := (μR: θ, coop_pre θ' θ)%R.

  Local Instance coop_os_row (θ' : sem_row Σ) `{Once θ'} : Once (coop θ').
  Proof.
    rewrite /coop. apply row_rec_once. iIntros (θ).
    rewrite /coop_pre. apply row_cons_once.
    { rewrite /async_sig. apply sig_eff_os_once; apply _. }
    apply row_cons_once; last apply _.
    apply sig_eff_os_once; apply _.
  Qed.

  Definition iter_ty τ := (∀R: θ, (τ -{ ¡ θ }-> ()) → List τ -{ ¡ θ }-∘ ())%T.
  
  Definition next_ty θ' := (() -{ θ' }-> ())%T.

  Definition add_ty θ' := ((() -{ θ' }-∘ ()) → ())%T.

  Definition resume_task_ty θ' := (∀T: α, '! α → ('! α -{ θ' }-∘ ()) → ())%T.
  
  Definition runner_ty := (∀T: α, ∀R: θ', (() -{ coop θ' }-∘ '! α) -{ θ' }-> '! α)%T.

  Lemma impossible_typed τ :
    ⊢ ⊨ impossible : ⊥ : τ.
  Proof.
    iIntros. rewrite /impossible.
    iApply sem_typed_app_os; [|iApply sem_typed_unit].
    rewrite - {1} (app_nil_r []).
    iApply sem_typed_sub_u2aarr.
    iApply sem_typed_ufun; solve_sidecond. simpl.
    iApply sem_typed_app_os; [|iApply sem_typed_unit].
    iApply sem_typed_sub_u2aarr.
    iApply sem_typed_var.
  Qed.

  Lemma async_typed :
    ⊢ ⊨ᵥ async : (∀R: θ', ∀T: α, (() -{ coop θ' }-∘ '! α) -{ coop θ' }-> Promise ('! α) θ').
  Proof.
    rewrite /async. iIntros.
    iApply sem_typed_Rclosure. iIntros (θ').
    rewrite - {1} (app_nil_r []).
    iApply sem_typed_TLam; first solve_copy. iIntros (α).
    rewrite - {1} (app_nil_r []).
    iApply sem_typed_ufun; solve_sidecond. simpl. rewrite {2} /coop.
    iApply sem_typed_sub_row; first iApply row_le_rec_fold.
    rewrite - {1} /(coop θ') {1} /coop_pre. 
    iApply (sem_typed_perform_os (TT:=[tele _]) [tele_arg (α : sem_ty Σ)] _ "async"
                                 (tele_app (λ α, () -{ coop θ' }-∘ '! α)) (tele_app (λ α, Promise ('! α) θ'))).
    iApply sem_typed_var'.
  Qed.

  Lemma await_typed :
    ⊢ ⊨ᵥ await : (∀R: θ', ∀T: α, Promise ('! α) θ' -{ coop θ' }-> '! α).
  Proof.
    rewrite /await. iIntros.
    iApply sem_typed_Rclosure. iIntros (θ').
    rewrite - {1} (app_nil_r []).
    iApply sem_typed_TLam; first solve_copy. iIntros (α).
    rewrite - {1} (app_nil_r []).
    iApply sem_typed_ufun; solve_sidecond. simpl.
    iApply sem_typed_sub_row; first iApply row_le_rec_fold.
    rewrite - {1} /(coop θ') {1} /coop_pre. 
    iApply sem_typed_sub_row; first iApply row_le_swap_second; first done.
    iApply (sem_typed_perform_os (TT:=[tele _]) [tele_arg (α : sem_ty Σ)] _ "await" 
                                 (tele_app (λ α, Promise ('! α) θ')) (tele_app (λ α, '! α))).
    iApply sem_typed_var'.
  Qed.

  Lemma yield_typed :
    ⊢ ⊨ᵥ yield : ( () -{ coop ⟨⟩ }-> () ).
  Proof.
    iIntros. iApply sem_typed_closure; try done. simpl.
    iApply (sem_typed_app_os (Promise ('! ()) ⟨⟩%R)).
    - iApply sem_typed_sub_u2aarr.
      iApply sem_typed_sub_ty; [iApply ty_le_uarr|]; 
        [iApply row_le_refl|iApply ty_le_refl|iApply ty_le_cpy_elim|].
      iApply sem_typed_sub_nil. simpl. rewrite -/coop.
      set C := (λ θ' α, (Promise ('! α) θ') -{ coop θ' }-> ('! α)).
      rewrite -/(C ⟨⟩%R ()). iApply sem_typed_TApp; first solve_copy.
      set D := (λ ρ, ∀T: α, C ρ α)%T.
      iApply (sem_typed_RApp D); first solve_copy.
      iApply sem_typed_val. iApply await_typed.
    - iApply (sem_typed_app_os (() -{ coop ⟨⟩ }-∘ '! ())).
      + iApply sem_typed_sub_nil. iApply sem_typed_sub_u2aarr.
        set C := (λ θ' α, (() -{ coop θ' }-∘ '! α) -{ coop θ' }-> Promise ('! α) θ').
        rewrite -/(C ⟨⟩%R ()). iApply sem_typed_TApp.
        set D := (λ ρ, ∀T: α, C ρ α)%T.
        iApply (sem_typed_RApp D). iApply sem_typed_val. iApply async_typed.
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
        iApply sem_typed_app_os; [|iApply sem_typed_var'].
        iApply sem_typed_contraction; solve_sidecond.
        simpl. iApply sem_typed_sub_u2aarr.
        iApply sem_typed_var'.
      + iApply sem_typed_swap_second. rewrite -/Γ₂.
        do 2 (iApply sem_typed_app_os; [|iApply sem_typed_var']).
        iApply sem_typed_sub_ty. 
        { iApply ty_le_trans; [|iApply ty_le_u2aarr].
          iApply ty_le_uarr. { simpl. iApply row_le_nil. }
          iApply ty_le_refl. iApply ty_le_refl. }
        iApply sem_typed_var'.
  Qed.

  Definition add_typed θ' :
    ⊢ ⊨ᵥ add : (Queue θ' → add_ty θ').
  Proof.
    iIntros. rewrite /add_ty.
    iApply sem_typed_closure; solve_sidecond. simpl.
    set q := ("q", Queue θ'). rewrite -(app_nil_r [q]).
    iApply sem_typed_ufun; solve_sidecond. simpl.
    set f := ("f", () -{ θ' }-∘ ()).
    iApply sem_typed_seq; [|iApply sem_typed_unit].
    iApply sem_typed_replace_cpy_os; [iApply sem_typed_var|].
    iApply sem_typed_cons.
    { iApply sem_typed_swap_second. iApply sem_typed_var. }
    iApply sem_typed_swap_second.
    iApply sem_typed_replace_cpy_os; [|iApply sem_typed_nil].
    iApply sem_typed_contraction; solve_sidecond.
    iApply sem_typed_var.
  Qed.

  Definition next_typed θ' :
    ⊢ ⊨ᵥ next : (Queue θ' → next_ty θ').
  Proof.
    iIntros. rewrite /next_ty.
    iApply sem_typed_closure; solve_sidecond. simpl.
    set q := ("q", Queue θ'). rewrite -(app_nil_r [q]).
    iApply sem_typed_ufun; solve_sidecond. simpl.
    iApply (sem_typed_match_list _ _ _ _ [q]); solve_sidecond.
    - iApply sem_typed_sub_nil.
      iApply sem_typed_replace_cpy_os; [|iApply sem_typed_nil].
      iApply sem_typed_contraction; solve_sidecond.
      iApply sem_typed_var.
    - iApply sem_typed_weaken. iApply sem_typed_unit'.
    - iApply sem_typed_swap_second.
      iApply sem_typed_swap_third.
      iApply sem_typed_swap_second.
      set x := ("x", () -{ θ' }-∘ ()).
      set xs := ("xs", List (() -{ θ' }-∘ ())).
      rewrite -/q.
      iApply sem_typed_seq.
      { iApply sem_typed_sub_nil. iApply sem_typed_replace_cpy_os; iApply sem_typed_var. }
      iApply (sem_typed_app_ms ()); [solve_copy|solve_sidecond|iApply sem_typed_var'|iApply sem_typed_unit'].
  Qed.

  Definition resume_task_typed θ' :
    ⊢ ⊨ᵥ resume_task : (add_ty θ' → resume_task_ty θ').
  Proof.
    iIntros. rewrite /resume_task_ty.
    iApply sem_typed_closure; solve_sidecond. simpl.
    set add := ("add", add_ty θ')%T. rewrite -(app_nil_r [add]).
    iApply sem_typed_TLam; solve_sidecond. iIntros (α).
    rewrite -(app_nil_r [add]).
    iApply sem_typed_ufun; solve_sidecond. simpl.
    rewrite -(app_nil_r [("v", '! α); add]).
    set v := ("v", '! α).
    iApply sem_typed_ufun; solve_sidecond. simpl.
    set k := ("k", '! α -{ θ' }-∘ ()).
    iApply sem_typed_app_os.
    { iApply sem_typed_sub_u2aarr. iApply sem_typed_var. }
    replace ([k; v; add]) with ([k;v] ++ [add]) by done.
    iApply sem_typed_afun; solve_sidecond. simpl.
    iApply sem_typed_swap_second.
    iApply (sem_typed_app_ms ('! α)%T); solve_sidecond; iApply sem_typed_var'.
  Qed.

  Definition runner_typed :
    ⊢ ⊨ᵥ runner : runner_ty.
  Proof.
    iIntros. iApply sem_typed_Tclosure. iIntros (α).
    rewrite - {1} (app_nil_r []).
    iApply sem_typed_RLam; solve_copy. iIntros (θ').
    rewrite - {1} (app_nil_r []).
    iApply sem_typed_ufun; solve_sidecond. simpl.
    set main := ("main", () -{ coop θ' }-∘ '! α).
    iApply (sem_typed_let _ _ _ _  [main]); solve_sidecond.
    { iApply (sem_typed_alloc_cpy (List (() -{ θ' }-∘ ()))). iApply sem_typed_sub_nil. iApply sem_typed_nil. }
    iApply sem_typed_contraction; solve_sidecond.
    set q := ("q", Queue θ').
    iApply (sem_typed_let _ _ _ _ [q; main]); solve_sidecond.
    { iApply sem_typed_sub_nil.
      iApply sem_typed_app_os; [|iApply sem_typed_var].
      iApply sem_typed_sub_u2aarr.
      iApply sem_typed_val. iApply add_typed. }
    set add := ("add", add_ty θ').
    iApply sem_typed_swap_second. 
    iApply (sem_typed_let _ _ _ _ [add; main]); solve_sidecond. 
    { iApply sem_typed_sub_nil.
      iApply (sem_typed_app_os (Queue θ')); last iApply sem_typed_var'.
      iApply sem_typed_sub_u2aarr.
      iApply sem_typed_val. iApply next_typed. }
    set next := ("next", next_ty θ').
    iApply sem_typed_swap_second. 
    iApply sem_typed_contraction; solve_sidecond.
    iApply (sem_typed_let _ _ _ _ [add; next; main]); solve_sidecond.
    { iApply sem_typed_sub_nil.
      iApply sem_typed_app_os; [|iApply sem_typed_var].
      iApply sem_typed_sub_u2aarr.
      iApply sem_typed_val. iApply resume_task_typed. }
    set resume_task := ("resume_task", resume_task_ty θ').
    rewrite -/next -/resume_task -/add.
    iApply (sem_typed_let _ _ _ _ [main]); solve_sidecond.
    - assert (Hrw : [resume_task;add;next;main] = [resume_task;add;next] ++ [main]) by done.
      rewrite Hrw. clear Hrw.
      iApply sem_typed_sub_nil.
      iApply (sem_typed_ufun_poly_rec 
                (λ β, Promise ('! β) θ') 
                (λ _, ⊥) 
                (λ β, (() -{ coop θ' }-∘ '! β) -{ θ' }-∘ ())); solve_sidecond. simpl.
     iIntros (β) "/=". 
     set promise := ("promise", Promise ('! β) θ').
     set fulfill := ("fulfill", ∀T: β', Promise ('! β') θ' → (() -{ coop θ' }-∘ '! β') -{ θ' }-∘ ()).
     rewrite -(app_nil_r [promise;fulfill;resume_task;add;next]).
     iApply sem_typed_afun; solve_sidecond. simpl.
     set comp := ("comp", () -{ coop θ' }-∘ '! β)%T.
     replace ([comp; promise; fulfill; resume_task; add;next]) with
             ([comp] ++ [promise; fulfill; resume_task; add;next]) by done.
     iApply (sem_typed_handler2 (TT:=[tele _]) OS "async" "await" 
                    (tele_app (λ α, () -{ coop θ' }-∘ '! α)) 
                    (tele_app (λ α, Promise ('! α) θ')) 
                    (tele_app (λ α, Promise ('! α) θ')) 
                    (tele_app (λ α, '! α))  _ _ _ _ [comp] []); solve_sidecond.
     + iApply row_le_refl.
     + iApply (sem_typed_app_ms () _ ('! β)); try solve_copy; [iApply sem_typed_var'|].
       rewrite -/(async_sig θ' (coop θ')) -/(await_sig θ') -/(coop_pre θ' (coop θ')).
       iApply sem_typed_sub_env_final.
       { iApply env_le_cons; first iApply env_le_refl. iApply ty_le_aarr; try iApply ty_le_refl.
         rewrite /coop. iApply (row_le_rec_unfold (coop_pre θ')). }
       iApply sem_typed_unit'.
     + iIntros (β').
       iApply sem_typed_swap_third. iApply sem_typed_weaken.
       iApply sem_typed_swap_fourth. iApply sem_typed_weaken.
       set x := ("x", () -{ coop θ' }-∘ '! β').
       set k := ("k", Promise ('!β') θ' -{ θ' }-∘ ()).
       rewrite -/x -/k -/fulfill -/add -/next.
       iApply (sem_typed_let (Promise ('! β') θ') _ _ _ [x;k;fulfill;add;next]); solve_sidecond. 
       { iApply sem_typed_alloc_cpy. iApply sem_typed_right_inj. iApply sem_typed_sub_nil. iApply sem_typed_nil. }
       set new_prom := ("new_prom", Promise ('! β') θ'). 
       iApply (sem_typed_seq _ _ _ _ [new_prom; k; next]).
       * iApply sem_typed_sub_nil.
         iApply (sem_typed_app_os (() -{ θ' }-∘ ())%T _ () _ [new_prom; k; add; next]).
         { iApply sem_typed_swap_third. iApply sem_typed_sub_u2aarr. iApply sem_typed_var'. }
         iApply sem_typed_swap_fourth. iApply sem_typed_swap_second.
         iApply sem_typed_contraction; solve_sidecond.
         do 2 iApply sem_typed_swap_fourth.
         assert (Hrw : [fulfill; x; new_prom; new_prom; k; add; next] = 
                       [fulfill; x; new_prom] ++ [new_prom; k; add; next]) by done.
         rewrite Hrw. clear Hrw.
         iApply sem_typed_afun; solve_sidecond. simpl.
         iApply sem_typed_swap_second. iApply sem_typed_app_nil; last iApply sem_typed_var'.
         iApply sem_typed_swap_second. iApply sem_typed_app_os; last iApply sem_typed_var'.
         set C := (λ β, Promise ('! β) θ' → (() -{ coop θ' }-∘ '! β) -{ θ' }-∘ ())%T.
         iApply sem_typed_sub_u2aarr. rewrite -/(C β').
         iApply sem_typed_TApp; first solve_copy. iApply sem_typed_var.
      * simpl.
        iApply sem_typed_swap_third. iApply sem_typed_weaken.
        iApply (sem_typed_app_ms (Promise ('! β') θ')); solve_sidecond; iApply sem_typed_var'.
     + iIntros (β').
       set x := ("x", Promise ('! β') θ').
       set k := ("k", '! β' -{ θ' }-∘ ()).
       do 4 (iApply sem_typed_swap_third; iApply sem_typed_weaken).
       iApply (sem_typed_match ('! β') _ _  _ _ [x;k;next]); solve_sidecond.
       * iApply sem_typed_sub_nil.
         iApply sem_typed_replace_cpy_os; first iApply sem_typed_var.
         iApply sem_typed_contraction; solve_sidecond.
         iApply sem_typed_right_inj. iApply sem_typed_nil.
       * simpl. set v := ("v", '! β').
         iApply sem_typed_swap_fourth. iApply sem_typed_weaken.
         iApply sem_typed_contraction; solve_sidecond.
         iApply sem_typed_swap_third. iApply sem_typed_swap_second.
         iApply (sem_typed_seq _ _ _ _ [v; k]).
         { iApply sem_typed_sub_nil.
           iApply sem_typed_replace_cpy_os; [iApply sem_typed_var|].
           iApply sem_typed_left_inj. iApply sem_typed_var. }
         iApply (sem_typed_app_ms ('! β')); solve_sidecond; iApply sem_typed_var'.
       * simpl. set ks := ("ks", List ('! β' -{ θ' }-∘ ())).
         iApply (sem_typed_seq (Status ('! β') θ')).
         ** iApply sem_typed_swap_third. 
            iApply sem_typed_sub_nil.
            iApply sem_typed_replace_cpy_os; first iApply sem_typed_var'.
            iApply sem_typed_right_inj. 
            iApply sem_typed_swap_second.
            iApply sem_typed_cons; [|iApply sem_typed_var]. 
            assert (Hrw : [k; x; next] = [k] ++ [x;next]) by done.
            rewrite Hrw. clear Hrw.
            iApply sem_typed_var.
          ** iApply (sem_typed_app_ms ()); solve_sidecond; [|iApply sem_typed_unit'].
             iApply sem_typed_sub_u2aarr; iApply sem_typed_var'.
    + simpl. 
      iApply sem_typed_swap_third. iApply sem_typed_weaken.
      iApply sem_typed_swap_fourth; iApply sem_typed_weaken.
      iApply sem_typed_swap_second.
      set x := ("x", '!β). rewrite -/resume_task -/promise.
      iApply (sem_typed_let _ _ _ _ [promise; x; resume_task; next]); solve_sidecond.
      * iApply sem_typed_sub_nil.
        iApply sem_typed_replace_cpy_os; [|iApply sem_typed_right_inj; iApply sem_typed_nil].
        iApply sem_typed_contraction; solve_sidecond.
        iApply sem_typed_var.
      * set v := ("v", '! β + (List ('! β -{ θ' }-∘ ()))).
        iApply (sem_typed_match  _ _ _ _ _ [promise; x; resume_task; next]); solve_sidecond;
          [iApply sem_typed_var'| |].
        { simpl. do 4 (iApply sem_typed_weaken). iApply sem_typed_sub_nil. iApply impossible_typed. }
        simpl. iApply sem_typed_swap_second. 
        iApply sem_typed_swap_third. iApply sem_typed_contraction; solve_sidecond.
        iApply sem_typed_swap_third. iApply sem_typed_swap_second.
        set ks := ("ks", List ('! β -{ θ' }-∘ ())).
        iApply (sem_typed_seq _ _ _ _ [x; ks; resume_task; next]).
        ** iApply sem_typed_sub_nil.
           iApply sem_typed_replace_cpy_os; [iApply sem_typed_var|].
           iApply sem_typed_left_inj. iApply sem_typed_var.
        ** iApply (sem_typed_seq ()).
           2: { iApply (sem_typed_app_ms ()); solve_sidecond; [|iApply sem_typed_unit'].
                iApply sem_typed_sub_u2aarr; iApply sem_typed_var'. }
           iApply sem_typed_swap_second.
           iApply sem_typed_sub_nil.
           iApply sem_typed_app_os; [|iApply sem_typed_var].
           iApply (sem_typed_app_os (('! β -{ θ' }-∘ ()) → ())%T).
           2: { iApply sem_typed_app_os; [|iApply sem_typed_var]. 
                iApply sem_typed_sub_u2aarr.
                set C := λ β, ('! β → ('! β -{ θ' }-∘ ()) → ())%T. rewrite -/(C β). simpl.
                iApply sem_typed_TApp; first solve_sidecond. iApply sem_typed_var. }
           iApply sem_typed_sub_u2aarr.
           iApply sem_typed_sub_ty; first iApply ty_le_uarr; 
            [iApply row_le_refl|iApply ty_le_uarr|iApply ty_le_refl|];
            [iApply row_le_os_intro|iApply ty_le_refl|iApply ty_le_refl|].
           iApply sem_typed_sub_ty; first iApply ty_le_uarr; 
            [iApply row_le_refl|iApply ty_le_refl|iApply ty_le_aarr|];
            [iApply row_le_os_elim|iApply ty_le_refl|iApply ty_le_refl|].
            set C := (λ (θ : sem_row Σ), (('! β -{ θ' }-∘ ()) -{ ¡ θ }-> ()) → List ('! β -{θ'}-∘ ()) -{ ¡ θ }-∘ ())%T.
           rewrite -/(C ⊥).
           iApply sem_typed_RApp; first solve_copy. 
           iApply sem_typed_val. iApply iter_typed.
  - set fulfill := ("fulfill", ∀T: α, Promise ('! α) θ' → (() -{ coop θ' }-∘ '! α) -{ θ' }-∘ ()).
    iApply (sem_typed_let _ _ _ _ [fulfill; main]); solve_sidecond.
    { iApply (sem_typed_alloc_cpy (Status ('! α) θ')). 
      iApply sem_typed_right_inj. iApply sem_typed_sub_nil. iApply sem_typed_nil. }
    set pmain := ("pmain", Refᶜ Status ('! α) θ').
    iApply sem_typed_contraction; solve_sidecond.
    iApply sem_typed_swap_third. iApply sem_typed_swap_second. iApply sem_typed_swap_fourth.
    iApply (sem_typed_seq ()).
    + iApply sem_typed_swap_second. iApply sem_typed_frame_ms; solve_copy.
      iApply sem_typed_app_nil; last iApply sem_typed_var'.
      iApply sem_typed_swap_second.
      iApply sem_typed_app_os; last iApply sem_typed_var'.
      iApply sem_typed_sub_u2aarr. 
      set C := (λ α, Promise ('! α) θ' → (() -{ coop θ' }-∘ '! α) -{ θ' }-∘ ())%T.
      rewrite -/(Promise ('! α) θ') -/(C α).
      iApply sem_typed_TApp. rewrite /C /Promise.
      iApply sem_typed_var'.
    + iApply sem_typed_sub_nil.
      iApply (sem_typed_match _ _ _ _ _ []); solve_sidecond; simpl; [|iApply sem_typed_var|].
      { iApply sem_typed_replace_cpy_os; [iApply sem_typed_var|].
        iApply sem_typed_right_inj. iApply sem_typed_nil. }
      iApply impossible_typed. 
  Qed.
                  
End typing.
