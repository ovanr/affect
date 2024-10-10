
From stdpp Require Import base list.
From iris.proofmode Require Import base tactics.
From iris.algebra Require Import excl_auth.

(* Local imports *)
From affect.lib Require Import base.
From affect.lang Require Import affect.
From affect.logic Require Import sem_def.
From affect.logic Require Import sem_env.
From affect.logic Require Import sem_sig.
From affect.logic Require Import mode.
From affect.logic Require Import sem_row.
From affect.logic Require Import sem_types.
From affect.logic Require Import sem_judgement.
From affect.logic Require Import sem_operators.
From affect.logic Require Import compatibility.
From affect.logic Require Import tactics.

(* Make all the definitions opaque so that we do not rely on their definition in the model to show that the programs are well-typed terms. *)
Opaque sem_typed sem_typed_val ty_le row_le sig_le row_type_sub row_env_sub.
Opaque sem_ty_bot sem_ty_unit sem_ty_bool sem_ty_int sem_ty_string sem_ty_top sem_ty_mbang env_mbang sem_ty_ref_cpy sem_ty_ref sem_ty_prod sem_ty_sum sem_ty_arr sem_ty_type_forall sem_ty_row_forall sem_ty_exists sem_ty_rec sem_ty_option.
Opaque sem_sig_eff sem_sig_flip_mbang.
Opaque sem_row_nil sem_row_flip_mbang sem_row_cons sem_row_rec.

Definition impossible : expr := ((rec: "f" <> := "f" #()) #())%E.

Definition async : val := (λ: "c", perform: "async" "c")%V.

Definition await : val := (λ: "p", perform: "await" "p")%V.

Definition yield : val := 
  (λ: <>, await (async (λ: <>, #())))%V. 

Definition iter  : val:= 
  (rec: "f" "g" "xs" := 
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
  (λ: "add", λ: "v" "k", "add" (λ: <>, "k" "v"))%V.

Definition runner : val :=
  (λ: "main", 
    let: "q" := ref NIL in  

    let: "add" := add "q" in
    let: "next" := next "q" in
    let: "resume_task" := resume_task "add" in

    let: "fulfill" := 
      (rec: "fulfill" "promise" := λ: "comp",   
          handle2: "comp" #() by
            "async" => (λ: "x" "k", 
                  let: "new_prom" := ref (InjR NIL) in
                  "add" (λ: <>, "fulfill" "new_prom" "x") ;;
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
                  iter ("resume_task" "x") "ks" ;;
                  "next" #()
              end)%E
          end)
      in
      let: "pmain" := ref (InjR NIL) in
      "fulfill" "pmain" "main" ;;
      match: "pmain" <!- InjR NIL with
        InjL "v" => "v"
      | InjR <> => impossible
      end
  )%V.

Section typing.

  Context `{!heapGS Σ}.

  Definition Queue := Refᶜ (List (𝟙 ⊸ 𝟙)).

  Definition Status τ := τ + List (τ ⊸ 𝟙).

  Definition Promise τ := Refᶜ (Status τ).

  Definition await_sig : sem_sig Σ := (∀ₛ α, (Promise (! α)) =[ OS ]=> (! α))%S.

  Definition async_sig (θ : sem_row Σ) : sem_sig Σ := 
    (∀ₛ α, ( 𝟙 -{ θ }-∘ ! α ) =[ OS ]=> Promise (! α))%S. 

  Definition coop_pre (θ : sem_row Σ) : sem_row Σ := 
    (("async", async_sig θ) · ("await", await_sig) · ⟨⟩)%R.


  Local Instance await_sig_ne :
    NonExpansive (λ (α : sem_ty Σ), Promise (! α)).
  Proof.
    rewrite /Promise /Status. 
    intros ????. by repeat f_equiv.
  Qed.

  Local Instance async_sig_ne θ :
    NonExpansive (λ (α : sem_ty Σ), 𝟙 -{ θ }-∘ ! α).
  Proof.
    intros ????. by repeat f_equiv.
  Qed.

  Local Instance async_sig_2_ne : NonExpansive async_sig.
  Proof.
    rewrite /async_sig.
    intros ?????. apply non_dep_fun_dist.
 f_equiv. rewrite /tele_app. intros []; simpl; apply non_dep_fun_dist;
    repeat f_equiv; intros ?; by repeat f_equiv.
  Qed.

  Local Instance contractive_coop_pre : Contractive coop_pre.
  Proof. 
    intros ????. rewrite /coop_pre. do 3 f_equiv. 
    destruct n; first apply dist_later_0.
    apply dist_later_S. rewrite - dist_later_S in H.
    by f_equiv.
  Qed.

  Definition coop : sem_row Σ := (μᵣ θ, coop_pre θ)%R.

  Local Instance await_res_sig_ne :
    NonExpansive (λ (α : sem_ty Σ), ! α).
  Proof. intros ????. by repeat f_equiv. Qed.

  Local Instance coop_os_row : OnceR coop.
  Proof. apply _. Qed.

  Definition iter_ty τ := (∀ᵣ θ, (τ -{ ¡ θ }-> 𝟙) → List τ -{ ¡ θ }-∘ 𝟙)%T.
  
  Definition next_ty := (𝟙 → 𝟙)%T.

  Definition add_ty := ((𝟙 ⊸ 𝟙) → 𝟙)%T.

  Definition resume_task_ty := (∀ₜ α, ! α → (! α ⊸ 𝟙) → 𝟙)%T.
  
  Definition runner_ty := (∀ₜ α, (𝟙 -{ coop }-∘ ! α) → ! α)%T.

  Lemma impossible_typed τ :
    ⊢ ⊨ impossible : ⟨⟩ : τ.
  Proof.
    iIntros. rewrite /impossible.
    iApply sem_typed_app_os; [|iApply sem_typed_unit].
    rewrite - {1} (app_nil_r []).
    iApply sem_typed_sub_u2aarr.
    smart_apply sem_typed_ufun. simpl.
    iApply sem_typed_app_os; [|iApply sem_typed_unit].
    iApply sem_typed_sub_u2aarr.
    iApply sem_typed_var.
  Qed.

  Lemma async_typed :
    ⊢ ⊨ᵥ async : (∀ₜ α, (𝟙 -{ coop }-∘ ! α) -{ coop }-> Promise (! α)).
  Proof.
    rewrite /async. iIntros.
    iApply sem_typed_Tclosure. iIntros (α).
    smart_apply sem_typed_closure. simpl. rewrite /coop.
    iApply sem_typed_sub_row; first iApply row_le_rec_fold.
    rewrite /coop_pre -/coop.
    iApply (sem_typed_perform_os (TT:=[tele _]) [tele_arg (α : sem_ty Σ)] _ "async"
                                 (tele_app (λ α, 𝟙 -{ coop }-∘ ! α)) (tele_app (λ α, Promise (! α)))).
    iApply sem_typed_var'.
  Qed.

  Lemma await_typed :
    ⊢ ⊨ᵥ await : (∀ₜ α, Promise (! α) -{ coop }-> ! α).
  Proof.
    rewrite /await. iIntros.
    iApply sem_typed_Tclosure. iIntros (α).
    smart_apply sem_typed_closure. simpl.
    iApply sem_typed_sub_row; first iApply row_le_rec_fold.
    rewrite /coop_pre -/coop. 
    iApply sem_typed_sub_row; first iApply row_le_swap_second; first done.
    iApply (sem_typed_perform_os (TT:=[tele _]) [tele_arg (α : sem_ty Σ)] _ "await" 
                                 (tele_app (λ α, Promise (! α))) (tele_app (λ α, ! α))).
    iApply sem_typed_var'.
  Qed.

  Lemma yield_typed :
    ⊢ ⊨ᵥ yield : ( 𝟙 -{ coop }-> 𝟙 ).
  Proof.
    iIntros. iApply sem_typed_closure; first done. simpl.
    iApply (sem_typed_app_os (Promise (! 𝟙))).
    - iApply sem_typed_sub_u2aarr.
      iApply sem_typed_sub_ty; [iApply ty_le_uarr|]; 
        [iApply row_le_refl|iApply ty_le_refl|iApply (ty_le_mbang_elim MS)|].
      iApply sem_typed_sub_nil. simpl. rewrite -/coop.
      set C := (λ α, (Promise (! α)) -{ coop }-> (! α)).
      rewrite -/(C 𝟙). iApply sem_typed_TApp.
      iApply sem_typed_val. iApply await_typed.
    - iApply (sem_typed_app_os (𝟙 -{ coop }-∘ ! 𝟙)).
      + iApply sem_typed_sub_nil. iApply sem_typed_sub_u2aarr.
        set C := (λ α, (𝟙 -{ coop }-∘ ! α) -{ coop }-> Promise (! α)).
        rewrite -/(C 𝟙). iApply sem_typed_TApp.
        iApply sem_typed_val. iApply async_typed.
      + iApply sem_typed_sub_nil.
        rewrite - {1} (app_nil_r []).
        smart_apply sem_typed_afun. simpl.
        iApply sem_typed_sub_ty; [iApply (ty_le_mbang_intro_unit)|].
        iApply sem_typed_unit'.
  Qed.

  Lemma iter_typed τ :
    ⊢ ⊨ᵥ iter : iter_ty τ.
  Proof.
    iApply sem_typed_Rclosure. iIntros (σ).
    iApply sem_typed_closure; first done. simpl.
    rewrite - [[("g", _); ("f", _)]]app_nil_r. 
    smart_apply sem_typed_afun. simpl.
    set Γ₂ := [("g", τ -{ ¡ σ }-> 𝟙);
               ("f", ((τ -{ ¡ σ }-> 𝟙) → List τ -{ ¡ σ }-∘ 𝟙)%T)].
    smart_apply (sem_typed_match_list _ _ _ _ Γ₂).
    - iApply sem_typed_var'.
    - do 2 iApply sem_typed_weaken. iApply sem_typed_unit'.
    - iApply sem_typed_seq.
      + iApply sem_typed_swap_third. iApply sem_typed_swap_second. 
        iApply sem_typed_app_os; [|iApply sem_typed_var'].
        iApply sem_typed_contraction.
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

  Definition add_typed :
    ⊢ ⊨ᵥ add : (Queue → add_ty).
  Proof.
    iIntros. rewrite /add_ty.
    iApply sem_typed_closure; first done. simpl.
    set q := ("q", Queue). rewrite -(app_nil_r [q]).
    smart_apply sem_typed_ufun. simpl.
    set f := ("f", 𝟙 ⊸ 𝟙).
    iApply sem_typed_seq; [|iApply sem_typed_unit].
    iApply sem_typed_replace_cpy_os; [iApply sem_typed_var|].
    iApply sem_typed_cons.
    { iApply sem_typed_swap_second. iApply sem_typed_var. }
    iApply sem_typed_swap_second.
    iApply sem_typed_replace_cpy_os; [|iApply sem_typed_nil].
    iApply sem_typed_contraction.
    iApply sem_typed_var.
  Qed.

  Definition next_typed :
    ⊢ ⊨ᵥ next : (Queue → next_ty).
  Proof.
    iIntros. rewrite /next_ty.
    iApply sem_typed_closure; first done. simpl.
    set q := ("q", Queue). rewrite -(app_nil_r [q]).
    smart_apply sem_typed_ufun. simpl.
    smart_apply (sem_typed_match_list _ _ _ _ [q]).
    - iApply sem_typed_replace_cpy_os; [|iApply sem_typed_nil].
      iApply sem_typed_contraction.
      iApply sem_typed_var.
    - iApply sem_typed_weaken. iApply sem_typed_unit.
    - iApply sem_typed_swap_second.
      iApply sem_typed_swap_third.
      iApply sem_typed_swap_second.
      set x := ("x", 𝟙 ⊸ 𝟙).
      set xs := ("xs", List (𝟙 ⊸ 𝟙)).
      rewrite -/q.
      iApply sem_typed_seq.
      { iApply sem_typed_replace_cpy_os; iApply sem_typed_var. }
      iApply sem_typed_app_os; [iApply sem_typed_var|iApply sem_typed_unit].
  Qed.

  Definition resume_task_typed :
    ⊢ ⊨ᵥ resume_task : (add_ty → resume_task_ty).
  Proof.
    iIntros. rewrite /resume_task_ty.
    iApply sem_typed_closure; first done. simpl.
    set add := ("add", add_ty)%T. rewrite -(app_nil_r [add]).
    iApply sem_typed_oval.
    iApply sem_typed_TLam.
    iIntros (α).
    rewrite -(app_nil_r [add]).
    smart_apply sem_oval_typed_ufun. simpl.
    rewrite -(app_nil_r [("v", ! α); add]).
    set v := ("v", ! α).
    smart_apply sem_typed_ufun. simpl.
    set k := ("k", ! α ⊸ 𝟙).
    iApply sem_typed_app_os.
    { iApply sem_typed_sub_u2aarr. iApply sem_typed_var. }
    replace ([k; v; add]) with ([k;v] ++ [add]) by done.
    smart_apply sem_typed_afun. simpl.
    iApply sem_typed_swap_second.
    iApply sem_typed_app_os; iApply sem_typed_var.
  Qed.

  Definition runner_typed :
    ⊢ ⊨ᵥ runner : runner_ty.
  Proof.
    iIntros. iApply sem_typed_Tclosure. iIntros (α).
    iApply sem_typed_closure; first done. simpl.
    set main := ("main", 𝟙 -{ coop }-∘ ! α).
    smart_apply (sem_typed_let _ _ _ _  [main]).
    { iApply (sem_typed_alloc_cpy (List (𝟙 ⊸ 𝟙))). iApply sem_typed_nil. }
    iApply sem_typed_contraction.
    set q := ("q", Queue).
    smart_apply (sem_typed_let _ _ _ _ [q; main]).
    { iApply sem_typed_app_os; [|iApply sem_typed_var].
      iApply sem_typed_sub_u2aarr.
      iApply sem_typed_val. iApply add_typed. }
    set add := ("add", add_ty).
    iApply sem_typed_swap_second. 
    smart_apply (sem_typed_let _ _ _ _ [add; main]). 
    { rewrite /next. iApply sem_typed_app_os; [|iApply sem_typed_var].
      iApply sem_typed_sub_u2aarr.
      iApply sem_typed_val. iApply next_typed. }
    set next := ("next", next_ty).
    iApply sem_typed_swap_second. 
    iApply sem_typed_contraction.
    smart_apply (sem_typed_let _ _ _ _ [add; next; main]).
    { iApply sem_typed_app_os; [|iApply sem_typed_var].
      iApply sem_typed_sub_u2aarr.
      iApply sem_typed_val. iApply resume_task_typed. }
    set resume_task := ("resume_task", resume_task_ty).
    rewrite -/next -/resume_task -/add.
    smart_apply (sem_typed_let _ _ _ _ [main]).
    - assert (Hrw : [resume_task;add;next;main] = [resume_task;add;next] ++ [main]) by done.
      rewrite Hrw. clear Hrw. iApply sem_typed_oval.
      smart_apply (sem_typed_ufun_poly_rec (λ β, Promise (! β)) (λ _, ⊥) (λ β, (𝟙 -{ coop }-∘ ! β) ⊸ 𝟙)).
     simpl. iIntros (β) "/=". 
     set promise := ("promise", Promise (! β)).
     set fulfill := ("fulfill", ∀ₜ β', Promise (! β') → (𝟙 -{ coop }-∘ ! β') ⊸ 𝟙).
     rewrite -(app_nil_r [promise;fulfill;resume_task;add;next]).
     smart_apply sem_typed_afun. simpl.
     set comp := ("comp", 𝟙 -{ coop }-∘ ! β)%T.
     replace ([comp; promise; fulfill; resume_task; add;next]) with
             ([comp] ++ [promise; fulfill; resume_task; add;next]) by done.
     smart_apply (sem_typed_handler2 (TT:=[tele _]) OS "async" "await" 
                    (tele_app (λ α, 𝟙 -{ coop }-∘ ! α)) 
                    (tele_app (λ α, Promise (! α))) 
                    (tele_app (λ α, Promise (! α))) 
                    (tele_app (λ α, ! α))  _ _ _ _ [comp] []).
     + iApply row_le_refl.
     + iApply (sem_typed_app_os 𝟙 _ (! β)); [iApply sem_typed_var'|]. 
       rewrite -/await_sig -/(async_sig coop) -/coop. 
       iApply sem_typed_sub_env_final; first iApply env_le_cons; first iApply env_le_refl; 
       [iApply ty_le_arr; try iApply ty_le_refl; iApply (row_le_rec_unfold coop_pre)|].
       rewrite -/coop. iApply sem_typed_unit'.
     + iIntros (β').
       iApply sem_typed_swap_third. iApply sem_typed_weaken.
       iApply sem_typed_swap_fourth. iApply sem_typed_weaken.
       set x := ("x", 𝟙 -{ coop }-∘ ! β').
       set k := ("k", Promise (!β') ⊸ 𝟙).
       rewrite -/x -/k -/fulfill -/add -/next.
       smart_apply (sem_typed_let (Promise (! β')) _ _ _ [x;k;fulfill;add;next]).
       { iApply sem_typed_alloc_cpy. iApply sem_typed_right_inj. iApply sem_typed_nil. }
       set new_prom := ("new_prom", Promise (! β')). 
       iApply (sem_typed_seq _ _ _ _ [new_prom; k; next]).
       * iApply (sem_typed_app_os (𝟙 ⊸ 𝟙)%T _ 𝟙 _ [new_prom; k; add; next]).
         { iApply sem_typed_swap_third. iApply sem_typed_sub_u2aarr. iApply sem_typed_var'. }
         iApply sem_typed_swap_fourth. iApply sem_typed_swap_second.
         iApply sem_typed_contraction.
         do 2 iApply sem_typed_swap_fourth.
         assert (Hrw : [fulfill; x; new_prom; new_prom; k; add; next] = 
                       [fulfill; x; new_prom] ++ [new_prom; k; add; next]) by done.
         rewrite Hrw. clear Hrw.
         smart_apply sem_typed_afun. simpl.
         do 2 (iApply sem_typed_swap_second; iApply sem_typed_app_os; [|iApply sem_typed_var]).
         set C := (λ β, Promise (! β) → (𝟙 -{ coop }-∘ ! β) ⊸ 𝟙)%T.
         iApply sem_typed_sub_u2aarr. rewrite -/(C β').
         iApply sem_typed_TApp. iApply sem_typed_var.
      * simpl.
        iApply sem_typed_swap_third. iApply sem_typed_weaken.
        iApply sem_typed_app_os; iApply sem_typed_var'.
     + iIntros (β').
       set x := ("x", Promise (! β')).
       set k := ("k", ! β' ⊸ 𝟙).
       do 4 (iApply sem_typed_swap_third; iApply sem_typed_weaken).
       smart_apply (sem_typed_match (! β') _ _  _ _ [x;k;next]).
       * iApply sem_typed_replace_cpy_os; first iApply sem_typed_var.
         iApply sem_typed_contraction.
         iApply sem_typed_right_inj. iApply sem_typed_nil.
       * simpl. set v := ("v", ! β').
         iApply sem_typed_swap_fourth. iApply sem_typed_weaken.
         iApply sem_typed_contraction.
         iApply sem_typed_swap_third. iApply sem_typed_swap_second.
         iApply (sem_typed_seq _ _ _ _ [v; k]).
         { iApply sem_typed_replace_cpy_os; [iApply sem_typed_var|].
           iApply sem_typed_left_inj. iApply sem_typed_var. }
         iApply sem_typed_app_os; [iApply sem_typed_var|].
         iApply sem_typed_var.
       * simpl. set ks := ("ks", List (! β' ⊸ 𝟙)).
         iApply (sem_typed_seq (Status (! β'))).
         ** iApply sem_typed_swap_third. 
            iApply sem_typed_replace_cpy_os; first iApply sem_typed_var.
            iApply sem_typed_right_inj. 
            iApply sem_typed_swap_second.
            iApply sem_typed_cons; [|iApply sem_typed_var]. 
            assert (Hrw : [k; x; next] = [k] ++ [x;next]) by done.
            rewrite Hrw. clear Hrw.
            iApply sem_typed_var.
          ** iApply sem_typed_app_os; [|iApply sem_typed_unit].
             iApply sem_typed_sub_u2aarr; iApply sem_typed_var.
    + simpl. 
      iApply sem_typed_swap_third. iApply sem_typed_weaken.
      iApply sem_typed_swap_fourth; iApply sem_typed_weaken.
      iApply sem_typed_swap_second.
      set x := ("x", !β). rewrite -/resume_task -/promise.
      smart_apply (sem_typed_let _ _ _ _ [promise; x; resume_task; next]).
      * iApply sem_typed_replace_cpy_os; [|iApply sem_typed_right_inj; iApply sem_typed_nil].
        iApply sem_typed_contraction.
        iApply sem_typed_var.
      * set v := ("v", ! β + (List (! β ⊸ 𝟙))).
        smart_apply (sem_typed_match  _ _ _ _ _ [promise; x; resume_task; next]);
          [iApply sem_typed_var| |].
        { simpl. do 4 (iApply sem_typed_weaken). iApply impossible_typed. }
        simpl. iApply sem_typed_swap_second. 
        iApply sem_typed_swap_third. iApply sem_typed_contraction.
        iApply sem_typed_swap_third. iApply sem_typed_swap_second.
        set ks := ("ks", List (! β ⊸ 𝟙)).
        iApply (sem_typed_seq _ _ _ _ [x; ks; resume_task; next]).
        ** iApply sem_typed_replace_cpy_os; [iApply sem_typed_var|].
           iApply sem_typed_left_inj. iApply sem_typed_var.
        ** iApply (sem_typed_seq 𝟙).
           2: { iApply sem_typed_app_os; [|iApply sem_typed_unit].
                iApply sem_typed_sub_u2aarr; iApply sem_typed_var. }
           iApply sem_typed_swap_second.
           iApply sem_typed_app_os; [|iApply sem_typed_var].
           iApply (sem_typed_app_os ((! β ⊸ 𝟙) → 𝟙)%T).
           2: { iApply sem_typed_app_os; [|iApply sem_typed_var]. 
                iApply sem_typed_sub_u2aarr.
                set C := λ β, (! β → (! β ⊸ 𝟙) → 𝟙)%T. rewrite -/(C β). simpl.
                iApply sem_typed_TApp. iApply sem_typed_var. }
           iApply sem_typed_sub_u2aarr.
           iApply sem_typed_sub_ty; first iApply ty_le_uarr; 
            [iApply row_le_refl|iApply ty_le_uarr|iApply ty_le_refl|];
            [iApply (row_le_mfbang_intro OS)|iApply ty_le_refl|iApply ty_le_refl|].
           iApply sem_typed_sub_ty; first iApply ty_le_uarr; 
            [iApply row_le_refl|iApply ty_le_refl|iApply ty_le_arr|];
            [iApply (@row_le_mfbang_elim _ _ )|iApply ty_le_refl|iApply ty_le_refl|].
           set C := (λ (θ : sem_row Σ), ((! β ⊸ 𝟙) -{ ¡ θ }-> 𝟙) → List (! β ⊸ 𝟙) -{ ¡ θ }-∘ 𝟙)%T.
           rewrite -/(C ⊥).
           iApply sem_typed_RApp.
           iApply sem_typed_val. iApply iter_typed.
  - set fulfill := ("fulfill", ∀ₜ α, Promise (! α) → (𝟙 -{ coop }-∘ ! α) ⊸ 𝟙).
    smart_apply (sem_typed_let _ _ _ _ [fulfill; main]).
    { iApply (sem_typed_alloc_cpy (Status (! α))). 
      iApply sem_typed_right_inj. iApply sem_typed_nil. }
    set pmain := ("pmain", Refᶜ Status (! α)).
    iApply sem_typed_contraction.
    iApply sem_typed_swap_third. iApply sem_typed_swap_second. iApply sem_typed_swap_fourth.
    iApply (sem_typed_seq 𝟙).
    + do 2 (iApply sem_typed_app_os; [|iApply sem_typed_var]). 
      iApply sem_typed_sub_u2aarr. 
      set C := (λ α, Promise (! α) → (𝟙 -{ coop }-∘ ! α) ⊸ 𝟙)%T.
      rewrite -/(C α).
      iApply sem_typed_TApp. rewrite /C /Promise.
      iApply sem_typed_var.
    + smart_apply (sem_typed_match _ _ _ _ _ []); simpl; [|iApply sem_typed_var|].
      { iApply sem_typed_replace_cpy_os; [iApply sem_typed_var|].
        iApply sem_typed_right_inj. iApply sem_typed_nil. }
      iApply impossible_typed. 
  Qed.
                  
End typing.
