
From iris.proofmode Require Import base tactics.
From iris.algebra Require Import excl_auth.


(* Hazel Reasoning *)
From program_logic Require Import weakest_precondition 
                                  tactics 
                                  shallow_handler_reasoning 
                                  deep_handler_reasoning 
                                  state_reasoning.

(* Local imports *)
From affine_tes.lang Require Import hazel.
From affine_tes.logic Require Import sem_def.
From affine_tes.logic Require Import sem_types.
From affine_tes.logic Require Import sem_sub_typing.
From affine_tes.logic Require Import sem_operators.
From affine_tes.logic Require Import compatibility.

From affine_tes.case_studies Require Import representable.
From affine_tes.case_studies Require Import iterator.
From affine_tes.case_studies Require Import generator.
From affine_tes.case_studies Require Import ghost.

Definition yield := (λ: "x", do: "x")%V.
Definition generate :=
  (λ: "i", let: "yield" := yield in
           let: "cont" := ref (λ: <>, "i" <_> "yield") in
           λ: <>, let: "comp" := Load "cont" in 
             shallow-try: "comp" #() with
                effect λ: "w" "k", "cont" <- "k" ;; SOME "w"
             | return λ: "w", "cont" <- (λ: <>,  #()) ;; NONE
             end
  )%V.

Definition iterate :=
  (λ: "g", 
    (λ: <> "f", 
      (rec: "go" "g" := match: "g" #() with
                           NONE => #()
                        |  SOME "x" => "f" "x" ;; "go" "g"
                        end) "g"))%V.


Section typing.

  Context `{!heapGS Σ}.

  Definition yield_sig (τ : sem_ty Σ) := (τ ⇒ ())%R.
  Definition yield_ty τ := τ -{ yield_sig τ }-> ().
  Definition iter_ty τ := (∀S: θ, (τ -{ θ }-> ()) -{ θ }-∘ ())%T.
  Definition generator_ty τ := (() ∘-> Option τ)%T.
  
  Ltac solve_dom := try 
      (apply not_elem_of_nil) || 
      (apply not_elem_of_cons; split; solve_dom) || 
      (intros ?; match goal with
        | H : (BAnon ∈ env_dom _) |- _ => destruct H
        end) ||
      done.
  
  Ltac solve_sidecond := solve_dom; solve_copy.
  
  Lemma app_singletons {A} (x y : A) : [x;y] = [x] ++ [y].
  Proof. done. Qed.
  
  Lemma sem_typed_generate τ :
    ⊢ ⊨ᵥ generate : (iter_ty τ → generator_ty τ).
  Proof.
    iIntros "". iApply sem_typed_closure.
    iApply (sem_typed_let _ [("i", iter_ty τ)] _ _ _ _ (yield_ty τ)); solve_sidecond. 
    - iApply sem_typed_val. iApply sem_typed_closure.
      iApply sem_typed_do. 
      iApply sem_typed_sub_nil.
      iApply sem_typed_var.
    - set cont_ty := Ref (() -{ yield_sig τ }-∘ ()). 
      iApply (sem_typed_let _ [] _ _ _ _ cont_ty); solve_sidecond.
      + set Γ₁ :=[("yield", yield_ty τ); ("i", iter_ty τ)].
        iApply sem_typed_alloc.
        rewrite -(app_nil_r Γ₁).
        iApply sem_typed_afun; solve_dom.
        iApply (sem_typed_app _ [("i", iter_ty τ)] _ _ _ (yield_ty τ));
          last (iApply sem_typed_sub_nil; iApply sem_typed_var).
          iApply (sem_typed_SApp _ _ _ (yield_sig τ) (λ ρ, ( τ -{ ρ }-> ()) -{ ρ }-∘ ())).
          iApply sem_typed_sub_nil. 
          iApply sem_typed_var.
      + set Γ₁ :=[("cont", cont_ty)]; rewrite -(app_nil_r Γ₁). 
        set in_cont_ty := (() -{ yield_sig τ }-∘ ()).
        iApply sem_typed_sufun; solve_sidecond.
        iApply (sem_typed_let _ [("cont", Ref Moved)] _ _ _ _ in_cont_ty); solve_sidecond.
        { iApply sem_typed_sub_nil. iApply sem_typed_load. }
        rewrite app_singletons.
        iPoseProof (sem_typed_shallow_try 
                      [("comp", in_cont_ty)] [] [("cont", cont_ty)] 
                      [("cont", Ref Moved)]
                      "w" "k" _ _ _ τ () (Option τ) ()) as "Hhand"; solve_sidecond.
        rewrite /Γ₁. iApply "Hhand"; iClear "Hhand".
        * iApply sem_typed_app; iApply sem_typed_sub_nil;
            [iApply sem_typed_var|iApply sem_typed_unit]. 
        * iApply (sem_typed_swap_third).
          iApply sem_typed_seq.
          { iApply sem_typed_store. 
            iApply sem_typed_swap_third.
            iApply sem_typed_var. }
          iApply sem_typed_swap_second.
          iApply sem_typed_some.
          iApply sem_typed_var.
        * iApply sem_typed_weaken.
          iApply sem_typed_seq. 
          iApply sem_typed_store.
          { rewrite -(app_nil_l [("cont", Ref Moved)]). 
            iApply (sem_typed_afun _ _ _ _ () (yield_sig τ) ()); solve_sidecond.
            iApply sem_typed_sub_nil.
            iApply sem_typed_unit. }
          iApply sem_typed_none.
  Qed.
  
  Lemma sem_typed_iterate τ :
    ⊢ ⊨ᵥ iterate : (generator_ty τ → iter_ty τ).
  Proof.
    iIntros. iApply sem_typed_closure. rewrite /iter_ty.
    rewrite {1}(symmetry (app_nil_r [("g", _)])). 
    iApply sem_typed_SLam. iIntros (ρ).
    rewrite {1}(symmetry (app_nil_r [("g", _)])). 
    iApply sem_typed_sub_nil. iApply sem_typed_afun; solve_sidecond.
    iApply sem_typed_app; 
      [|iApply sem_typed_sub_nil; iApply sem_typed_swap_second; iApply sem_typed_var].
    rewrite {1}(symmetry (app_nil_r [("f", _)])). 
    iApply sem_typed_sub_ty; [apply ty_le_u2aarr|].
    iApply sem_typed_sub_nil. iApply sem_typed_ufun; solve_sidecond.
    set Γ₂ := [("g", generator_ty τ); ("go", generator_ty τ -{ ρ }-> () ); ("f", τ -{ ρ }-> ())].
    iApply (sem_typed_match_option _ Γ₂ _ _ _ _ _ () _ τ); solve_sidecond.
    - iApply sem_typed_sub_nil. iApply sem_typed_suapp. iApply sem_typed_unit.
    - iApply sem_typed_sub_nil. do 3 (iApply sem_typed_weaken). iApply sem_typed_unit.
    - iApply sem_typed_seq.
      + iApply sem_typed_app; [|iApply sem_typed_sub_nil; iApply sem_typed_var].
        iApply sem_typed_sub_nil. iApply sem_typed_swap_third. 
        iApply sem_typed_sub_ty; [apply ty_le_u2aarr|]. iApply sem_typed_var.
      + iApply sem_typed_app; [|iApply sem_typed_sub_nil; iApply sem_typed_var].
        iApply sem_typed_sub_nil. iApply sem_typed_sub_ty; [apply ty_le_u2aarr|].
        iApply sem_typed_var.
  Qed.

End typing.

Section verification.
    Context `{!heapGS Σ}.
    Context {G : Type → Type} `{DataStructure Σ G, Iterable G}.
    Context {A : Type} `{Representable Σ A}.
    Context `{!inG Σ (excl_authR (leibnizO (list A)))}.

    Definition isIterCont (l : loc) γ (us : list A) (T : G A) : iProp Σ :=
      ∃ k, l ↦ k ∗ handlerView γ us ∗
                   EWP k #() <| YIELD (iterView γ) T |> {{ _, ∃ us, ⌜complete T us⌝ ∗ (iterView γ) us }}.

    Lemma generate_spec_iter_cont (l : loc) γ (us : list A) (T : G A) :
      let e := 
        (λ: <>, 
          let: "comp" := Load #l in
                shallow-try: "comp" #() with 
                  effect (λ: "w" "k", #l <- "k";; InjR "w")
                | return (λ: "w", #l <- (λ: <>, #());; InjL #())
                end)%V in
      isIterCont l γ us T -∗ isGen e T us.
    Proof. 
      iLöb as "IH" forall (us).
      iIntros "(%k & Hl & Hhand & Hk)".
      rewrite isGen_unfold /isGen_pre.
      ewp_pure_steps. ewp_bind_rule. iApply (ewp_load with "Hl").
      iIntros "!> Hl !> /=". ewp_pure_steps. 
      iApply (ewp_try_with with "Hk").
      iSplit; [|iSplit; iIntros (v c)];
      last (iIntros "?"; by rewrite upcl_bottom).
      - iIntros (v) "(%us' & %Hcompl & Hiter)".
        ewp_pure_steps. ewp_bind_rule. iApply (ewp_store with "Hl").
        iIntros "!> Hl !> /=". ewp_pure_steps. 
        iDestruct (confront_views with "Hhand Hiter") as %->.
        iSplitR; [by iPureIntro|].
        iApply "IH". rewrite /isIterCont.
        iExists (λ: <>, #())%V. iFrame. ewp_pure_steps. iFrame.
        iExists us. iFrame. by iPureIntro.
      - rewrite upcl_yield.
        iIntros "(%us' & %u & %x & -> & (Hxu & %Hperm & Hiter) & HQ)".
        ewp_pure_steps. ewp_bind_rule. iApply (ewp_store with "Hl").
        iDestruct (confront_views with "Hhand Hiter") as %->.
        iIntros "!> Hl".
        iMod (update_cell _ (us ++ [u]) with "Hhand Hiter") as "[Hhand Hiter]".
        iIntros "!> /=". ewp_pure_steps. iExists u. iFrame. 
        iSplit; [by iPureIntro|].
        iApply "IH". rewrite /isIterCont. iExists c. iFrame.
        iApply ("HQ" with "[Hiter]"). iFrame.
    Qed.

  Lemma generate_spec (i : val) (T : G A) :
    isIter i T -∗ EWP (generate i) {{ g, isGen g T [] }}.
  Proof.
    iIntros "Hi". rewrite /generate.
    ewp_pure_steps. ewp_bind_rule. simpl.
    iApply ewp_alloc. iIntros "!> %l Hl".
    iMod (new_cell []) as (γ) "[Hhand Hiter]".
    iIntros "!>". ewp_pure_steps.
    iAssert (isIterCont l γ [] T) with "[Hl Hi Hhand Hiter]" as "H";
    last (by iApply generate_spec_iter_cont).
    rewrite /isIterCont. iExists (λ: <>, i #() (λ: "x", do:"x")%V)%V.
    iFrame. rewrite /isIter.
    set I := (iterView γ).
    iSpecialize ("Hi" $! (YIELD I T) yield I). rewrite /I.
    ewp_pure_steps. rewrite -/yield. iApply ("Hi" with "[] Hiter").
    iIntros "!# %us %u %v %Hperm Hrepr Hiter".
    rewrite /yield. ewp_pure_steps. iApply ewp_do_os.
    rewrite upcl_yield. iExists us,u,v. iSplitR; first done.
    iFrame. iSplitR; first done. 
    iIntros "Hiter {$Hiter}".
  Qed.

  Lemma iterate_spec_helper uus g (f : val) Ψ I (T : G A) :
    □ (∀ (us : list A) (u : A) (v : val),
          ⌜permitted T (us ++ [u])⌝ -∗
          represents v u -∗ I us -∗ EWP f v <| Ψ |> {{ _, I (us ++ [u]) }}) -∗
    isGen g T uus -∗
    I uus -∗
    EWP (rec: "go" "g" :=
          match: "g" #() with InjL <> => #() | InjR "x" => f "x";; "go" "g" end)%V g 
          <| Ψ |> {{ _, ∃ us : list A, ⌜complete T us⌝ ∗ I us }}.
  Proof. 
    iIntros "#Hf Hgen HI".
    iLöb as "IH" forall (uus). 
    rewrite isGen_unfold /isGen_pre; ewp_pure_steps; ewp_bind_rule; 
    iApply (ewp_mono with "[Hgen]"); 
      try (iApply ewp_os_prot_mono; [iApply iEff_le_bottom|iApply "Hgen"]); 
      iIntros "%v Hv !> /="; destruct v eqn:Hv; try done; ewp_pure_steps. 
    - iExists uus. iFrame.
      destruct v0; try done. destruct l; try done.
      by iDestruct "Hv" as "[Hcompl _]". 
    - ewp_bind_rule. 
      iDestruct "Hv" as "(%u & Hrepr & Hperm & Hgen)".
      iApply (ewp_mono with "[Hf Hperm Hrepr HI]").
      { iApply ("Hf" $! uus with "Hperm Hrepr HI"). }
      iIntros (w) "HI !> /=". do 3 ewp_value_or_step.
      iApply ("IH" $! (uus ++ [u]) with "Hgen HI").
  Qed.

  Lemma iterate_spec g (T : G A) :
    isGen g T [] -∗ EWP (iterate g) {{ i, isIter i T }}.
  Proof.
    iIntros "Hgen". rewrite /iterate. ewp_pure_steps.
    rewrite /isIter. iIntros (Ψ f I) "#Hf HI". 
    do 6 ewp_value_or_step.
    iApply (iterate_spec_helper [] with "Hf Hgen HI").
  Qed.

  Lemma generate_iterate_inv i (T : G A) :
    isIter i T -∗ EWP iterate (generate i) {{ i, isIter i T }}.
  Proof.
    iIntros "Hi". ewp_bind_rule.
    iApply (ewp_mono with "[Hi]"). 
    { iApply (generate_spec with "Hi"). }
    iIntros (g) "Hg !> /=".
    by iApply iterate_spec.
  Qed.


  Lemma iterate_generate_inv g (T : G A) :
    isGen g T [] -∗ EWP generate (iterate g) {{ g, isGen g T [] }}.
  Proof.
    iIntros "Hg". ewp_bind_rule.
    iApply (ewp_mono with "[Hg]"). 
    { iApply (iterate_spec with "Hg"). }
    iIntros (i) "Hi !> /=".
    by iApply generate_spec.
  Qed.
    
End verification.
