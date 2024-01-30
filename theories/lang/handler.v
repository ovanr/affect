
(* handler.v *)

(* This file defines the Haffel handlers. *)

From iris.algebra Require Import ofe.
From iris.base_logic Require Export lib.iprop .
From iris.program_logic Require Export language.
From iris.proofmode Require Import base tactics classes.
From iris.heap_lang Require Export locations.

(* Hazel language *)
From hazel.language Require Export eff_lang.
From hazel.program_logic Require Import weakest_precondition 
                                        basic_reasoning_rules
                                        deep_handler_reasoning
                                        tactics
                                        shallow_handler_reasoning
                                        state_reasoning.

From haffel.lib Require Export base logic.

Definition rec_perform : val := (λ: "x", "x")%V.

Notation "'perform:' ( l , e )" := (rec_perform (Do OS ((l, #0)%V, e%E)))%E
  (at level 200, e at level 200,
   format "'[' 'perform:' ( l , e ) ']'") : expr_scope.

Notation "'performₘ:' ( l , e )" := (rec_perform (Do MS ((l, #0)%V, e%E)))%E
  (at level 200, e at level 200,
   format "'[' 'performₘ:' ( l , e ) ']'") : expr_scope.

Notation "'effect' l" := (#(LitStr l))%V (at level 70) : val_scope.
Notation label := (string).

Definition shallow_try_mode : val := (
  λ: "e" "hos" "hms" "r",
    shallow-try: "e" #() with
      effect (λ: "x" "k", 
          if: UnOp IsContOS "k" then
            "hos" "x" "k"
          else
            "hms" "x" "k"
      )
    | return "r" 
    end
)%V.

Arguments shallow_try_mode : simpl never.

Definition ShallowTryMode (e : expr) (hos hms r : expr) : expr :=
  shallow_try_mode (λ: <>, e)%E hos hms r.

Definition ShallowTryModeV (e : expr) (hos hms r : expr) : expr :=
  shallow_try_mode (λ: <>, e)%V hos hms r.

Notation "'shallow-try-mode:' e 'with' 'effect-os' hos | 'effect-ms' hms | 'return' r 'end'" :=
  (ShallowTryMode e hos hms r)
  (e, hos, hms, r at level 200, only parsing) : expr_scope.

Definition deep_try_mode : val := (
    rec: "H" "e" "hos" "hms" "r" := 
      ShallowTryMode ("e" #())
        (λ: "x" "k", "hos" "x" (λ: "y", "H" (λ: <>, "k" "y") "hos" "hms" "r"))
        (λ: "x" "k", "hms" "x" (λ: "y", "H" (λ: <>, "k" "y") "hos" "hms" "r"))
        "r"
)%V.

Arguments deep_try_mode : simpl never.

Definition DeepTryMode (e : expr) (hos hms r : expr) : expr :=
  deep_try_mode (λ: <>, e)%E hos hms r.

Definition DeepTryModeV (e : expr) (hos hms r : expr) : expr :=
  deep_try_mode (λ: <>, e)%V hos hms r.

Notation "'deep-try-mode:' e 'with' 'effect-os' hos | 'effect-ms' hms | 'return' r 'end'" :=
  (DeepTryMode e hos hms r)
  (e, hos, hms, r at level 200, only parsing) : expr_scope.


Definition shallow_handler_mode `{irisGS eff_lang Σ}
  (E : coPset)
  (Ψ1 : iEff Σ)
  (Ψ2 : iEff Σ)
  (Φ : val -d> iPropO Σ)
  (hos hms r : val)
  (Ψ1' : iEff Σ)
  (Ψ2' : iEff Σ)
  (Φ' : val -d> iPropO Σ) : iProp Σ :=

  (* Correctness of the return branch. *)
  (∀ (y : val), Φ y -∗ EWP r y @ E <| Ψ1' |> {| Ψ2' |} {{ Φ' }}) ∧

  (* Correctness of the effect one-shot branch. *)
  (∀ (v k : val),
     iEff_car (upcl OS Ψ1) v (λ w, EWP k w @ E <| Ψ1 |> {| Ψ2 |} {{ Φ }}) -∗
       EWP hos v k @ E <| Ψ1' |> {| Ψ2' |} {{ Φ' }}) ∧

  (* Correctness of the effect multi-shot branch. *)
  (∀ (v k : val),
     iEff_car (upcl MS Ψ2) v (λ w, EWP k w @ E <| Ψ1 |> {| Ψ2 |} {{ Φ }}) -∗
       EWP hms v k @ E <| Ψ1' |> {| Ψ2' |} {{ Φ' }}).

Lemma ewp_try_with_mode `{heapGS Σ} E e Ψ1 Ψ2 Φ (hos hms r : val) Ψ1' Ψ2' Φ' : 
  EWP e @ E <| Ψ1 |> {| Ψ2 |} {{ Φ }} -∗
    shallow_handler_mode E Ψ1 Ψ2 Φ hos hms r Ψ1' Ψ2' Φ' -∗
      EWP (ShallowTryModeV e hos hms r) @ E <| Ψ1' |> {| Ψ2' |} {{ Φ' }}.
Proof.
  iIntros "He H". rewrite /ShallowTryModeV /shallow_try_mode /shallow_handler_mode. 
  ewp_pure_steps. 
  iApply (ewp_try_with with "[He] [H]").
  { ewp_pure_steps. iApply "He". }
  iSplit; last iSplit.
  - iDestruct "H" as "[$ _]". 
  - iIntros (v k) "(%N & %l & ->) HΨ1". 
    iDestruct "H" as "[_ [H _]]". 
    ewp_pure_steps; first done. ewp_pure_steps.
    by iApply "H". 
  - iIntros (v k) "(%N & ->) HΨ1". 
    iDestruct "H" as "[_ [_ H]]". 
    ewp_pure_steps; first done. ewp_pure_steps.
    by iApply "H". 
Qed.

Notation deep_handler_mode_type Σ :=
  (coPset -d> iEff Σ -d> iEff Σ -d> (val -d> iPropO Σ) 
         -d> val -d> val -d> val 
         -d> iEff Σ -d> iEff Σ -d> (val -d> iPropO Σ) -d> iPropO Σ) (only parsing).

Definition deep_handler_mode_pre `{irisGS eff_lang Σ} :
  deep_handler_mode_type Σ → deep_handler_mode_type Σ :=
  (λ deep_handler_mode E Ψ1 Ψ2 Φ hos hms r Ψ1' Ψ2' Φ', 

  (* Correctness of the return branch. *)
  (∀ (y : val), Φ y -∗ EWP r y @ E <| Ψ1' |> {| Ψ2' |} {{ Φ' }}) ∧

  (* Correctness of the effect one-shot branch. *)
  (∀ (v k : val),
     iEff_car (upcl OS Ψ1) v (λ w, 
      ∀ Ψ1'' Ψ2'' Φ'',
        ▷ deep_handler_mode E Ψ1 Ψ2 Φ hos hms r Ψ1'' Ψ2'' Φ'' -∗
        EWP k w @ E <| Ψ1'' |> {| Ψ2'' |} {{ Φ'' }}) -∗
       EWP hos v k @ E <| Ψ1' |> {| Ψ2' |} {{ Φ' }}) ∧

  (* Correctness of the effect multi-shot branch. *)
  (∀ (v k : val),
     iEff_car (upcl MS Ψ2) v (λ w, 
      ∀ Ψ1'' Ψ2'' Φ'',
        ▷ deep_handler_mode E Ψ1 Ψ2 Φ hos hms r Ψ1'' Ψ2'' Φ'' -∗
        EWP k w @ E <| Ψ1'' |> {| Ψ2'' |} {{ Φ'' }}) -∗
       EWP hms v k @ E <| Ψ1' |> {| Ψ2' |} {{ Φ' }}))%I.

Local Instance deep_handler_mode_pre_contractive `{heapGS Σ} : Contractive deep_handler_mode_pre.
Proof.
  rewrite /deep_handler_mode_pre => n deep deep' Hne E Ψ1 Ψ2 Φ h r Ψ1' Ψ2' Φ'.
  repeat (f_contractive || f_equiv). intros ?; simpl.
  repeat (f_contractive || f_equiv); apply Hne.
Qed.
Definition deep_handler_mode `{heapGS Σ} := fixpoint deep_handler_mode_pre.
Arguments deep_handler_mode _ _%ieff _%ieff _%I _%V %V _%V _%ieff _%ieff _%I.

Global Lemma deep_handler_mode_unfold `{heapGS Σ} E Ψ1 Ψ2 Φ hos hms r Ψ1' Ψ2' Φ' :
  deep_handler_mode E Ψ1 Ψ2 Φ hos hms r Ψ1' Ψ2' Φ' ⊣⊢
    deep_handler_mode_pre deep_handler_mode E Ψ1 Ψ2 Φ hos hms r Ψ1' Ψ2' Φ'.
Proof.
  by apply (fixpoint_unfold deep_handler_mode_pre).
Qed.

Lemma ewp_deep_try_with_mode `{heapGS Σ} E e Ψ1 Ψ2 Φ (hos hms r : val) Ψ1' Ψ2' Φ' : 
  EWP e @ E <| Ψ1 |> {| Ψ2 |} {{ Φ }} -∗
    deep_handler_mode E Ψ1 Ψ2 Φ hos hms r Ψ1' Ψ2' Φ' -∗
      EWP (DeepTryModeV e hos hms r) @ E <| Ψ1' |> {| Ψ2' |} {{ Φ' }}.
Proof.
  iIntros "He H". rewrite /DeepTryModeV /deep_try_mode.
  iLöb as "IH" forall (e Ψ1' Ψ2' Φ'). ewp_pure_steps.
  rewrite deep_handler_mode_unfold /deep_handler_mode_pre.
  iApply (ewp_try_with_mode with "[He] [H]").
  { ewp_pure_steps. iApply "He". }
  iSplit; last iSplit.
  - iDestruct "H" as "[$ _]". 
  - iIntros (v k) "/= (%Φ'' & HΨ1 & HPost)". 
    iDestruct "H" as "[_ [H _]]".
    ewp_pure_steps. iApply "H". iExists Φ''. iFrame.
    iIntros (w) "HΦ'' % % %Φ''' Hdeep".
    do 3 ewp_value_or_step.
    iApply ("IH" with "[HΦ'' HPost] Hdeep"); by iApply "HPost".
  - iIntros (v k) "/= (%Φ'' & HΨ2 & #HPost)".
    iDestruct "H" as "[_ [_ H]]".
    ewp_pure_steps. iApply "H". iExists Φ''. iFrame.
    iIntros (w) "!# HΦ'' % % %Φ''' Hdeep".
    do 3 ewp_value_or_step.
    iApply ("IH" with "[HΦ'' HPost] Hdeep"); by iApply "HPost".
Qed.

Definition lft_def : val := 
  (λ: "l'" "e", 
     deep-try-mode: "e" #() with
       effect-os (λ: "x" "k", 
             let: "l" := Fst (Fst "x") in
             let: "s" := Snd (Fst "x") in
             let: "x" := Snd "x" in
             if: "l" = "l'" then
               "k" (Do OS ("l", "s" + #1, "x"))
             else
               "k" (Do OS ("l", "s", "x"))
         )
       | effect-ms (λ: "x" "k", 
             let: "l" := Fst (Fst "x") in
             let: "s" := Snd (Fst "x") in
             let: "x" := Snd "x" in
             if: "l" = "l'" then
               "k" (Do MS ("l", "s" + #1, "x"))
             else
               "k" (Do MS ("l", "s", "x"))
         )
       | return (λ: "x", "x")%V 
      end
)%V.

Notation "'lft:' ( l , e )" := (lft_def l%V (λ: <>, e)%E) (at level 10) : expr_scope.

Definition unlft_def : val := 
  (λ: "l'" "e", 
     deep-try-mode: "e" #() with
       effect-os (λ: "x" "k", 
             let: "l" := Fst (Fst "x") in
             let: "s" := Snd (Fst "x") in
             let: "x" := Snd "x" in
             if: "l" = "l'" then
               "k" (Do OS ("l", "s" - #1, "x"))
             else
               "k" (Do OS ("l", "s", "x"))
         )
       | effect-ms (λ: "x" "k", 
             let: "l" := Fst (Fst "x") in
             let: "s" := Snd (Fst "x") in
             let: "x" := Snd "x" in
             if: "l" = "l'" then
               "k" (Do MS ("l", "s" - #1, "x"))
             else
               "k" (Do MS ("l", "s", "x"))
         )
       | return (λ: "x", "x")%V 
      end
)%V.

Notation "'unlft:' ( l , e )" := (unlft_def l%V (λ: <>, e)%E) (at level 10) : expr_scope.

Definition shallow_try_ls : val := (
  rec: "H" "e" "l'" "h" "r" :=
    shallow_try_mode "e" 
      (λ: "x" "k",
          let: "l" := Fst (Fst "x") in
          let: "s" := Snd (Fst "x") in
          let: "x" := Snd "x" in
          if: ("l" = "l'") && ("s" = #0) then
            "h" "x" "k"
          else
            (λ: "y", "H" (λ: <>, "k" "y") "l'" "h" "r") (unlft: ("l'", Do OS ("l", "s", "x")))
      )%E
      (λ: "x" "k",
          let: "l" := Fst (Fst "x") in
          let: "s" := Snd (Fst "x") in
          let: "x" := Snd "x" in
          if: ("l" = "l'") && ("s" = #0) then
            "h" "x" "k"
          else
            (λ: "y", "H" (λ: <>, "k" "y") "l'" "h" "r") (unlft: ("l'", Do MS ("l", "s", "x")))
      )%E
      "r"
)%V.

Arguments shallow_try_ls : simpl never.

Definition ShallowTryLS (e : expr) (l : label) (h r : expr) : expr :=
  shallow_try_ls (λ: <>, e)%E (effect l)%V h r.

Definition ShallowTryLSV (e : expr) (l : label) (h r : expr) : expr :=
  shallow_try_ls (λ: <>, e)%V (effect l)%V h r.

Notation "'shallow-try-ls:' e 'handle' l 'with' 'effect' h | 'return' r 'end'" :=
  (ShallowTryLS e l h r)
  (e, l, h, r at level 200, only parsing) : expr_scope.

Definition deep_try_ls : val := (
  λ: "e" "l'" "h" "r",
    deep_try_mode "e"
      (λ: "x" "k", 
          let: "l" := Fst (Fst "x") in
          let: "s" := Snd (Fst "x") in
          let: "x" := Snd "x" in
          if: ("l" = "l'") && ("s" = #0) then
            "h" "x" "k"
          else
            "k" (unlft: ("l'", Do OS ("l", "s", "x")))
      )
      (λ: "x" "k", 
          let: "l" := Fst (Fst "x") in
          let: "s" := Snd (Fst "x") in
          let: "x" := Snd "x" in
          if: ("l" = "l'") && ("s" = #0) then
            "h" "x" "k"
          else
            "k" (unlft: ("l'", Do MS ("l", "s", "x")))
      )
      "r" 
)%V.
            
Arguments deep_try_ls : simpl never.

Definition DeepTryLS (e : expr) (l : label) (h r : expr) : expr :=
  deep_try_ls (λ: <>, e)%E (effect l)%V h r.

Definition DeepTryLSV (e : expr) (l : label) (h r : expr) : expr :=
  deep_try_ls (λ: <>, e)%V (effect l)%V h r.

Notation "'deep-try-ls:' e 'handle' l 'with' 'effect' h | 'return' r 'end'" :=
  (DeepTryLS e l h r)
  (e, l, h, r at level 200, only parsing) : expr_scope.

Definition deep_try_ls_2 : val := (
  λ: "e" "l1" "h1" "l2" "h2" "r",
    deep_try_mode "e"
      (λ: "x" "k", 
          let: "l" := Fst (Fst "x") in
          let: "s" := Snd (Fst "x") in
          let: "x" := Snd "x" in
          if: ("l" = "l1") && ("s" = #0) then
            "h1" "x" "k"
          else
            if: ("l" = "l2") && ("s" = #0) then
              "h2" "x" "k"
            else
              "k" (unlft: ("l2", unlft: ("l1", Do OS ("l", "s", "x"))))
      )
      (λ: "x" "k", 
          let: "l" := Fst (Fst "x") in
          let: "s" := Snd (Fst "x") in
          let: "x" := Snd "x" in
          if: ("l" = "l1") && ("s" = #0) then
            "h1" "x" "k"
          else
            if: ("l" = "l2") && ("s" = #0) then
              "h2" "x" "k"
            else
              "k" (unlft: ("l2", unlft: ("l1", Do MS ("l", "s", "x"))))
      )
      "r" 
)%V.
            
Arguments deep_try_ls_2 : simpl never.

Definition DeepTryLS2 (e : expr) (l1 l2 : label) (h1 h2 r : expr) : expr :=
  deep_try_ls_2 (λ: <>, e)%E (effect l1)%V h1 (effect l2)%V h2 r.

Definition DeepTryLS2V (e : expr) (l1 l2 : label) (h1 h2 r : expr) : expr :=
  deep_try_ls_2 (λ: <>, e)%V (effect l1)%V h1 (effect l2)%V h2 r.

Notation "'deep-try-ls2:' e 'with' 'effect' l1 '=>' h1 | 'effect' l2 '=>' h2 | 'return' r 'end'" :=
  (DeepTryLS2 e l1 l2 h1 h2 r)
  (e, l1, h1, l2, h2, r at level 200, only parsing) : expr_scope.
