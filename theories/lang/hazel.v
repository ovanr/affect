(* hazel.v *)

(* This file imports the Hazel language from coq-hazel
   and additionally defines some extensions to it such as
   the let-pair construct and its eliminator.
*)

From iris.algebra Require Import ofe.
From iris.base_logic Require Export lib.iprop .
From iris.program_logic Require Export language.
From iris.proofmode Require Import base tactics classes.
From program_logic Require Import weakest_precondition.
From iris.heap_lang     Require Export locations.

(* Hazel language *)
From language Require Export eff_lang.
From program_logic Require Import weakest_precondition 
                                  basic_reasoning_rules
                                  deep_handler_reasoning
                                  state_reasoning.

From affine_tes.lib Require Import base.

Definition pair_elim :=
  (λ: "x", λ: "f", "f" (Fst "x") (Snd "x"))%V.

Notation ELetPair x1 x2 e1 e2 := (pair_elim e1 (Lam x1 (Lam x2 e2)))%E.

Notation "'let:' '(' x1 ',' x2 ')' := e1 'in' e2" := (ELetPair x1%binder x2%binder e1%E e2%E)
  (at level 200, x1, x2 at level 1, e1, e2 at level 200,
   format "'[' 'let:'  '(' x1 ',' x2 ')'  :=  '[' e1 ']'  'in'  '/' e2 ']'") : expr_scope.

(* Notations for type abstraction and application *) 
Notation "Λ: e" := (λ: <>, e)%E (at level 200, only parsing) : expr_scope.
Notation "Λ: e" := (λ: <>, e)%V (at level 200, only parsing) : val_scope.
Notation "e '<_>'" := (App e%E #()) (at level 10, only parsing) : expr_scope.

(* Existential type packing and unpacking functions *)
(* Since hazel is an untyped language there is no notion of packing a type 
 * into an existential type nor unpacking an existential type.
 * Instead we define pack/unpack as just the identity and application respectively
 * to simply get a syntactic distinction for when existential pack/unpacking is applied *)
Definition exist_pack : val := (λ: "x", "x")%V.
Definition exist_unpack : val := (λ: "x" "y", "x" "y")%V.

(* Notation for pack and unpack *)
Notation "'pack:' e" := (exist_pack e%E)
  (at level 200, e at level 200,
   format "'[' 'pack:'  e ']'") : expr_scope.

Notation "'unpack:' x := e1 'in' e2" := (exist_unpack (Lam x%binder e2%E) e1%E)
  (at level 200, x at level 1, e1, e2 at level 200,
   format "'[' 'unpack:'  x  :=  '[' e1 ']'  'in'  '/' e2 ']'") : expr_scope.
Notation "'unpack:' x := e1 'in' e2" := (exist_unpack (LamV x%binder e2%E) e1%E)
  (at level 200, x at level 1, e1, e2 at level 200,
   format "'[' 'unpack:'  x  :=  '[' e1 ']'  'in'  '/' e2 ']'") : val_scope.

(* Folding and unfolding recursive types *)
(* Similarly as hazel is untyped we introduce the fold/unfold functions
 * as being the identity functions.
 * This gives us a syntactic distinction for when fold/unfold can be applied
 * which is necessary to trigger a step in the operational semantics and thus
 * remove the ▷ later modality in the recursive type definition. *)
Definition rec_fold : val := (λ: "x", "x")%V.
Definition rec_unfold : val := (λ: "x", "x")%V.

(* Notations for fold and unfold *)
Notation "'fold:' e" := (rec_fold e%E)
  (at level 200, e at level 200,
   format "'[' 'fold:'  e ']'") : expr_scope.

Notation "'unfold:' e" := (rec_unfold e%E)
  (at level 200, e at level 200,
   format "'[' 'unfold:'  e ']'") : expr_scope.

Definition rec_perform : val := (λ: "x", "x")%V.

Notation "'perform:' e" := (rec_perform (Do OS e%E))%E
  (at level 200, e at level 200,
   format "'[' 'perform:'  e ']'") : expr_scope.

(** Notations for lists. *)
Notation NIL := (InjL #()) (only parsing).
Notation NILV := (InjLV #()) (only parsing).
Notation CONS x xs := (InjR (Pair x xs)) (only parsing).
Notation CONSV x xs := (InjRV (PairV x xs)) (only parsing).

Notation ListMatch e1 e2 x e3 := 
  (Case (unfold: e1)%E (Lam BAnon e2) (Lam (BNamed x) (App (App e3 (Fst (Var x))) (Snd (Var x))))) (only parsing).
Notation "'list-match:' e1 'with' 'CONS' x => xs => e3 | 'NIL' => e2 'end'" :=
  (ListMatch e1 e2%E x%binder (Lam x%binder (Lam xs%binder e3%E)))
  (e1, x, xs, e2, e1 at level 200,
   format "'[hv' 'list-match:'  e1  'with'  '/  ' '[' 'CONS'  x  =>  xs  =>  '/  ' e3 ']'  '/' '[' |  'NIL'  =>  '/  ' e2 ']'  '/' 'end' ']'") : expr_scope.

Fixpoint ctx_lambda (domΓ : list string) (e : expr) : expr := 
  match domΓ with 
    [] => e
  | y :: domΓ' => (λ: y, ctx_lambda domΓ' e)%E 
  end.

Fixpoint ctx_lambda_val (domΓ : list string) (v : val) : val := 
  match domΓ with 
    [] => v
  | y :: domΓ' => (λ: y, ctx_lambda_val domΓ' v)%V 
  end.

Notation "λ*: Γ , e" := (ctx_lambda Γ e)%E (at level 200) : expr_scope.
Notation "λ*: Γ , v" := (ctx_lambda_val Γ v)%V (at level 200) : val_scope.

Notation "λλ*: x , Γ , e" := (λ: x, (λ*: Γ, e))%E (at level 200) : expr_scope.
Notation "λλ*: x , Γ , e" := (λ: x, (λ*: Γ, e) )%V (at level 200) : val_scope.

Notation "λ*λ: Γ , x , e" := (λ*: Γ, (λ: x, e))%E (at level 200) : expr_scope.
Notation "λ*λ: Γ , x , e" := (λ*: Γ, (λ: x, e))%V (at level 200) : val_scope.

Notation "λλ*λ: x , Γ , y , e" := (λ: x, (λ*λ: Γ, y, e))%E (at level 200) : expr_scope.
Notation "λλ*λ: x , Γ , y , e" := (λ: x, (λ*λ: Γ, y, e) )%V (at level 200) : val_scope.

Fixpoint app_mult (e : expr) (es : list expr) : expr :=
  match es with 
    [] => e
  | e' :: ees => app_mult (App e e') ees
  end.

(* Use the <_> notation to denote hidden argument application *)
Notation "e '<_' es '_>'" := (app_mult e es)%E (at level 10) : expr_scope.

Definition from_binder (b : binder) (e : expr) : expr :=
  match b with
    BAnon => e
  | BNamed x => Var x
  end.

(* Transforms a function f of type `τ -{ ρ }-∘ () -{ ρ ; Γ₁; Γ₂ }-∘ κ`
   to a function of type `τ -{ ρ ; Γ₁; Γ₂ }-∘ κ` *)
Definition lambdas_norm (f x : string) (Γ : list string) : val :=
   (λλ*λ: f, Γ, x, f x <_ map Var Γ _> #())%V.

Definition RecStar f x Γ e := 
  ((lambdas_norm f x Γ)
    (rec: f x := λ*λ: Γ, <>, let: f := (lambdas_norm f x Γ) f in e%E))%E. 

Notation "rec*: f , Γ , x , e" := (RecStar f x Γ e) (at level 200) : expr_scope.

Definition DeepTryWithAlt e x k xs h y r :=
  (DeepTryWith e
      (λ: (BNamed x) (BNamed k), 
        let: k := (lambdas_norm k x xs) k in h) (λ: y, r) <_ map Var xs _> #())%E.

Notation "'deep-try-alt:' e 'thread' xs 'with' 'effect' k => x => h '|' 'return' y => r 'end'" :=
  (DeepTryWithAlt e x k xs h y r)
  (e, h, k, x, y, r at level 200) : expr_scope.

Global Instance load_atomic (l : loc) :
  Atomic StronglyAtomic (Load $ Val $ LitV $ LitLoc l).
Proof.
  intros ?. simpl. intros ?????. unfold prim_step' in H.
  destruct κ; [|done].
  destruct efs; [|done]. inversion H. simplify_eq.
  destruct k as [|Ki K]; try destruct Ki; try naive_solver.
  - simpl in H0. simpl. simplify_eq. inversion H2. by exists v.
  - simpl in H0. simpl. simplify_eq.
    destruct K as [|Ki K]; try destruct Ki; try naive_solver.
    simpl in H0. simplify_eq. by inversion H2.
Qed.

Global Instance store_atomic (l : loc) (w : val) :
  Atomic StronglyAtomic (Store (Val $ LitV $ LitLoc l) (Val w)).
Proof.
 intros ?. simpl. intros ?????. unfold prim_step' in H.
 destruct κ; [|done].
 destruct efs; [|done]. inversion H. simplify_eq.
 destruct k as [|Ki K]; try destruct Ki; try naive_solver.
 - simpl in H0. simpl. simplify_eq. inversion H2.
   by exists (LitV $ LitUnit).
 - simpl in H0. simpl. simplify_eq.
   destruct K as [|Ki K]; try destruct Ki; try naive_solver.
   simpl in H0. simplify_eq. by inversion H2.
 - simpl in H0. simpl. simplify_eq.
   destruct K as [|Ki K]; try destruct Ki; try naive_solver.
   simpl in H1. simplify_eq. by inversion H2.
Qed.

Global Instance ewp_pre_contractive `{!irisGS eff_lang Σ}: Contractive ewp_pre := 
  weakest_precondition.ewp_pre_contractive.

Global Instance ewp_contractive `{!heapGS Σ}e n Ψ₁ Ψ₂:
  TCEq (to_val e) None →
  TCEq (to_eff e) None →
  Proper (pointwise_relation _ (dist_later n) ==> dist n) (ewp_def ⊤ e Ψ₁ Ψ₂).
Proof.
  intros Hval Heff Φ₁ Φ₂ HΦ. rewrite !ewp_unfold /ewp_pre /=.
  destruct (to_val e) eqn:?; [inversion Hval|].
  destruct (to_eff e) eqn:?; [inversion Heff|].
  do 24 (f_contractive || f_equiv).
  apply HΦ.
Qed.

Lemma ewp_frame_later_l `{irisGS eff_lang Σ} E e Ψ Φ R :
  TCEq (to_val e) None →
  ▷ R -∗ EWP e @ E <| Ψ |> {{ Φ }} -∗ EWP e @ E <| Ψ |> {{ v, R ∗ Φ v }}.
Proof.
  iIntros (Hval) "HR Hewp". rewrite !ewp_unfold {2}/ewp_pre -{1}ewp_unfold.
  destruct (to_val e) eqn:?; first (inversion Hval).
  destruct (to_eff e) eqn:?.
  - simpl. destruct p eqn:?, p0 eqn:?, m.
    + rewrite -(of_to_eff _ _ _ _ Heqo0) -ewp_eff_os_eq /=.
      iDestruct "Hewp" as "(%Φ' & HΨ & Hps)". iExists Φ'. iFrame.
      iIntros (w) "HΦ'". iSpecialize ("Hps" $! w with "HΦ'"). iNext.
      iApply (ewp_frame_l with "HR"). iFrame.
    + rewrite -(of_to_eff _ _ _ _ Heqo0) -ewp_eff_ms_eq /=.
      iDestruct "Hewp" as "(%Φ' & [[] _])". 
  - rewrite ewp_unfold {1}/ewp_pre Heqo Heqo0.
    iIntros (σ₁ ns κ κs nt) "Hσ₁". 
    iMod ("Hewp" $! σ₁ ns κ κs nt with "Hσ₁") as "[Hred Hewp]".
    iIntros "!> {$Hred} %e₂ %σ₂ Hprim /=".
    iSpecialize ("Hewp" $! e₂ σ₂ with "Hprim").
    iMod "Hewp" as "Hewp". iIntros "!> !>".
    iMod "Hewp" as "Hewp". iIntros "!>".
    iInduction (num_laters_per_step) as [|] "IH";
      last (simpl; iApply ("IH" with "HR Hewp")).
    simpl. iMod "Hewp" as "[Hst Hewp]". iIntros "!>".
    iFrame. iApply (ewp_frame_l with "HR Hewp").
Qed.

Lemma ewp_frame_later_r `{irisGS eff_lang Σ} E e Ψ Φ R :
  TCEq (to_val e) None →
  EWP e @ E <| Ψ |> {{ Φ }} -∗ ▷ R -∗ EWP e @ E <| Ψ |> {{ v, Φ v ∗ R }}.
Proof.
  iIntros (Hval) "Hewp HR". 
  iApply (ewp_mono with "[Hewp HR]").
  { iApply (ewp_frame_later_l with "HR Hewp"). }
  iIntros (?) "[HR HΦ] !> {$HR $HΦ}".
Qed.

Lemma fill_not_val e f :
  to_val e = None → to_val (fill f e) = None.
Proof. destruct f; first done; simpl; by destruct f. Qed.

Lemma fill_frame_not_val e f :
  to_val e = None → to_val (fill_frame f e) = None.
Proof. by destruct f. Qed. 

Lemma fill_not_eff e f :
  to_eff e = None → to_eff (fill f e) = None.
Proof. destruct f; first done; simpl; by destruct f. Qed.

Lemma fill_eff e f eff :
  to_eff (fill f e) = Some eff → to_eff e = Some eff.
Proof. induction f; first done; simpl; by destruct a. Qed.

Lemma fill_frame_eff e f eff :
  to_eff (fill_frame f e) = Some eff → to_eff e = Some eff.
Proof. by destruct f. Qed.

Lemma reducible_fill_inv e f σ :
  to_val e = None →
    to_eff e = None →
      reducible (fill f e) σ →
          reducible e σ.
Proof.
  intros ?? Hred; induction f; first done.
  apply IHf. simpl in Hred.
  apply (reducible_fill_frame_inv a); last done.
  { by apply fill_not_val. }
  { by apply fill_not_eff. }
Qed.
