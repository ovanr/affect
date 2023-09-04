From stdpp Require Import list.

(* Hazel Reasoning *)
From program_logic Require Import state_reasoning.

From iris.proofmode Require Import base tactics.
From iris.algebra Require Import excl_auth.

Section ghost_theory.
  Context {A : Type}.

  (* We use ghost variables with contents in the CMRA [Auth(Ex(List A))]. *)
  Context `{!inG Σ (excl_authR (leibnizO (list A)))}.

  (* The assertion [own γ (●E Ys)] states that the handler
     has seen the elements [Ys]. *)
  Definition handlerView γ Ys : iProp Σ :=
    own γ (●E (Ys : ofe_car (leibnizO (list A)))).
  (* The assertion [own γ (◯E Xs)] states that [iter]
     has seen the elements [Xs]. *)
  Definition iterView γ Xs : iProp Σ :=
    own γ (◯E (Xs : ofe_car (leibnizO (list A)))).

  (* Create a new ghost cell from this CMRA. *)
  (* In the verification of [invert], the ghost variable [γ]
     initially holds the empty list. *)
  Lemma new_cell Zs : ⊢ (|==> ∃ γ, handlerView γ Zs ∗ iterView γ Zs)%I.
  Proof.
    iMod (own_alloc ((●E (Zs : ofe_car (leibnizO (list A)))) ⋅
                     (◯E (Zs : ofe_car (leibnizO (list A)))))) as (γ) "[??]";
    [ apply excl_auth_valid | eauto with iFrame ]; done.
  Qed.

  (* Handler and [iter]'s views are in agreement. *)
  Lemma confront_views γ Ys Xs :
    handlerView γ Ys -∗ iterView γ Xs -∗ ⌜ Xs = Ys ⌝.
  Proof.
    iIntros "Hγ● Hγ◯".
    by iDestruct (own_valid_2 with "Hγ● Hγ◯") as %?%excl_auth_agree_L.
  Qed.

  (* With the ownership of both views, one can update the contents of [γ]. *)
  Lemma update_cell γ Zs Ys Xs :
    handlerView γ Ys -∗ iterView γ Xs ==∗ handlerView γ Zs  ∗ iterView γ Zs.
  Proof.
    iIntros "Hγ● Hγ◯".
    iMod (own_update_2 _ _ _ (●E (Zs : ofe_car (leibnizO (list A))) ⋅
                              ◯E (Zs : ofe_car (leibnizO (list A))))
      with "Hγ● Hγ◯") as "[$$]";
    [ apply excl_auth_update |]; done.
  Qed.
End ghost_theory.
