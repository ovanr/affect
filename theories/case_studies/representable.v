
From iris.proofmode Require Import base tactics.

(* Hazel Reasoning *)
From hazel.program_logic Require Import weakest_precondition 
                                        state_reasoning.
(* Local imports *)
From affine_tes.lang Require Import hazel.


(* Inhabitants of a representable type can be identified by values in Hazel *)
Class Representable Σ (A : Type) :=
    represents : val → A → iProp Σ.

(* Inhabitants of a persistently representable type are representable types
 * where their representation is non-persistent *)
Class PersRepresentable Σ A `{Representable Σ A} :=
    pers_representable x X :> Persistent (represents x X).

(* A DataStructure is a container T over types τ such that
   if τ is representable then T α is also representable. *)
Class DataStructure Σ (G : Type → Type) :=
    is_representable A `{Representable Σ A} :> Representable Σ (G A).

(* A persistent DataStructure is a datastructure such that if the inner type 
   is persistently representable then so is the whole structure *)
Class PersDataStructure Σ (G : Type → Type) `{DataStructure Σ G} :=
    is_pers_representable A `{PersRepresentable Σ A} :> PersRepresentable Σ (G A).

(* An iterable container G is one that can be described using 
   the two predicates `permitted` and `complete`:
    ∙ `permitted T xs` says that xs could be a possible prefix 
                       of the visited elements in T
    ∙ `complete T xs` says that xs describes all the elements of T *)
Class Iterable (G : Type → Type) := {
  permitted {A : Type} : G A → list A → Prop;
  complete {A : Type} : G A → list A → Prop
}.

Section linked_list.

  Context `{!heapGS Σ}.

  Global Instance BoolRepresentable : Representable Σ bool := λ v b, (⌜ v = #b ⌝)%I.
  Global Instance NatRepresentable : Representable Σ nat := λ v i, (⌜ v = #i ⌝)%I.

  Global Instance BoolPersRepresentable : PersRepresentable Σ bool. 
  Proof. intros ??. apply bi.pure_persistent. Qed.

  Global Instance NatPersRepresentable : PersRepresentable Σ nat. 
  Proof. intros ??. apply bi.pure_persistent. Qed.

  Global Instance ListDataStructure A `{Representable Σ A} : DataStructure Σ list :=
  fix go A `{Representable Σ A} (v : val) (us : list A) : iProp Σ :=
    match us with
    | [] => ⌜v = NILV⌝%I
    | u :: uus =>
        (∃ (x : val) (l : loc) (tl : val), represents x u ∗ ⌜
           v = CONSV x #l⌝ ∗ l ↦ tl ∗ go A tl uus)%I
    end.

  Global Instance ListIterable : Iterable list := { 
      permitted := λ _ t xs, ∃ zs, xs ++ zs = t;
      complete := λ _ t xs , xs = t
  }.

End linked_list.
