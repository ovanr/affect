
# Strong Updates

A strong update allows an update operation to change the type of the reference.
Since the semantics of the language are untyped, strong update is allowed:

In the head_step inductive we have:

```coq
  | StoreS l v σ :
     is_Some (σ.(heap) !! l) →
       head_step (Store (Val $ LitV $ LitLoc l) (Val v)) σ
                 (Val $ LitV LitUnit) (heap_upd <[l:=v]> σ)
```

## Threading references and One-context judgements

In this case, the head_step rule is is not enough to allow for strong update, 
as references because a reference can be shared
across different loads and stores, but the type of the reference 
can change according to the evaluation order.

The typing rule for the copyable references is: 

```
 Γ ⊢ e₁ : ρ : ref τ     Γ ⊢ e₂ : ρ : τ  
-----------------------------------------
          Γ ⊢ e₁ ← e₂ : ρ : ()
```

But a typing rule that allows strong updates should accept a different type for e₂.
But in order to track that the type of the reference has changed the return type
of the judgement should be ref κ.
So the typing rule should be:

```
 Γ ⊢ e₁ : ρ : ref τ     Γ ⊢ e₂ : ρ : κ 
----------------------------------------
        Γ ⊢ e₁ ← e₂ : ρ : ref κ
```

In order for such typing rule to work, we need to track references sub-structurally by threading them.
This is because a reference must be used at most once and its resulting reference after the store must
be used at all times in order to always use the *new* type.

## Sub-Structural references and two-context judgements

An alternative way to supporting strong updates would be by treating
references sub-structurally and having a two-context judgement.
The sub-structural treatment of references does not mean that they have to
be threaded but simply that they are not copyable (even if the inner type is).
In the semantic meaning of references this translates to having a non-persistent
points-to assertion that is not inside an invariant.
By removing the points-to assertion from the invariant we are allowed to
change the type of the reference. 

An additional requirement is that the store typing rule has to be of the form:

```
            Γ; x : ref κ ⊨ e : ρ : τ ⊨ Γ'; x : ref κ'
-------------------------------------------------------------
        Γ; x : ref κ ⊨ x <- e : ρ : () ⊨ Γ'; x : ref τ
```

So the left hand side of the store expression has to be a variable that points to the reference.
This is because we need to capture that the type of the reference changes.


### Observation

By allowing strong-updates in this way we have as a consequence that the lemma: 
```coq
  Lemma sem_typed_sep Γ₁ Γ₂ e ρ τ :
    Γ₁ ⊨ e : ρ : τ ⊨ Γ₂ -∗
    ∃ Γ', Γ₁ ≤E Γ' ++ Γ₂ ∧ Γ' ⊨ e : ρ : τ ⊨ [].
```
does not hold.

A counter-example for this is the following derivation:
```
                        ⋮
    --------------------------------------------------
    (x, ref A), (y : B) ⊨ x <- y : ρ : () ⊨ (x, ref B)
```

We have:
```
Γ₁ = (x, ref A), (y : B)
Γ₂ = (x, ref B)
```

This means that `Γ' = (y, B)`
but we do not have that `(x, ref A), (y : B) ≤E (x, ref B), (y : B)`


### Intermezzo


The contraction rule for the two-context judgement is as follows:

```
    Γ₁; x : κ ⊢ e : ρ : τ ⊢ Γ₂      Copy κ      x ∉ Dom Γ₂
   ----------------------------------------------------------
        Γ₁; x : κ ⊢ e : ρ ⊢ Γ₂; x : κ
```
