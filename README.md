# Affect

This artifact provides the Coq formalisation of the paper "Affect: An Affine Type and Effect System".

# Installation

## Building on local machine

Run the `install.sh` to automatically install Affect.
Alternatively follow these instructions.

Make sure that opam (tested using version 2.2.1) is installed and initialised (`opam init`) on your system.
Create a new opam switch:
```bash
opam switch create affect \
  --no-install \
  --repositories=default,coq-released=https://coq.inria.fr/opam/released,iris-dev=git+https://gitlab.mpi-sws.org/iris/opam.git \
  ocaml-base-compiler.5.0.0
eval "$(opam env --switch=affect)"
```

`Affect` relies on `coq-hazel` a separation logic library for effect handlers. 
To install `coq-hazel` we need to manually fetch it and apply three patches (this can take 5-10 minutes).
```bash
git clone https://gitlab.inria.fr/cambium/hazel
## If gitlab.inria.fr is down use local hazel copy: 
# tar xzf hazel-local-copy.tar.gz
cd hazel
git checkout 0936b5dc00b5d0b5802e7ca8e3dbd5afeafd970e
git am --whitespace=nowarn ../hazel-patches/0001-Bumps-Iris-version-to-dev.2024-10-07.0.6dece417.patch
git am --whitespace=nowarn ../hazel-patches/0001-Adds-a-Replace-e1-e2-construct.patch
git am --whitespace=nowarn ../hazel-patches/0001-Add-IsContOS-unary-operation-and-specialised-shallow.patch
opam install . 
cd ..
```

Compile `Affect` (this can take up to 10 minutes).
By default all case studies are compiled. 
You can omit them from the compilation by commenting their corresponding line in `_CoqProject`.
```bash
make -j 4
```

## Using the VirtualBox image

Download the virtualbox image (`ubuntu20.04lts-affect.ova`) from [zenodo](https://zenodo.org/uploads/13907548) and import as appliance in VirtualBox 7.1. 
The username and password is `affect` in both cases and the formalisation can be found at `/home/affect/affect`. 
CoqIDE is also installed which you can use to explore the Coq code.

# Supporting the claims of the paper

To support the claims of the paper, in this section we explain how definitions/theorems in the paper correspond to the ones in the Coq formalisation. 
We note that all Coq proofs have been proven without using any `admit`/`Admitted`.

In addition to [Iris](https://gitlab.mpi-sws.org/iris/iris) we rely on [Hazel](https://gitlab.inria.fr/cambium/hazel) [1]: an untyped language with effect handlers and a program logic for it formalised in Coq.
The Affect language is encoded into the Hazel language and follows similar semantics as Hazel.
We expand and adjust the Hazel program logic to reason about Affect programs. 
Note that during installation the `hazel` directory will be created that stores a local (patched) copy of the `coq-hazel` library.

[1]: de Vilhena, P. E., & Pottier, F. (2021). A separation logic for effect handlers. Proceedings of the ACM on Programming Languages, 5(POPL), 1-28.

## Overall Project Structure

|  Definition/Theorem                                                         | File
| --------------------------------------------------------------------------- | -----------------------------------------------------
|  Semantic definitions of types, signatures, rows and relations              | `theories/logic/sem_def.v`
|  Type instances and their relations                                         | `theories/logic/sem_types.v`
|  Signatures instances and their relations                                   | `theories/logic/sem_sig.v`
|  Rows instances and their relations                                         | `theories/logic/sem_row.v`
|  Environments instances and their relations                                 | `theories/logic/sem_env.v`
|  Typing Judgements                                                          | `theories/logic/sem_judgement.v`
|  Typing Rules                                                               | `theories/logic/compatibility.v`
|  Soundness Theorem of typing judgment                                       | `sem_typed_adequacy` in `theories/logic/adequacy.v`
|  Case studies (state, generator to iterators, cooperative concurrency, ...) | `theories/case_studies/*`
## Differences between paper and Coq Formalisation

### Syntax and Semantics

As noted above, we do not define inductive datatypes for the syntax and semantics of Affect explicitly but instead encode our semantics on top of Hazel.
Hazel's language syntax and operational semantics can be found at `hazel/theories/language/syntax.v` and `hazel/theories/language/semantics.v` and the encoding of Affect is found at `theories/lang/affect.v` and `theories/lang/handler.v`.

### Purely Semantic Typing

Instead of defining syntactic expressions for types, signatures, effect rows and typing judgements (as done in sections §3 and §4 in the paper) we instead view them directly as semantic objects in our logic.
Thus in the formalisation there are no inductive data types that correspond to types, signatures, rows but instead are defined directly as a logical object.
Similarly there is no inductive data type for the typing rules but in contrast each typing rule is a lemma that we need to prove. 
This approach is explained in Section 5.1 of the paper.

### Notation Differences

| Paper          |  Coq Formalisation
| -------------- | ---------------------
| `replace`      | `<!-`
| `!ₘ`           | `![m]`
| `¡ₘ`           | `¡[m]`
| `Ref`          | `Refᶜ`
| `τ -ρ->ₘ κ`    | `τ -{ ρ }-[m]-> κ`
| `τ <: κ`       | `τ ≤ₜ κ`
| `σ <: σ'`      | `σ ≤ₛ σ'`
| `ρ <: ρ'`      | `ρ ≤ᵣ ρ'`
| `∀ α, τ`       | `∀ₜ α, τ`
| `∀ θ, τ`       | `∀ᵣ θ, τ`
| `∀ ν, α`       | `∀ₘ ν, τ`
| `∀ α⃑, τ =>ₘ κ` | `∀ₛ αs, τ =[ m ]=> κ`
| `μ θ, ρ`       | `μᵣ θ, ρ`


## Detailed paper to Coq formalisation correspondence

### 2. Overview

| Lemmas and expressions from paper                  | Coq Formalisation 
| -------------------------------------------------- | ------------------------------------------------------
| Theorem 2.1                                        | `sem_typed_adequacy` in `theories/logic/adequacy.v`
| `Iter`, `Gen`, `iter2gen`                          | `theories/case_studies/generator_iterator.v`
| `async`, `await`, `Coop`, `Promise`, `handle_coop` | `theories/case_studies/cooperative_concurrency_gen.v`
| `g` from 2.5                                       | `hid_typed` in `theories/case_studies/hid.v`

### 3. One-Shot & 4. Multi-Shot Affect Language

In the Coq formalisation we do not distinguish between the one-shot language and the full one with multi-shot effects.
Instead we only support the full language as the one-shot language is a subset of it.

| Lemmas and expressions from paper                  | Coq Formalisation 
| -------------------------------------------------- | ------------------------------------------------------------
| Figure 1 syntax and semantics                      | `hazel/theories/language/syntax.v`, `hazel/theories/language/semantics.v`, `theories/lang/handlers.v` and `theories/lang/affect.v`
| Contraction                                        | `sem_typed_contraction` in `theories/logic/compatibility.v`
| Weakening                                          | `sem_typed_weaken` in `theories/logic/compatibility.v`
| `Multi`                                            | `MultiT` in `theories/logic/sem_types.v`
| `Once`                                             | `OnceR` in `theories/logic/sem_row.v`
| Figure 2, Figure 4 subtyping rules                 | `ty_le_*` lemmas in `theories/logic/sem_types.v`
| Figure 3, Figure 5 typing rules                    | `sem_typed_*` lemmas in `theories/logic/compatibility.v`
| `let (k : 1 -o 1) = ...` from Section 4.3          | `mk_one_shot_typed_dp` in `theories/case_studies/promotion.v`
| `ModeSub-O`                                        | `mode_type_sub_os` in `theories/logic/mode.v`
| `ModeSub-M`                                        | `mode_type_sub_multi_ty` in `theories/logic/sem_types.v`
| `ModeSub-Nil`                                      | `mode_env_sub_nil` in `theories/logic/sem_env.v`
| `ModeSub-Cons`                                     | `mode_env_sub_cons` in `theories/logic/sem_env.v`
| `RowSub-Once`                                      | `row_type_sub_once` in `theories/logic/sem_row.v`
| `RowSub-Multi`                                     | `row_type_sub_multi_ty` in `theories/logic/sem_types.v`
| `RowSub-Nil`                                       | `row_env_sub_nil` in `theories/logic/sem_env.v`
| `RowSub-Cons`                                      | `row_env_sub_cons` in `theories/logic/sem_env.v`
| `ModeSub-MBang`                                    | `mode_type_sub_mbang` in `theories/logic/sem_types.v`
| `RowSub-FMBang`                                    | `row_type_sub_mfbang_mbang` in `theories/logic/sem_types.v`

### 5. Semantic Typing

| Lemmas and expressions from paper                  | Coq Formalisation 
| -------------------------------------------------- | ------------------------------------------------------------
| Figure 6 proof rules                               | `ewpw_*` lemmas in `theories/logic/ewpw.v`
| `mono_in`                                          | `mono_prot_on_prop` definition in `theories/logic/sem_row.v`
| `ewp_handle`                                       | `ewpw_handler` in `theories/logic/ewpw.v`
| Semantic Judgments in Figure 7                     | `sem_typed` and `sem_oval_typed` in `theories/logic/sem_judgement.v`
| Semantic types in Figure 7                         | `theories/logic/sem_types.v`
| Semantic signatures in Figure 7                    | `theories/logic/sem_sig.v`
| Semantic rows in Figure 7                          | `theories/logic/sem_row.v`
| Semantic relations in Figure 7                     | `theories/logic/sem_def.v`, `theories/logic/mode.v` and `theories/logic/sem_row.v`

# Detailed Project Structure

There are two source directories, 
`src` that has examples of using effect handlers in OCaml 5 (make sure `multicont` is installed to run these: `opam install . --deps-only`) 
and `theories` which gives the affine type and effect system.

| File                              | Description
| --------------------------------- | -------------------------------------------------------------------------------------
| src/BackTrackEff.ml               |  Backtracking example with effect handlers
| src/Concurrent.ml                 |  Two process in-sync example with effect handlers
| src/Decide.ml                     |  Introductory example from paper with unsound optimisation
| src/GeneratorEff.ml               |  Generators to Iterators in OCaml
| src/Promises.ml                   |  Cooperative Concurrency with effect handlers in OCaml
| src/State.ml                      |  State effect in OCaml
| theories/case_studies/*.v         |  Various typings of examples
| theories/lang/handler.v           |  Affect handler encodings to Hazel
| theories/lang/affect.v            |  Affect language encoding
| theories/lang/iEff.v              |  iEff protocol lemmas
| theories/lang/subst_map.v         |  Parallel substitution definition and properties
| theories/lib/*.v                  |  Helper lemmas and definition of pure weakest precondition
| theories/logic/adequacy.v         |  Proves adequacy of semantic judgment
| theories/logic/compatibility.v    |  Semantic typing rules
| theories/logic/ewpw.v             |  Weakest precondition of Affect
| theories/logic/mode.v             |  Lemmas related to modes
| theories/logic/sem_def.v          |  Main semantic definition of types, signatures, rows, environments and relations
| theories/logic/sem_env.v          |  Lemmas and definitions related to environments
| theories/logic/sem_judgement.v    |  Definition of semantic judgment
| theories/logic/sem_operators.v    |  Unary and binary operators
| theories/logic/sem_row.v          |  Lemmas and definitions related to rows
| theories/logic/sem_sig.v          |  Lemmas and definitions related to signatures
| theories/logic/sem_types.v        |  Lemmas and definitions related to types
| theories/logic/tactics.v          |  Tactics
