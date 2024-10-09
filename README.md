# Affect

This artifact provides the Coq formalisation of the paper "Affect: An Affine Type and Effect System".

# Building on local machine

Make sure that opam (tested using version 2.2.1) is installed on your system.
Create a new opam switch:
```bash
opam switch create affect \
  --no-install \
  --repositories=default,coq-released=https://coq.inria.fr/opam/released,iris-dev=git+https://gitlab.mpi-sws.org/iris/opam.git \
  ocaml-base-compiler.5.0.0
eval "$(opam env --switch=affect)"
```

`Affect` relies on `coq-hazel` a separation logic library for effect handlers. 
To install `coq-hazel` we need to manually fetch it and apply the patch `hazel.patch` (this can take 5-10 minutes):
```bash
git clone https://gitlab.inria.fr/cambium/hazel
cd hazel
git checkout a0f7f67df7423fc84f39198ff46abacd84261e78
git apply --whitespace=nowarn ../hazel.patch
git add .; git commit -m "Hazel patch for Affect"
opam install . 
```

Compile `Affect` (this can take up to 10 minutes).
By default all case studies are compiled. 
You can omit them from the compilation by commenting their corresponding line in `_CoqProject`.
```bash
cd ..; make -j 4.
```

## Using the VirtualBox image

# Supporting the claims of the paper



# File Structure

There are two source directories, `src` that has examples of using effect handlers
in OCaml 5 and `theories` which gives the affine type and effect system.

| File                              | Description
| --------------------------------- | -------------------------------------------------------------------------------------
| theories/case_studies/*.v         |  Various typings of examples
| theories/lang/handler.v           |  Affect's handler encodings to Hazel
| theories/lang/affect.v            |  Affect language encoding
| theories/logic/adequacy.v         |  Proves adequacy of semantic judgment
| theories/logic/compatibility.v    |  Semantic typing rules
| theories/logic/ewpw.v             |  Wrapper around extended weakest precondition of Hazel
| theories/logic/mode.v             |  Lemmas related to modes
| theories/logic/sem_def.v          |  Main semantic definition of types, signatures, rows, environments and relations
| theories/logic/sem_env.v          |  Lemmas and definitions related to environments
| theories/logic/sem_judgement.v    |  Definition of semantic judgment
| theories/logic/sem_operators.v    |  Unary and binary operators
| theories/logic/sem_row.v          |  Lemmas and definitions related to rows
| theories/logic/sem_sig.v          |  Lemmas and definitions related to signatures
| theories/logic/sem_types.v        |  Lemmas and definitions related to types
| theories/logic/tactics.v          |  Tactics

# Differences of paper with Coq Formalisation

# Notes

We avoid defining syntactic expressions for types, signatures, effect rows and typing judgements but instead view them directly as semantic objects in our logic.
Thus in the formalisation, types and friends are not defined using inductive data types but as notations to the logical object.

We build and rely on the Hazel program logic that is dependent on the Hazel language that supports effect handlers.
As a result, the semantics of Affect are encoded on the Hazel language which follows similar semantics.
