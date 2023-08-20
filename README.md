# Affine TES

This project formalises an affine type and effect system for a language with effect handlers
and proves type safety for it.

# Installation

There are two source directories, `src` that has examples of using effect handlers
in OCaml 5 and `theories` which gives the affine type and effect system.
They depend on different OCaml versions and so they need to run in different environments.

To handle this we use opam switches.

## Running OCaml programs in `src`

To run the .ml files in `src` OCaml 5 is needed.

### Installation via the `src.switch`:

1. Install switch: 
    `opam switch --switch="affine-tes-src" import src.switch`

2. Enable switch: 
    `eval $(opam env --switch=affine-tes-src --set-switch)`

## Running the formalisation of Affine-Tes  

To run the .v files in `theories`, `coq`, `coq-iris` and `coq-hazel` is needed.
The project depends on `coq-hazel` a language with effects and effect handlers,
together with its embedding in `iris` that allows us to reason about programs written in Hazel.
Unfortunately, it is not available in the opam repositories and so it must be installed locally.

### Installation via the `theories.switch`:

1. Install switch: 
    `opam switch --switch="affine-tes-theories" import theories.switch`

2. Enable switch: 
    `eval $(opam env --switch=affine-tes-theories --set-switch)`

3. Installing `coq-hazel`: 
    1. `git clone https://gitlab.inria.fr/cambium/hazel.git`
    2. `cd hazel`
    3. `opam install .`

4. Compiling affine-tes theories: 
    `make`

