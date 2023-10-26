# Haffel

This project formalises an affine type and effect system for a language with effect handlers
and proves type safety for it.

# Installation

There are two source directories, `src` that has examples of using effect handlers
in OCaml 5 and `theories` which gives the affine type and effect system.

To run the .v files in `theories`, `coq`, `coq-iris` and `coq-hazel` is needed.
The project depends on `coq-hazel` a language with effects and effect handlers,
together with its embedding in `iris` that allows us to reason about programs written in Hazel.
Unfortunately, it is not available in the opam repositories and so it must be installed locally.

### Installation via `switch.freeze`:

1. Install switch: 
    `opam switch --switch="haffel" import switch.freeze`

2. Enable switch: 
    `eval $(opam env --switch=haffel --set-switch)`

3. Installing `coq-hazel`: 
    1. `git submodule update --init --recursive`
    1. `cd hazel`
    3. `opam install .`

4. Compiling haffel theories: 
    `make`

