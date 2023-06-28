# Affine TES

# Installation

## Hazel language

This project depends on `coq-hazel`, 
a language with effects and effect handlers,
together with its embedding in `iris` that allows 
us to reason about programs written in Hazel.


### Installing `coq-hazel`

Installing `coq-hazel` as a local package:

1. `git clone https://gitlab.inria.fr/cambium/hazel.git`
2. `cd hazel`
3. `opam install .`

## Building `affine-tes`

1. `make build-dep`
