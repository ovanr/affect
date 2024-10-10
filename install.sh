#!/bin/bash

function echoerr () {
    echo -e $* 1>&2
}

echo -e "...Affect Installation...\n"

if ! command -v opam >/dev/null ; then
  echoerr "You are missing opam, the OCaml package manager."
  echoerr "Visit the following link for help installing it:"
  echoerr "  https://opam.ocaml.org/doc/Install.html"
  exit 1
fi

echo -e "> Updating local opam package database."
echo -e "> This can take a few minutes..."
opam update

if [ -d _opam ] ; then
  echoerr "There is already a local opam switch in the current directory."
  echoerr "If it is OK to remove it, please type:"
  echoerr "  opam switch remove ."
  echoerr "then run ./install.sh again."
  exit 1
fi

export OPAMYES=true

echo -e "\n> Creating a new local opam switch."
echo -e "> This will take a while (perhaps over 10 minutes)..."

if [[ `opam switch show 2> /dev/null` == 'affect' ]]; then
    echoerr -e "\n'affect' switch already installed. Please remove switch (opam switch remove affect) to reinstall"
    exit 1
fi

opam switch create affect \
  --no-install \
  --repositories=default,coq-released=https://coq.inria.fr/opam/released,iris-dev=git+https://gitlab.mpi-sws.org/iris/opam.git \
  ocaml-base-compiler.5.0.0

eval "$(opam env --switch=affect)"

echo -e "\n> Updating local opam package database..."
opam update

opam pin add -n coq 8.18.0

echo -e "\n> Fetching coq-hazel library\n"
if [[ -d hazel ]]; then
    echoerr "'hazel' directory already present. Please remove it before continuing"
    exit 1
fi

git clone https://gitlab.inria.fr/cambium/hazel
if (( $? != 0)); then
    echoerr "Unable to fetch coq-hazel from https://gitlab.inria.fr/cambium/hazel"
    echoerr "Using local copy instead."
    [[ -d hazel ]] && rm -r hazel
    tar xzf hazel-local-copy.tar.gz
fi
cd hazel

echo -e "\n> Applying Hazel patch for Affect\n"
git checkout a0f7f67df7423fc84f39198ff46abacd84261e78
git apply --whitespace=nowarn ../hazel.patch
git add .; git commit -m "Hazel patch for Affect"

echo -e "\n> Installing coq-hazel and local dependencies. This can take 5-10 minutes.\n"
opam install . 
cd ..
opam install . --deps-only

echo -e "\n> Compiling Affect... This can take up to 5 minutes\n"
make

(( $? != 0 )) && exit 1
echo -e "\n> Compiled Affect"
