#!/bin/bash

function echoerr () {
    echo -e $* 1>&2
}

function ask () {
    read
    if [[ ${REPLY^^} == "Y" ]]; then
        return 0
    else
        return 1
    fi
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

switch_install=0
if [[ `opam switch show 2> /dev/null` == 'affect' ]]; then
    echoerr -e "\n'affect' switch already installed."
    echo -n "Should I reinstall it? (Y|N) "
    if ask; then
        opam switch remove affect
        switch_install=1
    fi
else
    switch_install=1
fi

if (( switch_install == 1 )); then
    opam switch create affect \
      --no-install \
      --repositories=default,coq-released=https://coq.inria.fr/opam/released,iris-dev=git+https://gitlab.mpi-sws.org/iris/opam.git \
      ocaml-base-compiler.5.0.0
fi

eval "$(opam env --switch=affect)"

echo -e "\n> Updating local opam package database..."
opam update

opam pin add -n coq 8.20.0

echo -e "\n> Installing coq-hazel library\n"
hazel_install=0
if [[ -d hazel ]]; then
    echoerr "'hazel' directory already present."
    echo -n "Should I reinstall hazel? (Y|n) "
    if ask; then
        rm -rf hazel
        hazel_install=1
    fi
else
    hazel_install=1
fi


if (( hazel_install == 1 )); then
    git clone https://gitlab.inria.fr/cambium/hazel
    if (( $? != 0)); then
        echo "Unable to fetch coq-hazel from https://gitlab.inria.fr/cambium/hazel"
        exit 1
    fi
    cd hazel
    
    echo -e "\n> Applying Hazel patch for Affect\n"
    git checkout 73e3a84eecf655e366d8791e1c94b7bbe01db597
    git am --whitespace=nowarn ../hazel-patches/0001-Adds-a-Replace-e1-e2-construct.patch
    
    echo -e "\n> Installing coq-hazel and local dependencies. This can take 5-10 minutes.\n"
    opam install . 

    cd ..
fi

echo -e "\n> Compiling Affect... This can take up to 5 minutes\n"
opam install . --deps-only
make

(( $? != 0 )) && exit 1
echo -e "\n> Compiled Affect"
