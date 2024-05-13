

export OPAMYES=true

# create new opam switch
opam switch create haffel ocaml-base-compiler.5.0.0

# fetch coq-hazel library
git clone https://gitlab.inria.fr/cambium/hazel
cd hazel

# switch to commit that patch applies to
git checkout a0f7f67df7423fc84f39198ff46abacd84261e78
# apply patch
git apply ../hazel.patch
# commit patch
git add .; git commit -m "hazel patch for haffel applied" 

# install coq-hazel
opam install . 
cd ..

# compile haffel 
make
