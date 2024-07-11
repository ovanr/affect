
echo "...Affect Setup..."

export OPAMYES=true

#echo "∙ Creating new opam switch"
#opam switch create affect ocaml-base-compiler.5.0.0

echo "∙ Fetching coq-hazel library"
git clone https://gitlab.inria.fr/cambium/hazel
cd hazel

echo "∙ Switching to commit that patch applies to"
git checkout a0f7f67df7423fc84f39198ff46abacd84261e78

echo "∙ Appling patch"
git apply ../hazel.patch

echo "∙ Commiting patch"
git add .; git commit -m "Hazel patch for Affect applied" 

#echo "∙ Installing coq-hazel"
#opam install . 
#cd ..

#echo "∙ Installing local dependencies"
#opam install . --deps-only

#echo "∙ Compiling Affect"
#make
