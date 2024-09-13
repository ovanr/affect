# Affect

This project formalises an affine type and effect system for a language with effect handlers
and proves type safety for it.

# Overview 

There are two source directories, `src` that has examples of using effect handlers
in OCaml 5 and `theories` which gives the affine type and effect system.

The project depends on `coq-hazel` a language with effects and effect handlers,
together with its embedding in `iris` that allows us to reason about programs written in Hazel.

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

# Installation

Run `install.sh`

# Notes

We avoid defining syntactic expressions for types, signatures, effect rows and typing judgements but instead view them directly as semantic objects in our logic.
Thus in the formalisation, types and friends are not defined using inductive data types but as notations to the logical object.

We build and rely on the Hazel program logic that is dependent on the Hazel language that supports effect handlers.
As a result, the semantics of Affect are encoded on the Hazel language which follows similar semantics.
