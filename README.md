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
| theories/case_studies/*.v         |  various typings of examples                                                       
| theories/logic/adequacy.v         |  proves adeaquacy of semantic judgment                                             
| theories/logic/compatibility.v    |  semantic typing rules                                                             
| theories/logic/ewpw.v             |  wrapper around extended weakest precondition of Hazel                             
| theories/logic/mode.v             |  lemmas related to modes                                                           
| theories/logic/sem_def.v          |  main semantic definition of types, signatures, rows, environments and relations   
| theories/logic/sem_env.v          |  lemmas and definitions related to environments                                    
| theories/logic/sem_judgement.v    |  definition of semantic judgment                                                   
| theories/logic/sem_operators.v    |  unary and binary operators                                                        
| theories/logic/sem_row.v          |  lemmas and definitions related to rows                                            
| theories/logic/sem_sig.v          |  lemmas and definitions related to signatures                                      
| theories/logic/sem_types.v        |  lemmas and definitions related to types                                           
| theories/logic/tactics.v          |  tactics                                                                           
| theories/lang/handler.v           |  Affect's hander encodings to Hazel                                                
| theories/lang/affect.v            |  Affect's encodings to Hazel                                                       

# Installation

Run `install.sh`

# Notes

We avoid defining syntactic expressions for types, signatures, effect rows and typing judgements but instead view them directly as semantic objects in our logic.
Thus in the formalisation, types and friends are not defined using inductive data types but defined as notations to the logical object.

We build and rely on the Hazel program logic that is dependent on the Hazel language that supports effect handlers.
As a result, the semantics of Affect are encoded on the Hazel language which follows similar semantics.

# Notation differences

Here are how notations in the paper are mapped to the formalisation: 

| Paper      | Formalisation
| ---------- | --------------
| Multi τ    | copy_ty τ
| Multi Γ    | copy_env Γ
| !ₘ τ       | '!_[m] τ 
| ¡ₘ σ       | ¡_[m] σ
| ¡ₘ ρ       | ¡_[m] ρ
| Γ ⊨ γ      | ⟦ Γ ⟧ γ
| τ <: τ'    | τ ≤T τ'
| σ <: σ'    | σ ≤S σ'
| ρ <: ρ'    | ρ ≤R ρ'
| Γ <: Γ'    | Γ ≤E Γ'
| m ≤ τ      | m ₘ≼ₜ τ 
| m ≤ Γ      | m ₘ≼ₑ E 
| ρ ≤ τ      | ρ ≼ₜ τ 
| ρ ≤ Γ      | ρ ≼ₑ Γ 
