# MetaCoq

## Introduction

Meta-programming is the art of writing programs (in a meta-language) that produce or manipulate programs (written in an object language).

tInd is crucial in MetaCoq when you need to refer to an inductive type within the Coq term representation. It allows you to specify that a constructor, function, or another term is of an inductive type, linking the term to the specific type being referred to in the Coq environment. 

Template-Coq allows us to move back and forth between concrete and reified syntax. 
Quote(Concrete Syntax) -> Reified Syntax

Test Quote - Prints the reified syntax 
Quote Definition - Records the reification of term 
Make Definition - To construct a term from its syntax.

MetaCoq Run <=> Run TemplateProgram