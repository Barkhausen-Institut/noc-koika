Load MetaCoqPrelude.

Module monad.

Import MCMonadNotation.
From MetaCoq Require Import bytestring.
Import String.
Open Scope bs.

MetaCoq Run (tmDefinition "foo" 24). (*Definition foo := 24.*)

Print foo.

MetaCoq Test Quote (fun x : nat => x).

MetaCoq Test Unquote ((tLambda {| binder_name := nNamed "x"; binder_relevance := Relevant |}
(tInd
   {|
     inductive_mind := (MPfile ["Datatypes"; "Init"; "Coq"], "nat");
     inductive_ind := 0
   |} []) (tRel 0))
).

MetaCoq Quote Definition quotebar := 24.  (*Quote gets the internal representation*)
Print quotebar.

MetaCoq Unquote Definition foo2 := quotebar. (*Unquote converts the internal representation to regular representation*)
Compute foo2.


Inductive reg_t:=
| r0
| r1
.

MetaCoq Quote Definition quotedreg := reg_t.
Print quotedreg.

Definition quotedr := (tConstruct
{|
  inductive_mind := (MPdot (MPfile ["metaprac2"]) "monad", "reg_t");
  inductive_ind := 0
|} 1 []).

Print quotedr.

MetaCoq Unquote Definition r3 := quotedr.

Print r3.