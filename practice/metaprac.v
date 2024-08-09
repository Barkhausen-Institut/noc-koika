(* Import necessary modules *)

Load MetaCoqPrelude.

Module monad.

Import MCMonadNotation.
From MetaCoq Require Import bytestring.
Import String.
Open Scope bs.

Print TemplateMonad.

MetaCoq Run (tmBind (tmQuote (3 + 3)) tmPrint).

MetaCoq Run (tmBind (tmQuoteRec add) tmPrint).

MetaCoq Run (tmBind (tmLocate "add") tmPrint).

Definition printInductive (q : qualid): TemplateMonad unit :=
  kn <- tmLocate1 q ;;
  match kn with
  | IndRef ind => (tmQuoteInductive ind.(inductive_mind)) >>= tmPrint
  | _ => tmFail ("[" ++ q ++ "] is not an inductive")
  end.

      Check tmMkInductive.
  Check term. 
Require Import MetaCoq.Template.All.
Require Import List.
Open Scope string_scope.



Print tmMkInductive.

Search tmMkInductive.

Load MetaCoqPrelude. 

About tmDefinition.


Check tInd.


Definition colordefinition :=  {|
ind_finite := Finite;
ind_npars := 0;
ind_params := [];
ind_bodies :=
[{|
     ind_name := "color";
     ind_indices := [];
     ind_sort := sType (Universe.make' Level.lzero);
     ind_type := tSort (sType (Universe.make' Level.lzero));
     ind_kelim := IntoAny;
     ind_ctors :=
       [{|
          cstr_name := "regt1";
          cstr_args := [];
          cstr_indices := [];
          cstr_type := tRel 0;
          cstr_arity := 0
        |};
        {|
          cstr_name := "regt2";
          cstr_args := [];
          cstr_indices := [];
          cstr_type := tRel 0;
          cstr_arity := 0
        |}];
     ind_projs := [];
     ind_relevance := Relevant
   |}];
ind_universes := Monomorphic_ctx;
ind_variance := None
|}.


MetaCoq Run (
  tmMkInductive' colordefinition
).

Print color.

Check ind_ctors.

From MetaCoq Require Import bytestring.
Open Scope bs.
 
Fixpoint generate_constructors (n : nat) : list constructor_body :=
  match n with
  | 0 => []
  | S n' =>
    let name := "reg" ++ string_of_nat (S n') in
    let cstr := {| cstr_name := name;
                   cstr_args := [];
                   cstr_indices := [];
                   cstr_type := tRel 0;
                   cstr_arity := 0 |} in
    cstr :: generate_constructors n'
  end.

Compute generate_constructors 3.


Definition paracolordefinition :=  {|
ind_finite := Finite;
ind_npars := 0;
ind_params := [];
ind_bodies :=
[{|
     ind_name := "paracolor";
     ind_indices := [];
     ind_sort := sType (Universe.make' Level.lzero);
     ind_type := tSort (sType (Universe.make' Level.lzero));
     ind_kelim := IntoAny;
     ind_ctors := generate_constructors 3;
     ind_projs := [];
     ind_relevance := Relevant
   |}];
ind_universes := Monomorphic_ctx;
ind_variance := None
|}.


MetaCoq Run (
  tmMkInductive' paracolordefinition
).

Print paracolor.