(* Load MetaCoqPrelude. *)
Require Import MetaCoq.Template.All.

Module monad.

Import MCMonadNotation.
Import List.
From MetaCoq Require Import bytestring.
Import String.
Open Scope bs.

Check tmDefinition.
Check tmMkDefinition.
Check tmMkInductive'.

MetaCoq Run (tmDefinition "foo" 24). (*Definition foo := 24.*)

MetaCoq Run (tmDefinition "foo2" <% 1 %>).
Check tmMkInductive'.

MetaCoq Quote Recursively Definition quotednat := nat.
Print quotednat.

Definition nat_inductive :=
  {|
  ind_finite := Finite;
  ind_npars := 0;
  ind_params := [];
  ind_bodies :=
    [{|
       ind_name := "nat2";
       ind_indices := [];
       ind_sort := sType (Universe.make' Level.lzero);
       ind_type := tSort (sType (Universe.make' Level.lzero));
       ind_kelim := IntoAny;
       ind_ctors :=
         [{|
            cstr_name := "O";
            cstr_args := [];
            cstr_indices := [];
            cstr_type := tRel 0;
            cstr_arity := 0
          |};
          {|
            cstr_name := "S";
            cstr_args :=
              [{|
                 decl_name :=
                   {|
                     binder_name := nAnon;
                     binder_relevance := Relevant
                   |};
                 decl_body := None;
                 decl_type := tRel 0
               |}];
            cstr_indices := [];
            cstr_type :=
              tProd
                {|
                  binder_name := nAnon; binder_relevance := Relevant
                |} (tRel 0) (tRel 1);
            cstr_arity := 1
          |}];
       ind_projs := [];
       ind_relevance := Relevant
     |}];
  ind_universes := Monomorphic_ctx;
  ind_variance := None
|}.

MetaCoq Run (tmMkInductive' nat_inductive).
Print nat2.

Fixpoint plus2 (n : nat2) (m : nat2) : nat2 :=
  match n with
  | O => m
  | S n' => S (plus2 n' m)
  end.


Definition P : Prop := forall n : nat2, plus2 O n = n.
MetaCoq Quote Recursively Definition nat_quoted := nat2.
Compute fst nat_quoted.

MetaCoq Quote Recursively Definition P_quoted := P.
Print P_quoted.
Check P_quoted.
Compute snd P_quoted.
Compute fst P_quoted.
Check empty_global_env.
Check add_global_decl.
Definition ind_decls := InductiveDecl nat_inductive.
Locate "×".
(* Definition ind_global_env:=add_global_decl empty_global_env (prod ind_decls nat2).  *)
Check Monomorphic_ctx.
Locate "::".
Locate "*".

Definition kername_of_string (s : string) : kername :=
  (MPfile [], s).

Definition global_declaraton_nat := (kername_of_string "some", ind_decls). 
Definition Sigma_env: global_env  := add_global_decl (fst P_quoted) global_declaraton_nat.
Definition universes := Monomorphic_ctx.
Print prod.
Locate "*".

Definition Sigma : global_env_ext := (Sigma_env, universes).
Locate "*".
Print prod.
Check InductiveDecl.
Check Sigma_env.

Check tApp.
Check exist.
(* Definition XYZ : forall n, exists t, Sigma ;;; [ ] |- t : tApp <% P %> (snd nat_quoted::nil). *)
Lemma XYZ : 
  {t | Sigma ;;; [ ] |- t : tApp <% P %> (snd nat_quoted::nil) }.
  
  Lemma XYZ : 
  {t | (isType Sigma [ ] t) (tApp <% P %> (snd nat_quoted::nil)) }.
  




Definition nat_term := <% nat %>.
Print nat_term.
MetaCoq Run (tmMkInductive' <% nat %>).
Check nat.

Compute <% 1 %>.
Print foo2.

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

MetaCoq Quote Definition quotedreg := r1.
Print quotedreg.
MetaCoq Quote Recursively Definition quote_rec_reg := reg_t.
Print quote_rec_reg.

Definition quotedr := (tConstruct
{|
  inductive_mind := (MPdot (MPfile ["metaprac2"]) "monad", "reg_t");
  inductive_ind := 0
|} 1 []).

MetaCoq Unquote Definition r3 := quotedr.

Print r3.

Check tApp.

Definition mydef x:= (
            match x with
              | 0 => 0
              | S n => n
            end).

MetaCoq Quote Definition mydef := mydefqu.
Print quotedx.