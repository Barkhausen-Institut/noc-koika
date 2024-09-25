Require Import MetaCoq.Template.All.
From MetaCoq.Common Require Import config.
Module Test.

Import MCMonadNotation.
Import List.
From MetaCoq Require Import bytestring.
Import String.
Open Scope bs.

(*nat2 AST*)
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

Fixpoint plus2 (n : nat2) (m : nat2) : nat2 :=
  match n with
  | O => m
  | S n' => S (plus2 n' m)
  end.


Definition P : Prop := forall n : nat2, plus2 O n = n.
MetaCoq Quote Recursively Definition P_quoted := P.

MetaCoq Quote Recursively Definition nat_quoted := nat2.
Definition ind_decls := InductiveDecl nat_inductive.

Definition kername_of_string (s : string) : kername :=
  (MPfile [], s).

Definition global_declaraton_nat := (kername_of_string "some", ind_decls). 
Definition Sigma_env: global_env  := add_global_decl (fst P_quoted) global_declaraton_nat.
Definition universes := Monomorphic_ctx.

Definition Sigma : global_env_ext := (Sigma_env, universes).

Local Existing Instance default_checker_flags.


Check tmUnquote.

Lemma XYZ : 
  {t & Sigma ;;; [ ] |- t : tApp P_quoted.2 (snd nat_quoted::nil) }.
  Proof.
  unfold P_quoted. 



Lemma XYZ : 
  {t & Sigma ;;; [ ] |- t : tApp <% P %> (snd nat_quoted::nil) }.
  Proof.
  Unset Printing Notations.