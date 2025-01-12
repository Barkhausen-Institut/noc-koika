Require Import MetaCoq.Template.All.
From MetaCoq.Common Require Import config.
From MetaCoq.Utils Require Import utils.
From Equations Require Import Equations.
Require Import MetaCoq.Quotation.ToTemplate.Init.

(* From MetaCoq.PCUIC Require Import PCUICTyping. *)
Module Test.

Import MCMonadNotation.
Import List.
From MetaCoq Require Import bytestring.
Import String.
Open Scope bs.

(*nat2 AST*)
Definition nat_inductive  :=
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

(* Class Add (T:Type) := { *)
(*   zero: T; *)
(*   plus: T -> T -> T *)
(* }. *)

(* Instance AddNat : Add nat := {
  zero := 0;
  plus := Nat.add
}. *)
(* Lemma P1 (T:Type) (H: Add T) (n:T) : plus zero n = n. *)

(* Axiom reify : mutual_inductive_body -> { T & Add T }. *)
(* Definition P3 {T:Type} `{Add T} (T:Type) :=forall n: plus zero n = n . *)

(* Lemma XYZ : forall (n:nat), *)
(*   let my_nat := reify (nat_inductive n) *)
(*   in P3 my_nat. *)

MetaCoq Run (tmMkInductive' nat_inductive).

Fixpoint plus2 (n : nat2) (m : nat2) : nat2 :=
  match n with
  | O => m
  | S n' => S (plus2 n' m)
  end.


Definition P : Prop := forall n : nat2, plus2 O n = n.
Check tProd.
MetaCoq Quote Recursively Definition P_quoted := P.

Lemma something :  (forall n : nat2, plus2 O n = n) = P.
Proof.
  unfold P.
  exact eq_refl.
Qed.

Print something.

MetaCoq Quote Recursively Definition sth_q := something.
Print sth_q.

Lemma P_act: P.
Proof.
unfold P.
reflexivity.
Qed.

Print P_act.

MetaCoq Quote Recursively Definition t_quoted := P_act.
Print t_quoted.

MetaCoq Quote Recursively Definition nat_quoted := nat2.
Definition ind_decls := InductiveDecl nat_inductive.

Definition kername_of_string (s : string) : kername :=
  (MPfile [], s).

Definition global_declaraton_nat := (kername_of_string "some", ind_decls).
Definition Sigma_env: global_env  := add_global_decl (fst sth_q) global_declaraton_nat.
Definition universes := Monomorphic_ctx.

Definition Sigma : global_env_ext := (Sigma_env, universes).
Search typing.
Local Existing Instance default_checker_flags.

Locate ">>=".

Check tmUnquote.
Compute tmUnquote P_quoted.2.
MetaCoq Run (tmMkDefinition "sts"%bs P_quoted.2).
Print sts.
Compute P_quoted.2.
Compute tmMkInductive' nat_inductive.

Definition P_copy :=
  (tProd
  {|
    binder_name := nNamed "n"; binder_relevance := Relevant
  |}
  (tInd
     {|
       inductive_mind :=
         (MPdot (MPfile ["meta_zulip"]) "Test", "nat2");
       inductive_ind := 0
     |} [])
  (tApp
     (tInd
        {|
          inductive_mind :=
            (MPfile ["Logic"; "Init"; "Coq"], "eq");
          inductive_ind := 0
        |} [])
     [tInd
        {|
          inductive_mind :=
            (MPdot (MPfile ["meta_zulip"]) "Test", "nat2");
          inductive_ind := 0
        |} [];
      tApp
        (tConst
           (MPdot (MPfile ["meta_zulip"]) "Test", "plus2") [])
        [tConstruct
           {|
             inductive_mind :=
               (MPdot (MPfile ["meta_zulip"]) "Test", "nat2");
             inductive_ind := 0
           |} 0 []; tRel 0]; tRel 0])).

Check P_copy.

MetaCoq Unquote Definition P_copyun := P_copy.
Print P_copyun.
MetaCoq Run (tmMkDefinition "P2" P_quoted.2).
Print P2.
Print P_quoted.
Print nat.
Print plus.
Print Init.Nat.add.

Check tApp.

(* Definition Sigma2_env:= empty_global_env.
Definition Sigma2 : global_env_ext := (Sigma2_env, universes). *)


(* Class Add (T:Type) := { *)
(*   zero: T; *)
(*   plus: T -> T -> T *)
(* }. *)

(* Lemma P1 (T:Type) (H: Add T) (n:T) : plus zero n = n. *)


(* Definition P3 {T:Type} `{Add T} (n:T) : plus zero n = n. *)
(* Admitted. *)

(* Axiom reify ast: mutual_inductive_body. *)
(* Lemma XYZ : forall (n:nat), *)
(*   let my_nat := reify (nat_inductive n) *)
(*   in P my_nat. *)
(* Axiom reify *)

Definition Sigma' : global_env_ext := (P_quoted.1, universes).


Lemma XYZ :
  {t & Sigma' ;;; [ ] |- t : P_quoted.2 }.
Proof.
  simpl.
  eexists.

  (** * Start unfolding
    load the constant [P] from [Sigma']
   *)
  eapply type_Conv.
  3:{
    eapply cumul_red_r.
    2:{
      eapply red_delta.
      - eapply declared_constant_from_gen.
        eapply lookup_constant_declared_gen.
        reflexivity.
      - reflexivity.
    }
    eapply cumul_refl.
    eapply TermEquality.leq_term_refl.
  }
  (** * Done unfolding
    I leave the second goal open because the
    sort is defined when clearing the goal
    that computes the proof term.
   *)

  eapply type_Lambda.

  (* Now I have to provide evidence that [nat2] is
     indeed properly typed/kinded/sorted.
   *)
  unfold lift_typing0.
  unfold lift_sorting.
  simpl.
  split.
  - exact tt.
  - eexists.
    split.
    + instantiate (1:= (sType (Universe.make' Level.lzero))).
      erewrite <- (closedu_subst_instance []).
      2:{ simpl. unfold closedu_universe. simpl.
          rewrite for_all_elements.
          simpl. trivial.}
      Fail eapply type_Ind.
      fold (ind_type (Build_one_inductive_body "nat2" [] (sType (Universe.make' Level.lzero)) (tSort (sType (Universe.make' Level.lzero))) IntoAny [] [] Relevant)).
      (* TODO Is the a way to do the previous step via existentials. *))
      eapply type_Ind.
