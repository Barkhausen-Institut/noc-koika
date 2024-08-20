Require Import MetaCoq.Template.All.


Module Type NOC_data.
  Parameter nocsize: nat.
End NOC_data.

Module NOCSyntax (ND:NOC_data).
Import ND.
Import MCMonadNotation.
Require Import List.
From MetaCoq Require Import bytestring.
Open Scope bs.
(* Definition nocsize :=4. *)
Definition regno := (Nat.sub nocsize 1).
Definition regprefix := "r".
Definition ruleprefix := "router_".

Fixpoint rev {A : Type} (l:list A) : list A :=
    match l with
      | nil => nil
      | x :: l' => rev l' ++ x :: nil
    end.

Fixpoint generate_constructors (prefix: string) (n : nat) : list constructor_body :=
  match n with
  | 0 => []
  | S n' =>
    let name := prefix ++ string_of_nat (S n') in
    let cstr := {| cstr_name := name;
                   cstr_args := [];
                   cstr_indices := [];
                   cstr_type := tRel 0;
                   cstr_arity := 0 |} in
    cstr :: generate_constructors prefix n'
  end.


Definition quoteind (ind_name : string) (prefix : string) (no_cstr :nat) :=  {|
ind_finite := Finite;
ind_npars := 0;
ind_params := [];
ind_bodies :=
[{|
     ind_name := ind_name;
     ind_indices := [];
     ind_sort := sType (Universe.make' Level.lzero);
     ind_type := tSort (sType (Universe.make' Level.lzero));
     ind_kelim := IntoAny;
     ind_ctors := rev (generate_constructors prefix no_cstr);
     ind_projs := [];
     ind_relevance := Relevant
   |}];
ind_universes := Monomorphic_ctx;
ind_variance := None
|}.

Fixpoint nat_to_term (n : nat) : term :=
  match n with
  | 0 => tConstruct
          {|
            inductive_mind :=
              (MPfile ["Datatypes"%bs; "Init"%bs; "Coq"%bs], "nat"%bs);
            inductive_ind := 0
          |} 0 []
  | S n' => tApp
        (tConstruct
          {|
            inductive_mind :=
              (MPfile ["Datatypes"%bs; "Init"%bs; "Coq"%bs], "nat"%bs);
            inductive_ind := 0
          |} 1 []) [nat_to_term n']
  end.

  Fixpoint generate_branches (n:nat): list (branch term) :=
    match n with
    | 0 => []
    | 1 => let branchterm := {|
          bcontext := [];
          bbody :=
            tApp
              (tConst
                (MPdot (MPfile ["Pipeline_NOC_parametric"%bs]) "Design"%bs,
                  "routestartfn"%bs) [])
              [(nat_to_term 0);
              tConstruct
                {|
                  inductive_mind :=
                    (MPdot (MPfile ["Pipeline_NOC_parametric"%bs])
                        "Registers"%bs, "reg_t"%bs);
                  inductive_ind := 0
                |} 0 []]|} in
    [branchterm]
    | S n' => let branchterm := {|
    bcontext := [];
    bbody :=
      tApp
        (tConst
           (MPdot (MPfile ["Pipeline_NOC_parametric"%bs]) "Design"%bs,
            "routecenterfn"%bs) [])
        [ (nat_to_term n');
         tConstruct
           {|
             inductive_mind :=
               (MPdot (MPfile ["Pipeline_NOC_parametric"%bs])
                  "Registers"%bs, "reg_t"%bs);
             inductive_ind := 0
           |} (Nat.sub n' 1) [];
         tConstruct
           {|
             inductive_mind :=
               (MPdot (MPfile ["Pipeline_NOC_parametric"%bs])
                  "Registers"%bs, "reg_t"%bs);
             inductive_ind := 0
           |} n' []]
  |} in
  branchterm :: generate_branches n'
    end.
  
  
  Definition add_last_router (l : list (branch term)) : list (branch term) :=
    match l with
    | [] => []
    | _ =>
    let last_term := {|
    bcontext := [];
    bbody :=
      tApp
        (tConst
          (MPdot (MPfile ["Pipeline_NOC_parametric"%bs]) "Design"%bs,
            "routeendfn"%bs) [])
        [(nat_to_term (Nat.sub nocsize 1));
        tConstruct
          {|
            inductive_mind :=
              (MPdot (MPfile ["Pipeline_NOC_parametric"%bs])
                  "Registers"%bs, "reg_t"%bs);
            inductive_ind := 0
          |} (Nat.sub nocsize 2) []]
  |} in
    l ++ [last_term]
    end.

Definition branch_body := Eval compute in add_last_router(rev(generate_branches regno)).

Definition match_syn := (tLambda {| binder_name := nNamed "rl"%bs; binder_relevance := Relevant |}
(tInd
 {|
     inductive_mind :=
       (MPdot (MPfile ["Pipeline_NOC_parametric"%bs]) "Registers"%bs,
        "rule_name_t"%bs);
     inductive_ind := 0
   |} [])
(tCase
   {|
     ci_ind :=
       {|
         inductive_mind :=
           (MPdot (MPfile ["Pipeline_NOC_parametric"%bs]) "Registers"%bs,
            "rule_name_t"%bs);
         inductive_ind := 0
       |};
     ci_npar := 0;
     ci_relevance := Relevant
   |}
   {|
     puinst := [];
     pparams := [];
     pcontext :=
       [{| binder_name := nNamed "rl"%bs; binder_relevance := Relevant |}];
     preturn :=
       tApp
         (tInd
            {|
              inductive_mind :=
                (MPfile ["Syntax"%bs; "Koika"%bs], "uaction"%bs);
              inductive_ind := 0
            |} [])
         [tConst (MPfile ["Frontend"%bs; "Koika"%bs], "pos_t"%bs) [];
          tConst (MPfile ["Frontend"%bs; "Koika"%bs], "var_t"%bs) [];
          tConst (MPfile ["Frontend"%bs; "Koika"%bs], "fn_name_t"%bs) [];
          tInd
            {|
              inductive_mind :=
                (MPdot (MPfile ["Pipeline_NOC_parametric"%bs])
                   "Registers"%bs, "reg_t"%bs);
              inductive_ind := 0
            |} [];
          tInd
            {|
              inductive_mind :=
                (MPfile ["Interop"%bs; "Koika"%bs], "empty_ext_fn_t"%bs);
              inductive_ind := 0
            |} []]
   |} (tRel 0)
     branch_body
     )).

Fixpoint generate_scheduler (n: nat) : term :=
  match n with
  | 0 => let sterm:= tApp
  (tConstruct
     {|
       inductive_mind :=
         (MPfile ["Syntax"%bs; "Koika"%bs], "scheduler"%bs);
       inductive_ind := 0
     |} 0 []) 
  [tConst (MPfile ["Frontend"%bs; "Koika"%bs], "pos_t"%bs) [];
  tInd
    {|
      inductive_mind :=
        (MPdot (MPfile ["Pipeline_NOC_parametric"%bs])
           "Registers"%bs, "rule_name_t"%bs);
      inductive_ind := 0
    |} []] in sterm
    | S n' => let sterm:= tApp (tConstruct
    {|
      inductive_mind :=
        (MPfile ["Syntax"%bs; "Koika"%bs], "scheduler"%bs);
      inductive_ind := 0
    |} 1 [])
    [tConst (MPfile ["Frontend"%bs; "Koika"%bs], "pos_t"%bs) [];
    tInd
      {|
        inductive_mind :=
          (MPdot (MPfile ["Pipeline_NOC_parametric"%bs])
             "Registers"%bs, "rule_name_t"%bs);
        inductive_ind := 0
      |} [];
    tConstruct
      {|
        inductive_mind :=
          (MPdot (MPfile ["Pipeline_NOC_parametric"%bs])
             "Registers"%bs, "rule_name_t"%bs);
        inductive_ind := 0
      |} n' []; generate_scheduler n' ]
      in sterm
      end.

Definition scheduler_synatx := Eval compute in (generate_scheduler nocsize).

End NOCSyntax.

