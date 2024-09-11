Require Import MetaCoq.Template.All.
Require Import Types.
Require Import Router. 
Require Import Koika.Frontend.
Require Import Koika.Std.
Require Import Koika.Testing.
Module Type NOC_data.
  Parameter nocsize: nat.
End NOC_data.

Module NOCSyntax (ND:NOC_data).
Import ND.
Require Import List.
Import MCMonadNotation.
From MetaCoq Require Import bytestring.
Open Scope bs.
(* Definition nocsize :=4. *)
Definition regno := (Nat.sub nocsize 1).
Definition regprefix := "r".
Definition ruleprefix := "router_".
Definition extfnprefix := "extfn_".

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

  Definition generate_ext_fn_args (n:nat):=
    tConstruct
               {|
                 inductive_mind :=
                   (MPdot (MPfile ["NOC_impl"]) "NOCImpl", "ext_fn_t");
                 inductive_ind := 0
               |} n [].
  
  Fixpoint generate_branches (n:nat): list (branch term) :=
    match n with
    | 0 => []
    | 1 => let branchterm := {|
          bcontext := [];
          bbody :=
            tApp
              (tConst
              (MPdot (MPdot (MPfile ["NOC_impl"]) "NOCImpl") "Routerfns", "routestartfn")[])
              [(nat_to_term 0);
              tConstruct
                {|
                  inductive_mind :=
                    (MPdot (MPfile ["NOC_impl"%bs])
                        "NOCImpl"%bs, "reg_t"%bs);
                  inductive_ind := 0
                |} 0 [];
                generate_ext_fn_args 0; generate_ext_fn_args 1]|} in
    [branchterm]
    | S n' => let branchterm := {|
    bcontext := [];
    bbody :=
      tApp
        (tConst
        (MPdot (MPdot (MPfile ["NOC_impl"]) "NOCImpl") "Routerfns", "routecenterfn") [])
        [ (nat_to_term n');
         tConstruct
           {|
             inductive_mind :=
               (MPdot (MPfile ["NOC_impl"%bs])
                  "NOCImpl"%bs, "reg_t"%bs);
             inductive_ind := 0
           |} (Nat.sub n' 1) [];
         tConstruct
           {|
             inductive_mind :=
               (MPdot (MPfile ["NOC_impl"%bs])
                  "NOCImpl"%bs, "reg_t"%bs);
             inductive_ind := 0
           |} n' [];
           generate_ext_fn_args (Nat.mul 2 n'); generate_ext_fn_args (Nat.add (Nat.mul 2 n') 1)]
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
        (MPdot (MPdot (MPfile ["NOC_impl"]) "NOCImpl") "Routerfns", "routeendfn") [])
        [(nat_to_term (Nat.sub nocsize 1));
        tConstruct
          {|
            inductive_mind :=
              (MPdot (MPfile ["NOC_impl"%bs])
                  "NOCImpl"%bs, "reg_t"%bs);
            inductive_ind := 0
          |} (Nat.sub nocsize 2) [];
          generate_ext_fn_args (Nat.sub (Nat.mul 2 nocsize) 2); generate_ext_fn_args (Nat.sub (Nat.mul 2 nocsize) 1)]
  |} in
    l ++ [last_term]
    end.

Definition branch_body := Eval compute in add_last_router(rev(generate_branches regno)).

Definition match_syn := (tLambda {| binder_name := nNamed "rl"%bs; binder_relevance := Relevant |}
(tInd
 {|
     inductive_mind :=
       (MPdot (MPfile ["NOC_impl"%bs]) "NOCImpl"%bs,
        "rule_name_t"%bs);
     inductive_ind := 0
   |} [])
(tCase
   {|
     ci_ind :=
       {|
         inductive_mind :=
           (MPdot (MPfile ["NOC_impl"%bs]) "NOCImpl"%bs,
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
              inductive_mind := (MPfile ["Syntax"; "Koika"], "uaction");
              inductive_ind := 0
            |} [])
         [tConst (MPfile ["Frontend"; "Koika"], "pos_t") [];
          tConst (MPfile ["Frontend"; "Koika"], "var_t") [];
          tConst (MPfile ["Frontend"; "Koika"], "fn_name_t") [];
          tConst
            (MPdot (MPdot (MPfile ["NOC_impl"]) "NOCImpl") "MyRegs",
             "reg_t") [];
          tConst
            (MPdot (MPdot (MPfile ["NOC_impl"]) "NOCImpl") "MyRegs",
             "ext_fn_t") []]
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
        (MPdot (MPfile ["NOC_impl"%bs])
           "NOCImpl"%bs, "rule_name_t"%bs);
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
          (MPdot (MPfile ["NOC_impl"%bs])
             "NOCImpl"%bs, "rule_name_t"%bs);
        inductive_ind := 0
      |} [];
    tConstruct
      {|
        inductive_mind :=
          (MPdot (MPfile ["NOC_impl"%bs])
             "NOCImpl"%bs, "rule_name_t"%bs);
        inductive_ind := 0
      |} n' []; generate_scheduler n' ]
      in sterm
      end.

Definition scheduler_synatx := Eval compute in (generate_scheduler nocsize).


End NOCSyntax.



Module MyNOCSize <: NOC_data.
  Definition nocsize := 4.  
End MyNOCSize.

Module NOCImpl. 
Print  Registers.

Import MCMonadNotation.
Module NOC_syn := NOCSyntax(MyNOCSize).
Import NOC_syn.
Import MyNOCSize.
Import Types.

Definition interfacesize := Nat.mul nocsize 2.

MetaCoq Run (
  tmMkInductive' (quoteind "reg_t" regprefix regno) ;;
  tmMkInductive' (quoteind "rule_name_t" ruleprefix nocsize);;
  tmMkInductive' (quoteind "ext_fn_t" extfnprefix interfacesize)
).

Print reg_t.
Print rule_name_t.
Print ext_fn_t.

Module MyRegs <: Registers.
Definition reg_t:=reg_t.
Definition ext_fn_t:= ext_fn_t.
End MyRegs.

Definition Sigma (fn: ext_fn_t) : ExternalSignature :=
  match fn with
  | _ => {$ bits_t sz ~> bits_t sz $}
  end.

Module Routerfns:= Router(MyRegs).
Import Routerfns.
Definition R ( reg : reg_t ) :=
  match reg with
  |  _ => bits_t (struct_sz basic_flit)
  end.
  
Definition r (reg : reg_t) : R reg :=
  match reg with
  |  _ => Bits.zero
  end.

 (* Definition to_action (rl: rule_name_t) := 
  match rl with
  | router_1 => routestartfn 0 r1 extfn_1 extfn_2
  | router_2 => routecenterfn 1 r1 r2 extfn_3 extfn_4
  | router_3 => routecenterfn 2 r2 r3 extfn_5 extfn_6
  | router_4 => routeendfn 3 r3 extfn_7 extfn_8
  end.

Check to_action.

MetaCoq Quote Definition testl:= Eval unfold to_action in to_action.
Print testl.  *)

MetaCoq Run ( tmMkDefinition "to_action"%bs match_syn).  

Print to_action.

MetaCoq Run ( tmMkDefinition "schedule"%bs scheduler_synatx). 

Print _routestart_r.
Definition external (r: rule_name_t) := false.


Definition rules :=
  tc_rules R Sigma to_action.

  Definition package :=
    {|
    ip_koika :=
    {|
    koika_reg_types := R;
    koika_reg_init := r;
    koika_ext_fn_types := Sigma;
    koika_rules := rules;
    koika_rule_external := external;
    koika_scheduler := schedule;
    koika_module_name := "NoC"
    |};
    
    ip_sim := {| sp_ext_fn_specs fn :=
    {| efs_name := show fn;
       efs_method := false |};
  sp_prelude := None |};
  ip_verilog := {| vp_ext_fn_specs fn :=
  {| efr_name := show fn;
     efr_internal := false
        |} |}
    |}.
(* Definition r_send_r1 := r_send r1. 

Definition tc_r_send := tc_function R Sigma r_send_r1.
Definition tc_r_receive := tc_function R Sigma r_receive. *)

Definition prog := Interop.Backends.register package.
Extraction "noc.ml" prog.

End NOCImpl.



Module Proofs.
Import NOCImpl.

(*8809 -> 10001001101001*)

Definition r2test (reg : reg_t) : R reg :=
  match reg with
  |  r1 => Bits.of_nat 14 8257 
  |  r2 => Bits.zero
  |  r3 => Bits.zero
  end.


(* Lemma router2:
    run_action r2test(rules router_2)
    (fun ctxt =>
      let bits_r2 := ctxt.[r2] in
      Bits.to_nat bits_r2 = 8769
    ).
  Proof.
    check.
  Defined.

  Definition r2testback (reg : reg_t) : R reg :=
    match reg with
    |  r1 => Bits.zero
    |  r2 => Bits.of_nat 14 9217 
    |  r3 => Bits.zero
    end.
  
  
  Lemma router2back:
      run_action r2testback(rules router_2)
      (fun ctxt =>
        let bits_r1 := ctxt.[r1] in
        Bits.to_nat bits_r1 = 8705
      ).
    Proof.
      check.
    Defined. *)

Definition r_r2l (reg : reg_t) : R reg :=
  match reg with
  |  r1 => Bits.zero 
  |  r2 => Bits.zero
  |  r3 => Bits.of_nat 14 9729
  end.

Goal
run_schedule r_r2l rules Sigma schedule
(fun ctxt =>
let r' := (fun idx => 
match idx with
  | r1=> ctxt.[r1]
  | r2=> ctxt.[r2]
  | r3=> ctxt.[r3]
  end ) in

run_schedule r' rules Sigma schedule
(fun ctxt2 =>
let bits_r0 := ctxt2.[r1] in
Bits.to_nat bits_r0 = 8705)).
  Proof.
    check.
  Defined.


(*8289 = 1 0000 0011 00001*)
Definition r_l2r (reg : reg_t) : R reg :=
  match reg with
  |  r1 => Bits.of_nat 14 8289 
  |  r2 => Bits.zero
  |  r3 => Bits.zero
  end.

Goal
run_schedule r_l2r rules Sigma schedule
(fun ctxt =>
let r' := (fun idx => 
match idx with
  | r1=> ctxt.[r1]
  | r2=> ctxt.[r2]
  | r3=> ctxt.[r3]
  end ) in

run_schedule r' rules Sigma schedule
(fun ctxt2 =>
let bits_r0 := ctxt2.[r3]in
Bits.to_nat bits_r0 = 9313)).
  Proof.
    check.
  Defined.

End Proofs.