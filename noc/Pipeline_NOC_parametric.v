Require Import MetaCoq.Template.All.

Module Types.
Require Import Koika.Frontend.
Require Import Koika.Std.
Require Import Koika.Testing.

Definition basic_flit :=
    {|
    struct_name := "basic_flit";
    struct_fields :=
      [
        ("new", bits_t 1);
        ("src" , bits_t 4);
        ("trg_y" , bits_t 2);
        ("trg_x" , bits_t 2);
        ("data" , bits_t 5)
      ]
    |}.
  
Definition router_address :=
    {|
    struct_name := "router_address";
    struct_fields :=
      [
        ("y" , bits_t 2);
        ("x" , bits_t 2)
      ]
    |}.


End Types.

Module Registers.
Require Import List.
Import MCMonadNotation.

From MetaCoq Require Import bytestring.
Open Scope bs.
Notation regno := 3.
Notation nocsize := 4.
Notation regprefix := "r".
Notation ruleprefix := "router_".

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

MetaCoq Run (
  tmMkInductive' (quoteind "reg_t" regprefix regno) ;;
  tmMkInductive' (quoteind "rule_name_t" ruleprefix nocsize)
).



Print reg_t.
Print rule_name_t.
End Registers.

Module Design.

Import Types.
Import Registers.
Require Import Koika.Frontend.
Require Import Koika.Std.
Require Import Koika.Testing.

Notation sz := 14.


Print reg_t.
Definition r_send (reg_name: reg_t) : UInternalFunction reg_t empty_ext_fn_t :=
  {{ fun r_send (value: bits_t sz) : unit_t =>
    write0(reg_name, value)
  }}.

Definition r_receive (reg_name: reg_t) : UInternalFunction reg_t empty_ext_fn_t :=
  {{ fun r_receive () : bits_t sz =>
    read0(reg_name)
  }}.

Definition _routestart_r (r_addr2: nat) (r0_send r0_receive: UInternalFunction reg_t empty_ext_fn_t) 
: uaction reg_t empty_ext_fn_t :=
UBind "r_addr" (USugar (UConstBits (Bits.of_nat 4 r_addr2)))
{{
    let m0 := r0_receive() in (*router input policy will be added here*)
    let msg := unpack(struct_t basic_flit, m0) in
    let new_data := get(msg, new) in
    let src_p := get(msg, src) in
    (( if (src_p != r_addr && new_data) then 
        let trg_x := get(msg, trg_x) in
        let trg_y := get(msg, trg_y) in
        let src_x := get(unpack(struct_t router_address, r_addr), x) in
        let src_y := get(unpack(struct_t router_address, r_addr), y) in
        (*r_addr[|2`d0| :+ 2] if not using struct*)
        if trg_x > src_x then
        r0_send(pack(subst(msg, src, r_addr)))
        else if trg_x < src_x then
        fail
        else
        pass    (*Pass to tile from this block*)
    else
    pass ))
}}.
  
Definition _routecenter_r (r_addr2: nat) (r0_send r1_send r0_receive r1_receive: UInternalFunction reg_t empty_ext_fn_t) 
: uaction reg_t empty_ext_fn_t :=
  UBind "r_addr" (USugar (UConstBits (Bits.of_nat 4 r_addr2)))
  {{
  let m0 := r0_receive() in (*router input policy will be added here*)
  let m1 := r1_receive() in 
  let msg := unpack(struct_t basic_flit, m0) in
  let new_data := get(msg, new) in
  let src_p := get(msg, src) in
  (( if (src_p != r_addr && new_data) then
      r0_send(pack(subst(msg, new, Ob~0)));
      let trg_x := get(msg, trg_x) in
      let trg_y := get(msg, trg_y) in
      let src_x := get(unpack(struct_t router_address, r_addr), x) in
      let src_y := get(unpack(struct_t router_address, r_addr), y) in
      (*r_addr[|2`d0| :+ 2] if not using struct*)
      if trg_x > src_x then
      r1_send(pack(subst(msg, src, r_addr)))
      else if trg_x < src_x then
      r0_send(pack(subst(msg, src, r_addr)))
      else
      pass    (*Pass to tile from this block*)
  else
  pass ));
  let msg1 := unpack(struct_t basic_flit, m1) in
  let new_data := get(msg1, new) in
  let src_p := get(msg1, src) in
  (( if (src_p != r_addr && new_data) then
      r1_send(pack(subst(msg1, new, Ob~0)));
      let trg_x := get(msg1, trg_x) in
      let trg_y := get(msg1, trg_y) in
      let src_x := get(unpack(struct_t router_address, r_addr), x) in
      let src_y := get(unpack(struct_t router_address, r_addr), y) in
      (*r_addr[|2`d0| :+ 2] if not using struct*)
      if trg_x > src_x then
      r1_send(pack(subst(msg1, src, r_addr)))
      else if trg_x < src_x then
      r0_send(pack(subst(msg1, src, r_addr)))
      else
      pass    (*Pass to tile from this block*)
  else
  pass ))

  }}.

Definition _routeend_r (r_addr2: nat) (r0_send r0_receive: UInternalFunction reg_t empty_ext_fn_t) 
: uaction reg_t empty_ext_fn_t :=
  UBind "r_addr" (USugar (UConstBits (Bits.of_nat 4 r_addr2)))
  {{
  let m0 := r0_receive() in (*router input policy will be added here*)
  let msg := unpack(struct_t basic_flit, m0) in
  let new_data := get(msg, new) in
  let src_p := get(msg, src) in
  (( if (src_p != r_addr && new_data) then 
      let trg_x := get(msg, trg_x) in
      let trg_y := get(msg, trg_y) in
      let src_x := get(unpack(struct_t router_address, r_addr), x) in
      let src_y := get(unpack(struct_t router_address, r_addr), y) in
      (*r_addr[|2`d0| :+ 2] if not using struct*)
      if trg_x > src_x then
      fail
      else if trg_x < src_x then
      r0_send(pack(subst(msg, src, r_addr)))
      else
      pass    (*Pass to tile from this block*)
  else
  pass ))
  }}.

Definition routecenterfn (n:nat) (r1 r2 : reg_t): uaction reg_t empty_ext_fn_t :=
  _routecenter_r n (r_send r1) (r_send r2) (r_receive r1) (r_receive r2).

Definition routestartfn (r1 : reg_t): uaction reg_t empty_ext_fn_t :=
  _routestart_r 0 (r_send r1) (r_receive r1). 

Definition routeendfn  (r1 : reg_t): uaction reg_t empty_ext_fn_t :=
  _routeend_r regno (r_send r1) (r_receive r1).

(* Definition to_action (rl: rule_name_t) := 
  match rl with
  | router_1 => routestartfn r1
  | router_2 => routecenterfn 1 r1 r2
  | router_3 => routecenterfn 2 r2 r3
  | router_4 => routeendfn r3
  end.

MetaCoq Quote Definition testl:= Eval hnf in to_action.
Print testl. *)
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
            [tConstruct
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
      [ (nat_to_term 2);
       tConstruct
         {|
           inductive_mind :=
             (MPdot (MPfile ["Pipeline_NOC_parametric"%bs])
                "Registers"%bs, "reg_t"%bs);
           inductive_ind := 0
         |} (Nat.sub n' 2) [];
       tConstruct
         {|
           inductive_mind :=
             (MPdot (MPfile ["Pipeline_NOC_parametric"%bs])
                "Registers"%bs, "reg_t"%bs);
           inductive_ind := 0
         |} (Nat.sub n 2) []]
|} in
branchterm :: generate_branches n'
(* | n =>  *)
  end.

Definition test := Eval compute in generate_branches 3.
Print test.

Fixpoint modify_last_item (l : list (branch term)) : list (branch term) :=
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
      [tConstruct
        {|
          inductive_mind :=
            (MPdot (MPfile ["Pipeline_NOC_parametric"%bs])
                "Registers"%bs, "reg_t"%bs);
          inductive_ind := 0
        |} (Compute Nat.sub n 2) []]
|} in
  l ++ last_term;
  end.

(* Definition branch_body : list (branch term) :=
     [{|
        bcontext := [];
        bbody :=
          tApp
            (tConst
               (MPdot (MPfile ["Pipeline_NOC_parametric"%bs]) "Design"%bs,
                "routestartfn"%bs) [])
            [tConstruct
               {|
                 inductive_mind :=
                   (MPdot (MPfile ["Pipeline_NOC_parametric"%bs])
                      "Registers"%bs, "reg_t"%bs);
                 inductive_ind := 0
               |} 0 []]
      |};
      {|
        bcontext := [];
        bbody :=
          tApp
            (tConst
               (MPdot (MPfile ["Pipeline_NOC_parametric"%bs]) "Design"%bs,
                "routecenterfn"%bs) [])
            [(nat_to_term 1);
             tConstruct
               {|
                 inductive_mind :=
                   (MPdot (MPfile ["Pipeline_NOC_parametric"%bs])
                      "Registers"%bs, "reg_t"%bs);
                 inductive_ind := 0
               |} 0 [];
             tConstruct
               {|
                 inductive_mind :=
                   (MPdot (MPfile ["Pipeline_NOC_parametric"%bs])
                      "Registers"%bs, "reg_t"%bs);
                 inductive_ind := 0
               |} 1 []]
      |};
      {|
        bcontext := [];
        bbody :=
          tApp
            (tConst
               (MPdot (MPfile ["Pipeline_NOC_parametric"%bs]) "Design"%bs,
                "routecenterfn"%bs) [])
            [ (nat_to_term 2);
             tConstruct
               {|
                 inductive_mind :=
                   (MPdot (MPfile ["Pipeline_NOC_parametric"%bs])
                      "Registers"%bs, "reg_t"%bs);
                 inductive_ind := 0
               |} 1 [];
             tConstruct
               {|
                 inductive_mind :=
                   (MPdot (MPfile ["Pipeline_NOC_parametric"%bs])
                      "Registers"%bs, "reg_t"%bs);
                 inductive_ind := 0
               |} 2 []]
      |};
      {|
        bcontext := [];
        bbody :=
          tApp
            (tConst
               (MPdot (MPfile ["Pipeline_NOC_parametric"%bs]) "Design"%bs,
                "routeendfn"%bs) [])
            [tConstruct
               {|
                 inductive_mind :=
                   (MPdot (MPfile ["Pipeline_NOC_parametric"%bs])
                      "Registers"%bs, "reg_t"%bs);
                 inductive_ind := 0
               |} 2 []]
      |}]. *)

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


(*MetaCoq Test Quote (let rl := router_1 in
match rl with
| router_1 => _routestart_r 0 (r_send r1) (r_receive r1)
| router_2 => _routecenter_r 1 (r_send r1) (r_send r2) (r_receive r1) (r_receive r2)
| router_3 => _routecenter_r 2 (r_send r2) (r_send r3) (r_receive r2) (r_receive r3)
| router_4 => _routeend_r 3 (r_send r3) (r_receive r3)
end).*)

 MetaCoq Run ( tmMkDefinition "to_action"%bs match_syn).  

Definition R ( reg : reg_t ) :=
  match reg with
  |  r1 => bits_t (struct_sz basic_flit)
  |  r2 => bits_t (struct_sz basic_flit)
  |  r3 => bits_t (struct_sz basic_flit)
  end.
  
Definition r (reg : reg_t) : R reg :=
  match reg with
  |  r3 => Bits.zero
  |  r1 => Bits.zero
  |  r2 => Bits.zero
  end.

Definition schedule : scheduler :=
    router_4 |> router_3 |> router_2 |>  router_1 |> done. 
     (* route0_r |> route1_r |> route2_r |>  route3_r |> done.  *)

Definition rules :=
  tc_rules R empty_Sigma to_action.

End Design.

Module Proofs.
Import Types.
Import Registers.
Require Import Koika.Frontend.
Require Import Koika.Std.
Require Import Koika.Testing.
Import Design.

Definition r_r2l (reg : reg_t) : R reg :=
  match reg with
  |  r1 => Bits.zero 
  |  r2 => Bits.zero
  |  r3 => Bits.of_nat 14 9729
  end.

Goal
run_schedule r_r2l rules empty_sigma schedule
(fun ctxt =>
let r' := (fun idx => 
match idx with
  | r1=> ctxt.[r1]
  | r2=> ctxt.[r2]
  | r3=> ctxt.[r3]
  end ) in

run_schedule r' rules empty_sigma schedule
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
run_schedule r_l2r rules empty_sigma schedule
(fun ctxt =>
let r' := (fun idx => 
match idx with
  | r1=> ctxt.[r1]
  | r2=> ctxt.[r2]
  | r3=> ctxt.[r3]
  end ) in

run_schedule r' rules empty_sigma schedule
(fun ctxt2 =>
let bits_r0 := ctxt2.[r3] in
Bits.to_nat bits_r0 = 9313)).
  Proof.
    check.
  Defined.

End Proofs.