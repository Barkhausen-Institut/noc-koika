Require Import Koika.Frontend.
Require Import Koika.Std.

(* Structure of standard flit *)
(* also used as burst header *)
(* HW-Doc.pdf page 8 *)

Module Types.

  Definition standard_flit :=
  {|
  struct_name := "standard_flit";
  struct_fields :=
    [
      (* if this flit starts burst - if it is a burst header *)
      ("burst"     , bits_t 1 );
      (* if this flit expects and acknowledgement *)
      ("arq"       , bits_t 1 );
      (* byte selector of payload *)
      (*
      header flit only: specifies the first [3:0] and last [7:4]
      valid byte of the data in the payload flits
      *)
      ("bsel"      , bits_t 8 );
      ("src_modid" , bits_t 8 ); 
      ("src_chipid", bits_t 6 );
      ("trg_modid" , bits_t 8 );
      ("trg_chipid", bits_t 6 );
      (* read, write .. etc *)
      ("mode"      , bits_t 4 );
      (* destination address *)
      ("addr"      , bits_t 32);
      (* header flit only: number of upcomming payload flits *)
      ("data"      , bits_t 64)
    ]
  |}.

  Definition basic_flit :=
  {|
  struct_name := "basic_flit";
  struct_fields :=
    [
      ("trg" , bits_t 1);
      ("data" , bits_t 4)
    ]
  |}.

End Types.

Module Design.

  Notation sz := 5.

  Inductive reg_t :=
      | in0
      | in1
      | ou0
      | ou1
      .

  Definition R reg :=
      match reg with
      | in0 => bits_t sz
      | in1 => bits_t sz
      | ou0 => bits_t sz
      | ou1 => bits_t sz
      end.

  Definition r idx : R idx :=
      match idx with
      | in0 => Bits.of_nat sz 8
      | in1 => Bits.of_nat sz 20
      | ou0 => Bits.of_nat sz 0
      | ou1 => Bits.of_nat sz 0
      end.

  Inductive rule_name_t :=
    | route0_r
    | route1_r.

  Definition _route0_r : uaction reg_t empty_ext_fn_t :=
  {{
  let m0 := read0(in0) in
  let addr0 := m0[Ob~1~0~0] in
      if !addr0 then
        write0(ou0, m0)
      else 
        write0(ou1, m0) 
  }}. 

  Definition _route1_r : uaction reg_t empty_ext_fn_t :=
  {{
  let m1 := read0(in1) in
  let addr1 := m1[Ob~1~0~0] in
      if !addr1 then
        write0(ou0, m1)
      else 
        write0(ou1, m1) 
  }}.

  Definition to_action rl :=
    match rl with
    | route0_r => _route0_r
    | route1_r => _route1_r
    end.


  Definition schedule : scheduler :=
  route0_r |> route1_r |> done.

  Definition rules :=
    tc_rules R empty_Sigma to_action.

End Design.

(*
Module TestSetup.

  Import Design.

  Notation run_action_no_compute' R rules action reg_vals :=
    (must'' (run_action_no_compute R rules action reg_vals)).

  (*! Define some convenience functions. !*)
  Notation run_action action reg_vals := (run_action' R rules action reg_vals).
  Definition run_schedule := run_schedule' R rules.

  (*! Type check the function right here. !*)
  Definition fun_3x :=
    tc_function R empty_Sigma times_three.

  Definition fun_isodd :=
    tc_function R empty_Sigma isodd.

End TestSetup.
*)

Require Import Koika.Testing.

Module PropTests.

  Import Design.
  Import Testing.
  
  Notation run_action action reg_vals := (run_action' R rules action reg_vals).
  Definition run_schedule := run_schedule' R rules.

   (* Checking both registers: *)
  Example assert_ou0:
    let ctxt    := run_action route0_r r in
    let bits_ou0 := ctxt.[ou0]           in
    let nat_ou0  := Bits.to_nat bits_r0 in
    assertion (nat_ou0 = 8).
  check.
  Defined.

  






