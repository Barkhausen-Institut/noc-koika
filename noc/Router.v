Require Import Koika.Frontend.
Require Import Koika.Std.
Require Import Koika.Testing.


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

  Import Types.

  Notation sz := 5.

  Inductive reg_t :=
      | in0
      | in1
      | in0nd
      | in1nd
      | ou0
      | ou1
      .

(*  Inductive ext_fn_t :=
    | Inputin0
    | Inputin1
      .
*)

Definition R reg :=
  match reg with
  | in0 => bits_t (struct_sz basic_flit)
  | in1 => bits_t (struct_sz basic_flit)
  | in0nd => bits_t 1
  | in1nd => bits_t 1
  | ou0 => bits_t (struct_sz basic_flit)
  | ou1 => bits_t (struct_sz basic_flit)
  end.

Definition r idx : R idx :=
  match idx with
  | in0 => Bits.of_nat 5 8
  | in1 => Bits.of_nat 5 20
  | in0nd => Bits.of_nat 1 1
  | in1nd => Bits.of_nat 1 1
  | ou0 => Bits.zero
  | ou1 => Bits.zero
  end.

Inductive rule_name_t :=
  | route0_r
  | route1_r.

Definition _route0_r i i_nd : uaction reg_t empty_ext_fn_t :=
  {{
    let newdata := read0(i_nd) in
    write0(i_nd, Ob~0);
  if newdata then
    let m0 := read0(i) in
    let addr0 := get(unpack(struct_t basic_flit, m0), trg) in
    if !addr0 then
        write0(ou0, m0)
    else 
      write0(ou1, m0)
  else
    fail 
  }}.


  Definition to_action rl :=
    match rl with
    | route0_r => _route0_r in0 in0nd
    | route1_r => _route0_r in1 in1nd
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


Module PropTests.

  Import Design.
  Import Testing.

  Goal
    run_action r (rules route0_r)
    (fun ctxt =>
      let bits_r0 := ctxt.[ou0] in
      Bits.to_nat bits_r0 = 8
    ).
  Proof.
    check.
  Defined.

Goal
run_action r (rules route1_r)
    (fun ctxt =>
      let bits_r0 := ctxt.[ou1] in
      Bits.to_nat bits_r0 = 20
    ).
    Proof.
    check.
  Defined.

(*Set nd = 0*)
Goal
run_action r (rules route0_r)
    (fun ctxt =>
       let bits_r0 := ctxt.[ou1] in
       let bits_in0nd := ctxt.[in0nd] in
       Bits.to_nat bits_in0nd = 0 /\ Bits.to_nat bits_r0=0
    ).
    Proof.
    check.
  Defined.
