Require Import Koika.Frontend.
Require Import Koika.Std.
Require Import Koika.Testing.


(* Structure of standard flit *)
(* also used as burst header *)
(* HW-Doc.pdf page 8 *)

Module Types.

  Definition xy_cord :=
    {|
    struct_name := "xy_cord";
    struct_fields :=
      [
        ("x" , bits_t 1);
        ("y" , bits_t 1)
      ]
    |}.
  
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
      ("trg" , bits_t 2);
      ("data" , bits_t 4)
    ]
  |}.

End Types.

Module Design.

  Import Types.

  Notation sz := 6.

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

Definition send1: UInternalFunction reg_t empty_ext_fn_t :=
  {{ fun send1 (value: bits_t 6) : unit_t =>
    write0(ou1, value)
  }}.

Definition receive1: UInternalFunction reg_t empty_ext_fn_t :=
  {{ fun receive1 () : bits_t 6 =>
    read0(in1)
  }}.

Definition send0: UInternalFunction reg_t empty_ext_fn_t :=
  {{ fun send0 (value: bits_t 6) : unit_t =>
    write0(ou0, value)
  }}.

Definition receive0: UInternalFunction reg_t empty_ext_fn_t :=
  {{ fun receive0 () : bits_t 6 =>
    read0(in0)
  }}.


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
  | in0 => Bits.of_nat 6 49
  | in1 => Bits.of_nat 6 20
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
    (*write0(ou0, Ob~0~0~0~0~0)*) 
  }}.


Definition _routexy_r i : uaction reg_t empty_ext_fn_t :=
  {{
    let r_addr := Ob~0~0 in
    let m0 := read0(i) in
    let addr := get(unpack(struct_t basic_flit, m0), trg) in
    if addr[Ob~1] > r_addr[Ob~1] then
        write0(ou0, m0)
    else if addr[Ob~0] > r_addr[Ob~0] then
        write0(ou1, m0)
    else
      pass
  }}.

Check Ob~0~0.
Compute {{Ob~0~0[Ob~0]}}.
Print Syntax.uaction. 
Definition _routepr_r (r_addr2: bits_t 2) (receive send0 send1: UInternalFunction reg_t empty_ext_fn_t) : uaction reg_t empty_ext_fn_t :=
  UBind "r_addr" (USugar (UConstBits r_addr2))
  {{
      let m0 := receive() in
       let addr := get(unpack(struct_t basic_flit, m0), trg) in
    if addr[Ob~1] > r_addr[Ob~1] then
        send0(m0)
    else if addr[Ob~0] > r_addr[Ob~0] then
        send1(m0)
    else
      pass
  }}.

Print _routepr_r.
 (* Definition to_action rl :=
    match rl with
    | route0_r => _routepr_r Ob~0~0 receive0 send0 send1
    | route1_r => _routepr_r Ob~0~0 receive1 send0 send1
    end. *)



Definition to_action rl :=
    match rl with
    | route0_r => _routepr_r Ob~0~0 receive0 send0 send1
    | route1_r => _routepr_r Ob~0~0 receive1 send0 send1
    end.

  Definition schedule : scheduler :=
  route0_r |> route1_r |> done.

Print Syntax.uaction.

  Definition rules :=
    tc_rules R empty_Sigma to_action.

End Design.

Module PropTests.

  Import Design.
  Import Testing.

  Goal
    run_action r (rules route0_r)
    (fun ctxt =>
      let bits_r0 := ctxt.[ou0] in
      Bits.to_nat bits_r0 = 49
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


  Goal
    run_schedule r rules empty_sigma schedule
    (fun ctxt =>
       let r' := (fun idx => 
                    match idx with
                    | in0 => ctxt.[in0]
                    | in1 =>  ctxt.[in1]
                    | in0nd =>  ctxt.[in0nd]
                    | in1nd => ctxt.[in1nd]
                    | ou0 =>  ctxt.[ou0]
                    | ou1 =>  ctxt.[ou1]
                    end ) in

       run_schedule r' rules empty_sigma schedule
         (fun ctxt2 =>
            let bits_ou0 := ctxt2.[ou0]           in
            let nat_ou0  := Bits.to_nat bits_ou0 in

            nat_ou0 = 8
    )).
  Proof.
    check.
  Defined.

End PropTests.
