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
      ("new" , bits_t 1);
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

Module Design.

  Import Types.

  Notation sz := 10.

  Inductive reg_t :=
    | north_in
    | south_in
    | east_in
    | north_out
    | south_out
    | east_out
      .

(*  Inductive ext_fn_t :=
    | Inputin0
    | Inputin1
      .
*)

Definition northsend: UInternalFunction reg_t empty_ext_fn_t :=
  {{ fun northsend (value: bits_t 10) : unit_t =>
    write0(north_out, value)
  }}.

Definition southsend: UInternalFunction reg_t empty_ext_fn_t :=
  {{ fun southsend (value: bits_t 10) : unit_t =>
    write0(south_out, value)
  }}.

Definition eastsend: UInternalFunction reg_t empty_ext_fn_t :=
  {{ fun eastsend (value: bits_t 10) : unit_t =>
    write0(east_out, value)
  }}.

Definition northreceive: UInternalFunction reg_t empty_ext_fn_t :=
  {{ fun northreceive () : bits_t 10 =>
    read0(north_in)
  }}.

Definition southreceive: UInternalFunction reg_t empty_ext_fn_t :=
  {{ fun southreceive () : bits_t 10 =>
    read0(south_in)
  }}.

Definition eastreceive: UInternalFunction reg_t empty_ext_fn_t :=
  {{ fun eastreceive () : bits_t 10 =>
    read0(east_in)
  }}.



Definition R ( reg : reg_t ) :=
  match reg with
  | north_in => bits_t (struct_sz basic_flit)
  | south_in => bits_t (struct_sz basic_flit)
  | east_in => bits_t (struct_sz basic_flit)
  | north_out => bits_t (struct_sz basic_flit)
  | south_out => bits_t (struct_sz basic_flit)
  | east_out => bits_t (struct_sz basic_flit)
  end.

(* 834 = 1 10 10 00010*)
Definition r (reg : reg_t) : R reg :=
  match reg with
  | north_in => Bits.of_nat 10 834
  | south_in => Bits.zero
  | east_in => Bits.zero
  | north_out => Bits.zero
  | south_out => Bits.zero
  | east_out => Bits.zero
  end.

Inductive rule_name_t :=
  | route0_r.

Check Ob~0~0.
Compute {{Ob~0~0[Ob~0]}}.
Print Syntax.uaction. 
Definition _routepr_r (r_addr2: bits_t 4) (northreceive southreceive eastreceive northsend southsend eastsend: UInternalFunction reg_t empty_ext_fn_t) 
: uaction reg_t empty_ext_fn_t :=
  UBind "r_addr" (USugar (UConstBits r_addr2))
  {{
    let m0 := northreceive() in (*router input policy will be added here*)
    let new_data := get(unpack(struct_t basic_flit, m0), new) in
    if (new_data) then
        let trg_x := get(unpack(struct_t basic_flit, m0), trg_x) in
        let trg_y := get(unpack(struct_t basic_flit, m0), trg_y) in
        let src_x := get(unpack(struct_t router_address, r_addr), x) in
        let src_y := get(unpack(struct_t router_address, r_addr), y) in
        (*r_addr[|2`d0| :+ 2]*)
        if trg_x > src_x then
        fail
        else if trg_x < src_x then
        eastsend(m0)
        else if trg_y > src_y then
        northsend(m0)
        else if trg_y < src_y then
        southsend(m0)
        else
          pass    (*Pass to tile from this else*)
    else
      pass
  }}.

Print _routepr_r.



Definition to_action rl :=
    match rl with
    | route0_r => _routepr_r Ob~0~1~0~1 northreceive southreceive eastreceive northsend southsend eastsend
    end.

  Definition schedule : scheduler :=
  route0_r |> done.

Print Syntax.uaction.

  Definition rules :=
    tc_rules R empty_Sigma to_action.

End Design.

Module RouterTests.

  Import Design.
  Import Testing.


  
  (* 834 = 1 10 10 00010*)

  (* 834 = 1 10 10 00010*)

  Definition r_west (reg : reg_t) : R reg :=
  match reg with
  | north_in => Bits.of_nat 10 834
  | _ => Bits.zero
  end.


  (* 834 = 1 10 00 00010*)

  Definition r_east (reg : reg_t) : R reg :=
  match reg with
  | north_in => Bits.of_nat 10 770
  | _ => Bits.zero
  end.

  Lemma check_east:
    run_action r_east (rules route0_r)
    (fun ctxt =>
      let bits_r0 := ctxt.[east_out] in
      Bits.to_nat bits_r0 = 770
    ).
  Proof.
    check.
  Defined.

  (* 834 = 1 10 01 00010*)

  Definition r_north (reg : reg_t) : R reg :=
  match reg with
  | north_in => Bits.of_nat 10 802
  | _ => Bits.zero
  end.

  Lemma check_north:
    run_action r_north (rules route0_r)
    (fun ctxt =>
      let bits_r0 := ctxt.[north_out] in
      Bits.to_nat bits_r0 = 802
    ).
  Proof.
    check.
  Defined.

  (* 834 = 1 00 01 00010*)

  Definition r_south (reg : reg_t) : R reg :=
  match reg with
  | north_in => Bits.of_nat 10 546
  | _ => Bits.zero
  end.

  Lemma check_south:
    run_action r_south (rules route0_r)
    (fun ctxt =>
      let bits_r0 := ctxt.[south_out] in
      Bits.to_nat bits_r0 = 546
    ).
  Proof.
    check.
  Defined.

 
    
End RouterTests.
