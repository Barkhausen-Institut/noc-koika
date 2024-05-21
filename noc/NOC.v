Require Import Koika.Frontend.
Require Import Koika.Std.
Require Import Koika.Testing.
Require Import noc.Router.

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
      | r0_0d5_c
      | r0_0d5_a
      | r0d5_1_c
      | r0d5_1_a
      | r1_0d5_c
      | r1_0d5_a
      | r0d5_0_c
      | r0d5_0_a
      .


Definition R reg :=
  match reg with
    | r0_0d5_c => bits_t (struct_sz basic_flit) 
    | r0_0d5_a => bits_t (struct_sz basic_flit)
    | r0d5_1_c => bits_t (struct_sz basic_flit)
    | r0d5_1_a => bits_t (struct_sz basic_flit)
    | r1_0d5_c => bits_t (struct_sz basic_flit)
    | r1_0d5_a => bits_t (struct_sz basic_flit)
    | r0d5_0_c => bits_t (struct_sz basic_flit)
    | r0d5_0_a => bits_t (struct_sz basic_flit)
  end.

Definition r idx : R idx :=
  match idx with
    | r0_0d5_c => Bits.of_nat 6 49 
    | r0_0d5_a => Bits.zero
    | r0d5_1_c => Bits.zero
    | r0d5_1_a => Bits.zero
    | r1_0d5_c => Bits.zero
    | r1_0d5_a => Bits.zero
    | r0d5_0_c => Bits.zero
    | r0d5_0_a => Bits.zero
  end.

Inductive rule_name_t :=
  | route0_r
  | route1_r
  | route2_r
  | route3_r.

(* SEND FUNCTIONS*)
Definition sendr0_0d5_a: UInternalFunction reg_t empty_ext_fn_t :=
  {{ fun sendr0_0d5_a (value: bits_t 6) : unit_t =>
    write0(r0_0d5_a, value)
  }}.

Definition sendr0_0d5_c: UInternalFunction reg_t empty_ext_fn_t :=
  {{ fun sendr0_0d5_c (value: bits_t 6) : unit_t =>
    write0(r0_0d5_c, value)
  }}.

Definition sendr0d5_1_a: UInternalFunction reg_t empty_ext_fn_t :=
  {{ fun sendr0d5_1_a (value: bits_t 6) : unit_t =>
    write0(r0d5_1_a, value)
  }}.

Definition sendr0d5_1_c: UInternalFunction reg_t empty_ext_fn_t :=
  {{ fun sendr0d5_1_c (value: bits_t 6) : unit_t =>
    write0(r0d5_1_c, value)
  }}.

Definition sendr1_0d5_a: UInternalFunction reg_t empty_ext_fn_t :=
  {{ fun sendr1_0d5_a (value: bits_t 6) : unit_t =>
    write0(r1_0d5_a, value)
  }}.

Definition sendr1_0d5_c: UInternalFunction reg_t empty_ext_fn_t :=
  {{ fun sendr1_0d5_c (value: bits_t 6) : unit_t =>
    write0(r1_0d5_c, value)
  }}.

Definition sendr0d5_0_a: UInternalFunction reg_t empty_ext_fn_t :=
  {{ fun sendr0d5_0_a (value: bits_t 6) : unit_t =>
    write0(r0d5_0_a, value)
  }}.

Definition sendr0d5_0_c: UInternalFunction reg_t empty_ext_fn_t :=
  {{ fun sendr0d5_0_c (value: bits_t 6) : unit_t =>
    write0(r0d5_0_c, value)
  }}.

(* RECIEVE FUNCTIONS*)
Definition receiver0_0d5_a: UInternalFunction reg_t empty_ext_fn_t :=
  {{ fun receiver0_0d5_a () : bits_t 6 =>
    read0(r0_0d5_a)
  }}.

Definition receiver0_0d5_c: UInternalFunction reg_t empty_ext_fn_t :=
  {{ fun receiver0_0d5_c () : bits_t 6 =>
    read0(r0_0d5_c)
  }}.

Definition receiver0d5_1_a: UInternalFunction reg_t empty_ext_fn_t :=
  {{ fun receiver0d5_1_a () : bits_t 6 =>
    read0(r0d5_1_a)
  }}.

Definition receiver0d5_1_c: UInternalFunction reg_t empty_ext_fn_t :=
  {{ fun receiver0d5_1_c () : bits_t 6 =>
    read0(r0d5_1_c)
  }}.

Definition receiver1_0d5_a: UInternalFunction reg_t empty_ext_fn_t :=
  {{ fun receiver1_0d5_a () : bits_t 6 =>
     read0(r1_0d5_a)
  }}.

Definition receiver1_0d5_c: UInternalFunction reg_t empty_ext_fn_t :=
  {{ fun receiver1_0d5_c () : bits_t 6 =>
    read0(r1_0d5_c)
  }}.

Definition receiver0d5_0_a: UInternalFunction reg_t empty_ext_fn_t :=
  {{ fun receiver0d5_0_a () : bits_t 6 =>
    read0(r0d5_0_a)
  }}.

Definition receiver0d5_0_c: UInternalFunction reg_t empty_ext_fn_t :=
  {{ fun receiver0d5_0_c () : bits_t 6 =>
    read0(r0d5_0_c)
  }}.


Definition _routepr_r (r_addr: bits_t 2) (receive0 receive1 send0 send1: UInternalFunction reg_t empty_ext_fn_t) : uaction reg_t empty_ext_fn_t :=
  {{
      let r_addr := Ob~0~0 in
      let m0 := receive0() ^ receive1() in
       let addr := get(unpack(struct_t basic_flit, m0), trg) in
    if addr[Ob~1] > r_addr[Ob~1] then
        send0(m0)
    else if addr[Ob~0] > r_addr[Ob~0] then
        send1(m0)
    else
      pass
  }}.



(*Definition _routepr_r r send receive address : uaction r empty_ext_fn_t :=
  {{
      let newdata := receive  in
      
      if newdata then
        let m0 := receive in
        let addr0 := get(unpack(struct_t basic_flit, m0), trg) in
        if !addr0 then
          send(m0)
        else
          send(m0)
      else
        fail
  }}. *)


Inductive router_t :=
  | rout4con r_addr
  | rout6con 

 Definition to_action rl :=
    list 
    end.


  Definition schedule : scheduler :=
  route0_r |> route1_r |> route3_r |>  route2_r |> done.

  Definition rules :=
    tc_rules R empty_Sigma to_action.

End Design.
