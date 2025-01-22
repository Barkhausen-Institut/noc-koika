Require Import Koika.Frontend.
Require Import Koika.Std.
Require Import Koika.Testing.


Module Types.

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

Notation nocsize := 4.

Inductive reg_t :=
  | r0_fw
  | r0_bw  
  | r1_fw
  | r1_bw
  | r2_fw
  | r2_bw
  .

Definition r0_bw_send: UInternalFunction reg_t empty_ext_fn_t :=
  {{ fun r0_bw_send (value: bits_t 10) : unit_t =>
    write0(r0_bw, value)
  }}.

Definition r1_bw_send: UInternalFunction reg_t empty_ext_fn_t :=
  {{ fun r1_bw_send (value: bits_t 10) : unit_t =>
    write0(r1_bw, value)
  }}.

Definition r2_bw_send: UInternalFunction reg_t empty_ext_fn_t :=
  {{ fun r2_bw_send (value: bits_t 10) : unit_t =>
    write0(r2_bw, value)
  }}.

Definition r0_fw_send: UInternalFunction reg_t empty_ext_fn_t :=
  {{ fun r0_fw_send (value: bits_t 10) : unit_t =>
    write0(r0_fw, value)
  }}.

Definition r1_fw_send: UInternalFunction reg_t empty_ext_fn_t :=
  {{ fun r1_fw_send (value: bits_t 10) : unit_t =>
    write0(r1_fw, value)
  }}.

Definition r2_fw_send: UInternalFunction reg_t empty_ext_fn_t :=
  {{ fun r2_fw_send (value: bits_t 10) : unit_t =>
    write0(r2_fw, value)
  }}.

Definition r0_fw_receive: UInternalFunction reg_t empty_ext_fn_t :=
  {{ fun r0_fw_receive () : bits_t 10 =>
    read0(r0_fw)
  }}.

Definition r1_fw_receive: UInternalFunction reg_t empty_ext_fn_t :=
  {{ fun r1_fw_receive () : bits_t 10 =>
    read0(r1_fw)
  }}.

Definition r2_fw_receive: UInternalFunction reg_t empty_ext_fn_t :=
  {{ fun r2_fw_receive () : bits_t 10 =>
    read0(r2_fw)
  }}.

Definition r0_bw_receive: UInternalFunction reg_t empty_ext_fn_t :=
  {{ fun r0_bw_receive () : bits_t 10 =>
    read0(r0_bw)
  }}.

Definition r1_bw_receive: UInternalFunction reg_t empty_ext_fn_t :=
  {{ fun r1_bw_receive () : bits_t 10 =>
    read0(r1_bw)
  }}.

Definition r2_bw_receive: UInternalFunction reg_t empty_ext_fn_t :=
  {{ fun r2_bw_receive () : bits_t 10 =>
    read0(r2_bw)
  }}.


Definition R ( reg : reg_t ) :=
  match reg with
  |  r0_fw => bits_t (struct_sz basic_flit)
  |  r0_bw => bits_t (struct_sz basic_flit)
  |  r1_fw => bits_t (struct_sz basic_flit)
  |  r1_bw => bits_t (struct_sz basic_flit)
  |  r2_fw => bits_t (struct_sz basic_flit)
  |  r2_bw => bits_t (struct_sz basic_flit)
  end.
  
(*1 0011 00001*)
Definition r (reg : reg_t) : R reg :=
  match reg with
  |  r0_fw => Bits.zero 
  |  r0_bw => Bits.of_nat 10 609 
  |  r1_fw => Bits.zero
  |  r1_bw => Bits.zero
  |  r2_fw => Bits.zero
  |  r2_bw => Bits.zero
  end.

Inductive rule_name_t :=
  | route0_r
  | route1_r
  | route2_r
  | route3_r.

Definition _routestart_r (r_addr2: bits_t 4) (r0_send r0_receive: UInternalFunction reg_t empty_ext_fn_t) 
: uaction reg_t empty_ext_fn_t :=
  UBind "r_addr" (USugar (UConstBits r_addr2))
  {{
    let m0 := r0_receive() in (*router input policy will be added here*)
    let new_data := get(unpack(struct_t basic_flit, m0), new) in
    if (new_data) then
        let trg_x := get(unpack(struct_t basic_flit, m0), trg_x) in
        let trg_y := get(unpack(struct_t basic_flit, m0), trg_y) in
        let src_x := get(unpack(struct_t router_address, r_addr), x) in
        let src_y := get(unpack(struct_t router_address, r_addr), y) in
        (*r_addr[|2`d0| :+ 2] if not using struct*)
        if trg_x > src_x then
        r0_send(m0)
        else if trg_x < src_x then
          fail
        else
          pass    (*Pass to tile from this block*)
    else
      pass
  }}.


Definition _routeend_r (r_addr2: bits_t 4) (r0_send r0_receive: UInternalFunction reg_t empty_ext_fn_t) 
: uaction reg_t empty_ext_fn_t :=
  UBind "r_addr" (USugar (UConstBits r_addr2))
  {{
    let m0 := r0_receive() in (*router input policy will be added here*)
    let new_data := get(unpack(struct_t basic_flit, m0), new) in
    if (new_data) then
        let trg_x := get(unpack(struct_t basic_flit, m0), trg_x) in
        let trg_y := get(unpack(struct_t basic_flit, m0), trg_y) in
        let src_x := get(unpack(struct_t router_address, r_addr), x) in
        let src_y := get(unpack(struct_t router_address, r_addr), y) in
        (*r_addr[|2`d0| :+ 2] if not using struct*)
        if trg_x > src_x then
          fail
        else if trg_x < src_x then
          r0_send(m0)
        else
          pass    (*Pass to tile from this block*)
    else
      pass
  }}.

Definition _routecenter_r (r_addr2: bits_t 4) (r0_send r1_send r0_receive r1_receive: UInternalFunction reg_t empty_ext_fn_t) 
: uaction reg_t empty_ext_fn_t :=
  UBind "r_addr" (USugar (UConstBits r_addr2))
  {{
    let m0 := r0_receive() in (*router input policy will be added here*)
    let new_data := get(unpack(struct_t basic_flit, m0), new) in
    if (new_data) then
        let trg_x := get(unpack(struct_t basic_flit, m0), trg_x) in
        let trg_y := get(unpack(struct_t basic_flit, m0), trg_y) in
        let src_x := get(unpack(struct_t router_address, r_addr), x) in
        let src_y := get(unpack(struct_t router_address, r_addr), y) in
        (*r_addr[|2`d0| :+ 2] if not using struct*)
        if trg_x > src_x then
          r1_send(m0)
        else if trg_x < src_x then
          r0_send(m0)
        else
          pass    (*Pass to tile from this block*)
    else
      pass
  }}.


Definition to_action rl :=
  match rl with
  | route0_r => _routestart_r Ob~0~0~0~0 r0_fw_send r0_bw_receive
  | route1_r => _routecenter_r Ob~0~0~0~1 r0_bw_send r1_fw_send r0_fw_receive r1_bw_receive
  | route2_r => _routecenter_r Ob~0~0~1~0 r1_bw_send r2_fw_send r1_fw_receive r2_bw_receive
  | route3_r => _routeend_r Ob~0~0~1~1 r2_bw_send r2_fw_receive
  end.

Definition schedule : scheduler :=
  route3_r |> route2_r |> route1_r |>  route0_r |> done.

Definition rules :=
  tc_rules R empty_Sigma to_action.

End Design.

Module Proofs.
Import Design.

Goal
    run_schedule r rules empty_sigma schedule
    (fun ctxt =>
    let r' := (fun idx => 
    match idx with
      | r0_fw=> ctxt.[r0_fw]
      | r0_bw=> ctxt.[r0_bw]
      | r1_fw=> ctxt.[r1_fw]
      | r1_bw=> ctxt.[r1_bw]
      | r2_fw=> ctxt.[r2_fw]
      | r2_bw=> ctxt.[r2_bw]
      end ) in
    
    run_schedule r' rules empty_sigma schedule
    (fun ctxt2 =>
    let r'' := (fun idx => 
    match idx with
      | r0_fw=> ctxt2.[r0_fw]
      | r0_bw=> ctxt2.[r0_bw]
      | r1_fw=> ctxt2.[r1_fw]
      | r1_bw=> ctxt2.[r1_bw]
      | r2_fw=> ctxt2.[r2_fw]
      | r2_bw=> ctxt2.[r2_bw]
      end ) in

      run_schedule r'' rules empty_sigma schedule
      (fun ctxt3 =>
      let bits_r0 := ctxt3.[r2_fw] in
      Bits.to_nat bits_r0 = 609))).

  Proof.
    check.
  Defined.


End Proofs.
