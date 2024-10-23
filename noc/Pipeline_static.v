Require Import Koika.Frontend.
Require Import Koika.Std.
Require Import Koika.Testing.


Module Types.

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

Module Design.

Import Types.

Notation sz := 14.

Notation nocsize := 4.

Inductive reg_t :=
  | r0
  | r1
  | r2
  | debug
  .

Definition r_send (reg_name: reg_t) : UInternalFunction reg_t empty_ext_fn_t :=
  {{ fun r_send (value: bits_t sz) : unit_t =>
    write0(reg_name, value)
  }}.

Definition r_receive (reg_name: reg_t) : UInternalFunction reg_t empty_ext_fn_t :=
  {{ fun r_receive () : bits_t sz =>
    read0(reg_name)
  }}.

Definition _routestart_r (r_addr2: bits_t 4) (r0_send r0_receive: UInternalFunction reg_t empty_ext_fn_t) 
: uaction reg_t empty_ext_fn_t :=
UBind "r_addr" (USugar (UConstBits r_addr2))
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
  
Definition _routecenter_r (r_addr2: bits_t 4) (r0_send r1_send r0_receive r1_receive: UInternalFunction reg_t empty_ext_fn_t) 
: uaction reg_t empty_ext_fn_t :=
  UBind "r_addr" (USugar (UConstBits r_addr2))
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

Definition _routeend_r (r_addr2: bits_t 4) (r0_send r0_receive: UInternalFunction reg_t empty_ext_fn_t) 
: uaction reg_t empty_ext_fn_t :=
  UBind "r_addr" (USugar (UConstBits r_addr2))
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
Inductive rule_name_t :=
  | route0_r
  | route1_r
  | route2_r
  | route3_r.

Definition to_action rl :=
  match rl with
  | route0_r => _routestart_r Ob~0~0~0~0 (r_send r0) (r_receive r0)
  | route1_r => _routecenter_r Ob~0~0~0~1 (r_send r0) (r_send r1) (r_receive r0) (r_receive r1)
  | route2_r => _routecenter_r Ob~0~0~1~0 (r_send r1) (r_send r2) (r_receive r1) (r_receive r2)
  | route3_r => _routeend_r Ob~0~0~1~1 (r_send r2) (r_receive r2)
  end.

Definition R ( reg : reg_t ) :=
  match reg with
  |  r0 => bits_t (struct_sz basic_flit)
  |  r1 => bits_t (struct_sz basic_flit)
  |  r2 => bits_t (struct_sz basic_flit)
  |  debug => bits_t (struct_sz basic_flit)
  end.
  
Definition r (reg : reg_t) : R reg :=
  match reg with
  |  r0 => Bits.zero
  |  r1 => Bits.zero
  |  r2 => Bits.zero
  |  debug => Bits.zero
  end.

Definition schedule : scheduler :=
    route3_r |> route2_r |> route1_r |>  route0_r |> done. 
     (* route0_r |> route1_r |> route2_r |>  route3_r |> done.  *)

Definition rules :=
  tc_rules R empty_Sigma to_action.

End Design.

