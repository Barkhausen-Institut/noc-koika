Require Import Types.
Require Import Koika.Frontend.
Require Import Koika.Std.
Require Import Koika.Testing.

Module Type Registers.
Parameter reg_t : Type.
End Registers.

Module Router (Regs:Registers).
Import Regs.
Import Types.

Inductive ext_fn_t :=
| Tile_In
| Tile_Out.

Definition Sigma (fn: ext_fn_t) : ExternalSignature :=
  match fn with
  | Tile_In => {$ bits_t 1 ~> bits_t sz $}
  | Tile_Out => {$ bits_t sz ~> bits_t sz $}
  end.

(* Definition to_tile : UInternalFunction reg_t ext_fn_t :=
  {{ fun to_tile (value: bits_t sz) : unit_t =>
    extcall Tile_Intf(value)
  }}. *)

Definition r_send (reg_name: reg_t) : UInternalFunction reg_t ext_fn_t :=
  {{ fun r_send (value: bits_t sz) : unit_t =>
    write0(reg_name, value ^  (extcall Tile_In(|1`d0|)))
  }}.

Definition r_receive (reg_name: reg_t) : UInternalFunction reg_t ext_fn_t :=
  {{ fun r_receive () : bits_t sz =>
      read0(reg_name)
  }}.

Definition _routestart_r (r_addr2: nat) (r0_send r0_receive: UInternalFunction reg_t ext_fn_t) 
: uaction reg_t ext_fn_t :=
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
        r0_send(extcall Tile_Out(m0)) 
        
    else
    pass ))
}}.
  
Definition _routecenter_r (r_addr2: nat) (r0_send r1_send r0_receive r1_receive: UInternalFunction reg_t ext_fn_t) 
: uaction reg_t ext_fn_t :=
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
      r0_send(extcall Tile_Out(m0)) 
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
      r0_send(extcall Tile_Out(m1))
  else
  pass ))

  }}.

Definition _routeend_r (r_addr2: nat) (r0_send r0_receive: UInternalFunction reg_t ext_fn_t) 
: uaction reg_t ext_fn_t :=
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
      r0_send(extcall Tile_Out(m0))     (*Pass to tile from this block*)
  else
  pass ))
  }}.

Definition routecenterfn (n:nat) (r1 r2 : reg_t): uaction reg_t ext_fn_t :=
  _routecenter_r n (r_send r1) (r_send r2) (r_receive r1) (r_receive r2).

Definition routestartfn (n:nat) (r1 : reg_t): uaction reg_t ext_fn_t :=
  _routestart_r n (r_send r1) (r_receive r1). 

Definition routeendfn (n:nat) (r1 : reg_t): uaction reg_t ext_fn_t :=
  _routeend_r n (r_send r1) (r_receive r1).


End Router.