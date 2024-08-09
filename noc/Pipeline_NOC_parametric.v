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

From MetaCoq Require Import bytestring.
Open Scope bs.
Notation regno := 3.

Fixpoint generate_constructors (n : nat) : list constructor_body :=
  match n with
  | 0 => []
  | S n' =>
    let name := "r" ++ string_of_nat (S n') in
    let cstr := {| cstr_name := name;
                   cstr_args := [];
                   cstr_indices := [];
                   cstr_type := tRel 0;
                   cstr_arity := 0 |} in
    cstr :: generate_constructors n'
  end.

Definition quoteregt :=  {|
ind_finite := Finite;
ind_npars := 0;
ind_params := [];
ind_bodies :=
[{|
     ind_name := "reg_t";
     ind_indices := [];
     ind_sort := sType (Universe.make' Level.lzero);
     ind_type := tSort (sType (Universe.make' Level.lzero));
     ind_kelim := IntoAny;
     ind_ctors := generate_constructors 3;
     ind_projs := [];
     ind_relevance := Relevant
   |}];
ind_universes := Monomorphic_ctx;
ind_variance := None
|}.

MetaCoq Run (
  tmMkInductive' quoteregt
).

End Registers.

Module Design.

Import Types.
Import Registers.
Require Import Koika.Frontend.
Require Import Koika.Std.
Require Import Koika.Testing.

Notation sz := 14.

Notation nocsize := 4.


Print reg_t.
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
  | route0_r => _routestart_r Ob~0~0~0~0 (r_send r1) (r_receive r1)
  | route1_r => _routecenter_r Ob~0~0~0~1 (r_send r1) (r_send r2) (r_receive r1) (r_receive r2)
  | route2_r => _routecenter_r Ob~0~0~1~0 (r_send r2) (r_send r3) (r_receive r2) (r_receive r3)
  | route3_r => _routeend_r Ob~0~0~1~1 (r_send r3) (r_receive r3)
  end.

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
    route3_r |> route2_r |> route1_r |>  route0_r |> done. 
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