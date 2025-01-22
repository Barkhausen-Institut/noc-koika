Require Import Types.
Require Import Router. 
Require Import Koika.Frontend.
Require Import Koika.Std.
Require Import Koika.Testing.

Module MyTypes <: Typesize.
Definition nocsize := 4.
Definition data_sz := 4.  
End MyTypes.

Inductive reg_t : Set :=
	r1 : reg_t
  | r2 : reg_t
  | r3 : reg_t
  | r4 : reg_t
  | r5 : reg_t
  | r6 : reg_t
  | r7 : reg_t.

Inductive rule_name_t : Set :=
	router_1 : rule_name_t
  | router_2 : rule_name_t
  | router_3 : rule_name_t
  | router_4 : rule_name_t.


Inductive ext_fn_t : Set :=
	extfn_1 : ext_fn_t
  | extfn_2 : ext_fn_t
  | extfn_3 : ext_fn_t
  | extfn_4 : ext_fn_t
  | extfn_5 : ext_fn_t
  | extfn_6 : ext_fn_t
  | extfn_7 : ext_fn_t
  | extfn_8 : ext_fn_t.

  Module MyRegs <: Registers.
Definition reg_t:=reg_t.
Definition ext_fn_t:= ext_fn_t.
End MyRegs.


Module Routerfns:= Router(MyRegs)(MyTypes).
Import Routerfns.
Import NOC_type.

Definition Sigma' (fn: ext_fn_t) : ExternalSignature :=
  match fn with
  | _ => {$ bits_t sz ~> bits_t sz $}
  end.


Definition R ( reg : reg_t ) :=
  match reg with
  |  _ => bits_t (struct_sz basic_flit)
  end.
  
Definition r (reg : reg_t) : R reg :=
  match reg with
  |  _ => Bits.zero
  end.


Definition to_action :=
fun rl : rule_name_t =>
match rl with
| router_1 => routestartfn 0 r1 r4 extfn_1 extfn_2
| router_2 => routecenterfn 1 r1 r2 r5 extfn_3 extfn_4
| router_3 => routecenterfn 2 r2 r3 r6 extfn_5 extfn_6
| router_4 => routeendfn 3 r3 r7 extfn_7 extfn_8
end.

Definition schedule : scheduler :=
    router_4 |> router_3 |> router_2 |> router_1 |> done.


Definition rules :=
  tc_rules R Sigma' to_action.
  
    Definition sigdenote fn : Sig_denote (Sigma' fn) :=
        match fn with
        | _ => fun x => x +b (Bits.of_nat 9 0)
        end.
      
      
      Definition r_r2l (reg : reg_t) : R reg :=
        match reg with
        |  r1 => Bits.zero
        |  r2 => Bits.zero
        |  r3 => Bits.of_nat 9 448  
        |  _ => Bits.zero
        end.
      
      (* Definition schedule2 : scheduler :=
        router_1 |> router_2 |> done. *)
      Lemma forward:
      run_schedule r_r2l rules sigdenote schedule
      (fun ctxt =>
      let r' := (fun idx => 
      match idx with
        | r1=> ctxt.[r1]
        | r2=> ctxt.[r2]
        | r3=> ctxt.[r3]
        | r4=> ctxt.[r4]
        | r5=> ctxt.[r5]
        | r6=> ctxt.[r6]
        | r7=> ctxt.[r7]
        end ) in
      
      run_schedule r' rules sigdenote schedule
      (fun ctxt2 =>
      let bits_r0 := ctxt2.[r1] in
      Bits.to_nat bits_r0 = 320)).
        Proof.
          check.
        Defined.
      