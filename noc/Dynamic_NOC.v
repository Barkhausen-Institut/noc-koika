Require Import Koika.Frontend.
Require Import Koika.Std.
Require Import Koika.Testing.
Require Import Types.
Require Import Router.

Module Type NOC_data.
  Parameter nocsize: nat.
End NOC_data.

(* Module DynamicNOC(ND:NOC_data).
Import ND. *)
Module Design.
Import Types.
Definition nocsize:=4.
Definition regno := (Nat.sub nocsize 1).

Inductive reg_t := reg_ (n: Vect.index regno).
Inductive rule_name_t := router_ (n: Vect.index nocsize).

Definition reg n :=
  reg_ (match index_of_nat regno n with
        | Some n => n
        | None => thisone
        end).

Definition router n :=
  router_ (match index_of_nat nocsize n with
        | Some n => n
        | None => thisone
        end).


Print reg_t.
Module MyRegs <: Registers.
Definition reg_t:=reg_t.
End MyRegs.


Module Routerfns:= Router(MyRegs).
Import Routerfns.
Definition routefail(r_addr2: nat) (r0: reg_t) 
: uaction reg_t empty_ext_fn_t :=
{{ fail }}.
Compute router 5.
Compute router_ (anotherone (anotherone (anotherone (anotherone _)))).
Definition to_action rl :=
  match rl with
  | router_ (thisone)  => routestartfn 0 (reg 0)
  | router_ (anotherone thisone) => routecenterfn 1 (reg 0) (reg 1)  
  | router_ (anotherone (anotherone thisone))  => routecenterfn 2 (reg 1) (reg 2)
  | router_ (anotherone (anotherone (anotherone thisone)))  => routeendfn 3 (reg 2)
  | router_ (anotherone (anotherone (anotherone (anotherone _)))) => routefail 0 (reg 0) 
  end.


Definition R ( reg : reg_t ) :=
  match reg with
  |  _ => bits_t (struct_sz basic_flit)
  end.
  
Definition r (reg : reg_t) : R reg :=
  match reg with
  |  _ => Bits.zero
  end.

  Definition schedule : scheduler :=
    (router 3) |> (router 2) |> (router 1) |>  (router 0) |> done. 
     (* route0_r |> route1_r |> route2_r |>  route3_r |> done.  *)

Definition rules :=
  tc_rules R empty_Sigma to_action.
End Design.

Module Proofs.
Import Design.

Definition r_r2l (reg : reg_t) : R reg :=
  match reg with
  | reg_ (thisone)  => Bits.zero
  | reg_ (anotherone thisone) => Bits.zero
  | reg_ (anotherone (anotherone thisone))  => Bits.of_nat 14 9729
  | _ => Bits.zero
  end.

Goal
run_schedule r_r2l rules empty_sigma schedule
(fun ctxt =>
let r' := (fun idx => 
match idx with
  | reg_ (thisone)  => ctxt[(reg 0)]
  | reg_ (anotherone thisone) => ctxt[(reg 1)]
  | reg_ (anotherone (anotherone thisone))  => ctxt[(reg 2)]
  | _ => Bits.zero
  end ) in

run_schedule r' rules empty_sigma schedule
(fun ctxt2 =>
let bits_r0 := ctxt2.[(reg 0)] in
Bits.to_nat bits_r0 = 8705)).
  Proof.
    check.
  Defined.


(*8289 = 1 0000 0011 00001*)
Definition r_l2r (reg : reg_t) : R reg :=
  match reg with
  |  r0 => Bits.of_nat 14 8289 
  |  r1 => Bits.zero
  |  r2 => Bits.zero
  | debug => Bits.zero
  end.

Goal
run_schedule r_l2r rules empty_sigma schedule
(fun ctxt =>
let r' := (fun idx => 
match idx with
  | r0=> ctxt.[r0]
  | r1=> ctxt.[r1]
  | r2=> ctxt.[r2]
  | debug => ctxt.[debug]
  end ) in

run_schedule r' rules empty_sigma schedule
(fun ctxt2 =>
let bits_r0 := ctxt2.[r2] in
Bits.to_nat bits_r0 = 9313)).
  Proof.
    check.
  Defined.

End Proofs.