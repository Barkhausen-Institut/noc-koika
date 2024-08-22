Require Import Koika.Frontend.
Require Import Koika.Std.
Require Import Koika.Testing.
Require Import NOC_setup.
Require Import Router.
Require Import Types.



Module MyNOCSize <: NOC_data.
  Definition nocsize := 4.  
End MyNOCSize.

Module Design:= NOCSetup(MyNOCSize).
Import Design.
Import MyNOCSize.
Import Types.
Definition reg n :=
  reg_ (match index_of_nat regno n with
        | Some n => n
        | None => thisone
        end).
Print MyNOCSize.nocsize.
Definition router n :=
  router_ (match index_of_nat nocsize n with
        | Some n => n
        | None => thisone
        end). 

        
Module MyRegs <: Registers.
Definition reg_t:=reg_t.
End MyRegs.


Module Routerfns:= Router(MyRegs).        
Import Routerfns.

(* Definition to_action rl :=
  match rl with
  | router_ (thisone)  => routestartfn 0 (reg 0)
  | router_ (anotherone thisone) => routecenterfn 1 (reg 0) (reg 1)  
  | router_ (anotherone (anotherone thisone))  => routecenterfn 2 (reg 1) (reg 2)
  | router_ (anotherone (anotherone (anotherone thisone)))  => routeendfn 3 (reg 2)
  | router_ (anotherone (anotherone (anotherone (anotherone _)))) => routefail 0 (reg 0) 
  end. *)



Definition to_action rl :=
match rl with
| router_ idx => let idx_nat := index_to_nat idx in
  if Nat.eqb idx_nat 0 then (routestartfn 0 (reg 0)) 
  else if Nat.eqb idx_nat regno then (routeendfn regno (reg (Nat.sub regno 1))) 
  else (routecenterfn idx_nat (reg (Nat.sub idx_nat 1)) (reg idx_nat))  
end.

Definition R ( reg : reg_t ) :=
  match reg with
  |  _ => bits_t (struct_sz basic_flit)
  end.
  
Definition r (reg : reg_t) : R reg :=
  match reg with
  |  _ => Bits.zero
  end.

  Fixpoint schedule_gen (n:nat): scheduler:=
  match n with
  | 0 => done
  | S n' => (router n') |> (schedule_gen n')
  end.

  Definition schedule : scheduler := schedule_gen nocsize.
    (* (router 3) |> (router 2) |> (router 1) |>  (router 0) |> done.  *)
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