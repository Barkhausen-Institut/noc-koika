Require Import Koika.Frontend.
Require Import Koika.Std.
Require Import Koika.Testing.

Module simple.

Inductive reg_t :=
  | r0
  | r1
  | r_ack
  .

Definition R ( reg : reg_t ) :=
  match reg with
  |  r0 => bits_t 4
  |  r1 => bits_t 4
  |  r_ack => bits_t 4
  end.
  
Definition r (reg : reg_t) : R reg :=
  match reg with
  |  r0 => Bits.zero
  |  r1 => Bits.zero
  |  r_ack => Bits.zero
  end.

Inductive ext_fn_t :=
  | noc_enter
  | noc_exit.

Definition Sigma (fn: ext_fn_t) :=
  match fn with
  | noc_enter => {$ bits_t 4 ~> bits_t 4 $}
  | noc_exit => {$ bits_t 4 ~> bits_t 4 $}
  end. 


Definition router0 :uaction reg_t ext_fn_t :=
    {{
      let msg := (extcall noc_enter(|4`d0|)) in
      write0(r0, msg)
    }}.
    
Definition router1 : uaction reg_t ext_fn_t :=
    {{
      let msg := read0(r0) in
      write0(r1, msg)
    }}.

Definition router2 : uaction reg_t ext_fn_t :=
    {{
      let msg := read0(r1) in
      write0(r_ack, extcall noc_exit(msg))
    }}.


Inductive rule_name_t :=
  | route0_r
  | route1_r
  | route2_r.

Definition to_action rl := match rl with
 | route0_r => router0
 | route1_r => router1
 | route2_r => router2
end.

Definition schedule : scheduler :=
    route0_r |> route1_r |> route2_r |> done.

Definition rules :=
  tc_rules R Sigma to_action.

Module Tests.

Definition r_l2r (reg : reg_t) : R reg :=
  match reg with
  |  r0 => Bits.zero
  |  r1 => Bits.zero
  |  r_ack => Bits.zero
  end.

Definition sigdenote fn : Sig_denote (Sigma fn) :=
  match fn with
  | noc_enter => fun x => x +b (Bits.of_nat 4 10)
  | noc_exit => fun x => x +b (Bits.of_nat 4 0)
  end.

Lemma l2r:
    run_schedule r_l2r rules sigdenote schedule
(fun ctxt =>
let r' := (fun idx => 
match idx with
  | r0=> ctxt.[r0]
  | r1=> ctxt.[r1]
  | r_ack=> ctxt.[r_ack]
  end ) in

run_schedule r' rules sigdenote schedule
(fun ctxt2 =>
let bits_r0 := ctxt2.[r1] in
Bits.to_nat bits_r0 =  10)).
  Proof.
    check.
  Defined.

