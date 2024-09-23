From MetaCoq.Template Require Import All.
Require Import Types.
Require Import Router. 
Require Import Koika.Frontend.
Require Import Koika.Std.
Require Import Koika.Testing.
Require Import NOCSyntax.

Module MyTypes <: Typesize.
Definition nocsize := 4.
Definition data_sz := 4.  
End MyTypes.

Module MyNOCSize <: NOC_data.
  Definition nocsize := 4.
End MyNOCSize.

Module NOCImpl. 
(* Print  Registers. *)

Import MCMonadNotation.
Module NOC_syn := NOCSyntax(MyNOCSize).
(* Module NOC_type := Types(MyTypes). *)
Import NOC_syn.
Import MyNOCSize.
(* Import NOC_type. *)

Definition interfacesize := Nat.mul nocsize 2.

MetaCoq Run (
  tmMkInductive' (quoteind "reg_t" regprefix regno) ;;
  tmMkInductive' (quoteind "rule_name_t" ruleprefix nocsize);;
  tmMkInductive' (quoteind "ext_fn_t" extfnprefix interfacesize)
).

Print reg_t.
Print rule_name_t.
Print ext_fn_t.

Module MyRegs <: Registers.
Definition reg_t:=reg_t.
Definition ext_fn_t:= ext_fn_t.
End MyRegs.


Module Routerfns:= Router(MyRegs)(MyTypes).
Import Routerfns.
Import NOC_type.   (*TODO Is there a way to avoid this additio*)



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

 (* Definition to_action (rl: rule_name_t) := 
  match rl with
  | router_1 => routestartfn 0 r1 r4 extfn_1 extfn_2
  | router_2 => routecenterfn 1 r1 r2 r5 extfn_3 extfn_4
  | router_3 => routecenterfn 2 r2 r3 r6 extfn_5 extfn_6
  | router_4 => routeendfn 3 r3 r7 extfn_7 extfn_8
  end.

Check to_action.

MetaCoq Quote Definition testl:= Eval unfold to_action in to_action.
Print testl.   *)

MetaCoq Run ( tmMkDefinition "to_action"%bs match_syn).  

Print to_action.

MetaCoq Run ( tmMkDefinition "schedule"%bs scheduler_synatx). 

Definition external (r: rule_name_t) := false.


Definition snocsize:= string_of_nat nocsize.
Definition module_name:= String.to_string (String.append "NoC"%bs snocsize).
Definition rules :=
  tc_rules R Sigma' to_action.

  Definition package :=
    {|
    ip_koika :=
    {|
    koika_reg_types := R;
    koika_reg_init := r;
    koika_ext_fn_types := Sigma';
    koika_rules := rules;
    koika_rule_external := external;
    koika_scheduler := schedule;
    koika_module_name :=module_name
    |};
    
    ip_sim := {| sp_ext_fn_specs fn :=
    {| efs_name := show fn;
       efs_method := false |};
  sp_prelude := None |};
  ip_verilog := {| vp_ext_fn_specs fn :=
  {| efr_name := show fn;
     efr_internal := false
        |} |}
    |}.
(* Definition r_send_r1 := r_send r1. 

Definition tc_r_send := tc_function R Sigma r_send_r1.
Definition tc_r_receive := tc_function R Sigma r_receive. *)

Definition prog := Interop.Backends.register package.
Extraction "noc.ml" prog.

End NOCImpl.



Module Proofs.
Import NOCImpl.

(*8809 -> 10001001101001*)

(* Definition r2test (reg : reg_t) : R reg :=
  match reg with
  |  r1 => Bits.of_nat 14 8257 
  |  r2 => Bits.zero
  |  r3 => Bits.zero
  end. *)


(* Lemma router2:
    run_action r2test(rules router_2)
    (fun ctxt =>
      let bits_r2 := ctxt.[r2] in
      Bits.to_nat bits_r2 = 8769
    ).
  Proof.
    check.
  Defined.

  Definition r2testback (reg : reg_t) : R reg :=
    match reg with
    |  r1 => Bits.zero
    |  r2 => Bits.of_nat 14 9217 
    |  r3 => Bits.zero
    end.
  
  
  Lemma router2back:
      run_action r2testback(rules router_2)
      (fun ctxt =>
        let bits_r1 := ctxt.[r1] in
        Bits.to_nat bits_r1 = 8705
      ).
    Proof.
      check.
    Defined. *)
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

Print forward.
Compute eq_refl.

(*8289 = 1 0000 0011 00001*)
Definition r_l2r (reg : reg_t) : R reg :=
  match reg with
  |  r1 => Bits.of_nat 9 304 
  |  r2 => Bits.zero
  |  r3 => Bits.zero
  | _ => Bits.zero
  end.

Goal
run_schedule r_l2r rules sigdenote schedule
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
let bits_r0 := ctxt2.[r3]in
Bits.to_nat bits_r0 = 432)).
  Proof.
    check.
  Defined.


Definition sigdenote2 fn : Sig_denote (Sigma' fn) :=
  match fn with
  | extfn_1 => fun x => x +b (Bits.of_nat 9 304)
  | _ => fun x => x +b (Bits.of_nat 9 0)
  end.

  Definition r_l2r_input_interface (reg : reg_t) : R reg :=
    match reg with
    |  r1 => Bits.zero
    |  r2 => Bits.zero
    |  r3 => Bits.zero
    | _ => Bits.zero
    end.

  Goal
  run_schedule r_l2r_input_interface rules sigdenote2 schedule
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
  let r'' := (fun idx => 
  match idx with
  | r1=> ctxt2.[r1]
  | r2=> ctxt2.[r2]
  | r3=> ctxt2.[r3]
  | r4=> ctxt2.[r4]
  | r5=> ctxt2.[r5]
  | r6=> ctxt2.[r6]
  | r7=> ctxt2.[r7]
    end ) in

    run_schedule r'' rules sigdenote schedule
(fun ctxt3 =>
let r''' := (fun idx => 
match idx with
| r1=> ctxt3.[r1]
| r2=> ctxt3.[r2]
| r3=> ctxt3.[r3]
| r4=> ctxt3.[r4]
| r5=> ctxt3.[r5]
| r6=> ctxt3.[r6]
| r7=> ctxt3.[r7]
  end ) in
  run_schedule r''' rules sigdenote schedule
  (fun ctxt4 =>
let bits_out := ctxt4.[r7]in
let bits_in := ctxt.[r1] in
let bits_r3 := ctxt3.[r3] in
Bits.to_nat bits_out = 432 /\
Bits.to_nat bits_r3 = 432 /\
Bits.to_nat bits_in = 304 )))). (*Check acknowledge register, check rightmost noc reg, and check input*)
  Proof.
    check.
  Defined.

(*Load right*)
Definition sigdenote3 fn : Sig_denote (Sigma' fn) :=
    match fn with
    | extfn_3 => fun x => x +b (Bits.of_nat 9 370)
    | _ => fun x => x +b (Bits.of_nat 9 0)
    end.
  
    Goal
    run_schedule r_l2r_input_interface rules sigdenote3 schedule
    (fun ctxt => 
    let bits_r0 := ctxt.[r2]in
    Bits.to_nat bits_r0 = 370).
    Proof.
    check.
    Defined.

(*Load left*)    
Definition sigdenote4 fn : Sig_denote (Sigma' fn) :=
    match fn with
    | extfn_3 => fun x => x +b (Bits.of_nat 9 322)
    | _ => fun x => x +b (Bits.of_nat 9 0)
    end.
  
    Goal
    run_schedule r_l2r_input_interface rules sigdenote4 schedule
    (fun ctxt => 
    let bits_r0 := ctxt.[r1]in
    Bits.to_nat bits_r0 = 322).
    Proof.
    check.
    Defined.

Definition interfacesize := Nat.mul nocsize 2.
Definition regno :=  Nat.add nocsize (Nat.sub nocsize 1).


    (* MetaCoq Run (
      tmMkInductive' (quoteind "reg_t" regprefix regno) ;;
      tmMkInductive' (quoteind "rule_name_t" ruleprefix nocsize);;
      tmMkInductive' (quoteind "ext_fn_t" extfnprefix interfacesize)
  dt <- tmMkInductive (quote_ind "my_dt" n)
  tmLemma "XYZ" (P dt).
    )

    MetaCoq Run (
  tmMkInductive' (quoteind "reg_t" regprefix regno) ;;
  tmMkInductive' (quoteind "rule_name_t" ruleprefix nocsize);;
  tmMkInductive' (quoteind "ext_fn_t" extfnprefix interfacesize)
). *)
Lemma XYZ : 
  forall nocsize,
  let Sigma := 
    InductiveDecl "name" (quoteind "reg_t" nocsize) ::
    InductiveDecl "name" (quoteind "reg_t" nocsize) :: 
    fst P_quoted 
  in {t | Sigma ;;; [ ] |- t : tmApp <% P %> (quote_ind n) }.

End Proofs.