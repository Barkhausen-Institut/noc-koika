Require Import Koika.Frontend.
Require Import Koika.Std.
Require Import noc.actions.
Require Import noc.Types.
Require Import Koika.Testing.

(* Require Import Coq.Strings.Byte. *)


Module MyTypeSize <: Typesize.
  Definition nocsize := 4.
  Definition data_sz := 4.
End MyTypeSize.

Module NoC4 := FNoc MyTypeSize.
Import NoC4 NoC4.d.Routerfns NoC4.d.Routerfns.NOC_setup MyTypeSize.

Definition r (reg : (reg_t nocsize)) : R reg :=
  match reg with
  |  _ => Bits.zero
  end.


Definition sigdenote (fn : (ext_fn_t nocsize)) : Sig_denote (Sigma fn) :=
  match fn with
  | _ => fun x => x +b (Bits.of_nat 9 0)
  end.

Definition r_r2l (reg : (reg_t nocsize)) : R reg :=
  match reg with
  |  _ => Bits.zero 
  end.

(* Compute run_schedule r_r2l to_action sigdenote schedule. *)


(* Definition snocsize:= of_nat nocsize.
Definition module_name:= String.to_string (String.append "NoC"%bs snocsize). *)
(* Definition external (r: rule_name_t) := false. *)


  Definition package :=
    {|
    ip_koika :=
    {|
    koika_reg_types := R;
    koika_reg_init := r;
    koika_ext_fn_types := Sigma;
    koika_rules := to_action;
    koika_rule_external := false;
    koika_scheduler := schedule;
    koika_module_name :="NoC4"
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

Definition prog := Interop.Backends.register package.
Extraction "noc.ml" prog.