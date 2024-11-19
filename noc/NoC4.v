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

Definition r (reg : (reg_t (S nocsize))) : R reg :=
  match reg with
  |  _ => Bits.zero
  end.

Definition sigdenote (fn : (ext_fn_t (S nocsize))) : Sig_denote (Sigma fn) :=
  match fn with
  | _ => fun x => x +b (Bits.of_nat 9 0)
  end.

Definition r_r2l (reg : (reg_t (S nocsize))) : R reg :=
  match reg with
  |  _ => Bits.zero 
  end.


(* Lemma P (n:nat) (H: NoC4.d.le_t (S n) (S nocsize)) :
  run_schedule r_r2l to_action sigdenote schedule
    (fun ctxt =>
      let bits_r := ctxt.[router nocsize (NoC4.d.widen_fin H (@Fin.F1 n)) state] in
      Bits.to_nat bits_r = 0). *)

Timeout 5 Definition package :=
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