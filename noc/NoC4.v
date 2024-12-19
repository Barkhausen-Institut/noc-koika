Require Import Koika.Frontend.
Require Import Koika.Std.
Require Import noc.actions.
Require Import noc.Types.
Require Import noc.helpers.
Require Import noc.setup.
Require Import Koika.Testing.
Require Import Coq.Vectors.Fin.
Require Import noc.Show_fns.

From Equations Require Import Equations.

Module MyTypeSize <: Typesize.
  Definition nocsize := 4.
  Definition data_sz := 4.
End MyTypeSize.

Module NoC4 := FNoc MyTypeSize.
Import NoC4 NoC4.d.Routerfns Setup MyTypeSize Shows.
Import (hints) NoC4.d.

(* Definition r (reg : (reg_t (S nocsize))) : R reg := *)
(*   match reg with *)
(*   |  _ => Bits.zero *)
(*   end. *)

Definition sigdenote (fn : (ext_fn_t (S nocsize))) : Sig_denote (Sigma fn) :=
  match fn with
  | _ => fun x => x +b (Bits.of_nat 11 0)
  end.

Definition r_r2l (reg : (reg_t (S nocsize))) : R reg :=
  match reg with
  |  _ => Bits.zero
  end.

Import Instances Helpers.

(** * Fixed-size NoC property
    This property talks about a NoC of size [nocsize=4].
 *)

Lemma P4 (n:nat) (H: (S n) <<= (S nocsize)) :
  run_schedule_compact r_r2l to_action sigdenote schedule
    (fun ctxt =>
      let bits_r := ctxt.[router nocsize (Helpers.widen_fin H (@Fin.F1 n)) state] in
      Bits.to_nat bits_r = 0).
Proof.
  unfold nocsize, run_schedule_compact, create.
  simp schedule.
 Print Rewrite HintDb schedule.
 simp schedule.
 rewrite <- interp_scheduler_cps_correct. Search interp_scheduler_cps.

Admitted.


Definition rule_external (rule : (rule_name_t (S nocsize))) : bool:=
  match rule with
  _ => false
  end.

Timeout 60 Definition package :=
    {|
    ip_koika :=
    {|
    koika_reg_names := Show_reg;
    koika_reg_types := R;
    koika_reg_init := r;
    koika_ext_fn_types := Sigma;
    koika_rules := to_action;
    koika_rule_external := rule_external;
    koika_rule_names := Show_rule;
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
