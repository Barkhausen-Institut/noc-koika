Require Import Koika.Frontend.
Require Import Koika.Std.
Require Import noc.actions.
Require Import noc.Types.
Require Import noc.helpers.
Require Import noc.setup.
Require Import Koika.Testing.
Require Import Coq.Vectors.Fin.


(* Require Import Coq.Strings.Byte. *)

Module MyTypeSize <: Typesize.
  Definition nocsize := 4.
  Definition data_sz := 4.
End MyTypeSize.

Module NoC4 := FNoc MyTypeSize.
Import NoC4 NoC4.d.Routerfns Setup MyTypeSize. 

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

Import Instances.
Lemma P (n:nat) (H: Helpers.le_t (S n) (S nocsize)) :
  run_schedule r_r2l to_action sigdenote schedule
    (fun ctxt =>
      let bits_r := ctxt.[router nocsize (Helpers.widen_fin H (@Fin.F1 n)) state] in
      Bits.to_nat bits_r = 0).
    Admitted.

Definition show_router (r : router_reg_t) : string :=
  match r with
  | state => "state"
  | downstream => "downstream"
  end.

Fixpoint fin_to_nat {n : nat} (f : Fin.t n) : nat :=
  match f with
  | @F1 _ => 0
  | @FS _ f' => S (fin_to_nat f')
  end.

Definition fin_to_string {n:nat} (f: Fin.t n): string :=
  Show_nat.string_of_nat (fin_to_nat f).
  

Definition show_reg {nocsize:nat} (reg : (reg_t (S nocsize))) : string :=
  match reg with
  | router n f s => ("router"  ++ (show_router s) ++ (fin_to_string f))%string
  end.  

Definition show_rule {nocsize:nat} (rule : (rule_name_t (S nocsize))) : string :=
  match rule with
  | rule n f => ("rule" ++ (fin_to_string f))%string
  end.  

(* Definition example_reg : reg_t 3 := router 2 (@FS 2 (@F1 1)) state.
Definition example_rule  : rule_name_t 3 := rule 2 (@FS 2 (@F1 1)). *)

Definition rule_external (rule : (rule_name_t (S nocsize))) : bool:=
  match rule with
  _ => false
  end.

Instance Show_reg : Show (reg_t (S nocsize)) :=
  {| show := show_reg |}.

Instance Show_rule : Show (rule_name_t (S nocsize)) :=
  {| show := show_rule |}.

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