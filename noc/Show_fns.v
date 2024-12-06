Require Import noc.setup.
Require Import Koika.Frontend.
Require Import Koika.Std.
Require Import Coq.Vectors.Fin.

Module Shows.

Import Setup.

Definition show_router (r : router_reg_t) : string :=
  match r with
  | state => "state"
  | downstream => "downstream"
  end.

Definition show_extcon (e : ext_com_t) : string :=
  match e with
  | input => "input"
  | output => "output"
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

Definition show_ext {nocsize:nat} (reg : (ext_fn_t (S nocsize))) : string :=
    match reg with
    | ext_fun n f s => ("ext"  ++ (show_extcon s) ++ (fin_to_string f))%string
    end. 
 
Definition show_rule {nocsize:nat} (rule : (rule_name_t (S nocsize))) : string :=
  match rule with
  | rule n f => ("rule" ++ (fin_to_string f))%string
  end.

Instance Show_reg {nocsize:nat} : Show (reg_t (S nocsize)) :=
  {| show := show_reg |}.

Instance Show_rule {nocsize:nat} : Show (rule_name_t (S nocsize)) :=
  {| show := show_rule |}.

Instance Show_ext {nocsize:nat} : Show (ext_fn_t (S nocsize)) :=
  {| show := show_ext |}.
  
End Shows.