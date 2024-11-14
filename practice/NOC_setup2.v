Require Import Koika.Frontend.
Require Import Koika.Std.
Require Import Router.
Require Import Types.
From Coq Require Import Arith Lia Program.
From Equations Require Import Equations.
Require Import Coq.Vectors.Fin.

Module Type NOC_data.
  Parameter nocsize: nat.
  Axiom nocprop: 1<nocsize.
End NOC_data.

Module NOCSetup(ND:NOC_data)(MyTypes: Typesize).
Import ND. 
Module NOC_type := Types(MyTypes).
Import NOC_type.
Definition interfacesize := Nat.mul nocsize 2. 
Definition regno := Nat.add nocsize (Nat.sub nocsize 1).

Definition regno' (r:nat):= Nat.add r (Nat.sub r 1).
Definition interfacesize' (nocsize:nat) := Nat.mul nocsize 2. 
Inductive reg_t := reg_ (n: Fin.t regno).
Inductive rule_name_t := rule_ (n: Fin.t regno).
Inductive ext_fn_t := ex_ (n: Fin.t regno).


Module MyRegs <: Registers.
Definition reg_t:=reg_t.
Definition ext_fn_t:= ext_fn_t.
End MyRegs.

Module Routerfns:= Router(MyRegs)(MyTypes).        
Import Routerfns.

Fixpoint fin_to_nat {n : nat} (f : Fin.t n) : nat :=
  match f with
  | Fin.F1 => 0
  | Fin.FS f' => S (fin_to_nat f')
end.

Definition nat_to_fin {n : nat} (i : nat) (pf : i < n) : Fin.t n :=
  Fin.of_nat_lt pf. 

Equations? to_action (nocsize:nat) (H: 2<=nocsize) (rl : rule_name_t) :
uaction reg_t ext_fn_t:=
    
   to_action 1 (le_S nocsize H1) _ with H1 := {} ; 
   to_action (S nocsize') H (rule_ idx) :=
       let n_idx := fin_to_nat idx in
       (* let interfacesize := Nat.mul nocsize' 2 in 
       let regno := Nat.add (S nocsize') (Nat.sub (S nocsize') 1) in *)
       if Nat.eqb n_idx 0 then
                     routestartfn 0 
                           (reg_ (nat_to_fin 0 _)) 
                           (reg_ (nat_to_fin nocsize' _)) 
                           (ex_ (nat_to_fin 0 _)) 
                           (ex_ (nat_to_fin 1 _))
       else if Nat.eqb n_idx nocsize' then
                     routeendfn nocsize'
                           (reg_ (nat_to_fin (Nat.pred n_idx) _ ))
                           (reg_ (nat_to_fin  (Nat.add (Nat.pred n_idx) nocsize') _))
                           (ex_  (nat_to_fin (Nat.mul n_idx 2) _ )) 
                           (ex_  (nat_to_fin (S (Nat.mul n_idx 2)) _))
       else
                      routecenterfn n_idx 
                           (reg_ (nat_to_fin (Nat.pred n_idx) _ ))
                           (reg_ (nat_to_fin  n_idx _))
                           (reg_ (nat_to_fin  (Nat.add (Nat.pred n_idx) nocsize') _))
                           (ex_ (nat_to_fin (Nat.mul n_idx 2) _ )) 
                           (ex_ (nat_to_fin (S (Nat.mul n_idx 2)) _)).
Proof.
- unfold regno.