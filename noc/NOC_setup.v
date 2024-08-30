Require Import Koika.Frontend.
Require Import Koika.Std.
Require Import Router.
Require Import Types.
From Coq Require Import Arith Lia Program.
From Equations Require Import Equations.

Module Type NOC_data.
  Parameter nocsize: nat.
End NOC_data.

Module NOCSetup(ND:NOC_data).
Import ND. 
Import Types.
Definition regno := (Nat.sub nocsize 1).

Inductive reg_t := reg_ (n: Vect.index regno).
Inductive rule_name_t :=
  | route0_r
  | route1_r
  | route2_r
  | route3_r.

(* Inductive rule_name_t := router_ (n: Vect.index nocsize). *)

  (* Axiom index_of_nat_never_none : forall n, index_of_nat regno n <> None. 
Equations reg (n : nat) : reg_t :=  
  reg n :=
  match index_of_nat regno n with
  | Some m => reg_ m
  | None => absurd (index_of_nat regno n = None) index_of_nat_never_none 
  end. *)
(* 
 Definition router n :=
  router_ (match index_of_nat nocsize n with
        | Some n => n
        | None => thisone
        end).  
  *)
Module MyRegs <: Registers.
  Definition reg_t:=reg_t.
End MyRegs.


Module Routerfns:= Router(MyRegs).        
Import Routerfns.
Compute index 3.
Compute index_of_nat nocsize 1.


Fixpoint list_seq_index_anotherone {N : nat} (l : list (index N)) : list (index (S N)) :=
  match l with
  | nil => nil
  | cons el l' => cons (anotherone el) (list_seq_index_anotherone l')
  end.

(* Constucting an ascending list of all possible indecies N *)
Fixpoint list_seq_index (N : nat) : list (index N) :=
  match N with
  | O => nil
  | S N' => cons (thisone) (list_seq_index_anotherone (list_seq_index N'))
  end.

  Fixpoint get_nth_item_default {A : Type} (l : list A) (n : nat) (default : A) : A :=
    match l, n with
    | [], _ => default
    | x :: _, 0 => x
    | _ :: xs, S n' => get_nth_item_default xs n' default
    end.
  
(* Fixpoint get_nth_item_fin {A : Type} (l : list A) (n : Fin.t regno) : A :=
  match l with
  | [] => match n with end (* This case is impossible due to the dependent type *)
  | x :: xs =>
    match n with
    | Fin.F1 => x
    | Fin.FS n' => get_nth_item_fin xs n'
    end
  end. *)


Definition indices := list_seq_index regno.
Compute indices.
Check get_nth_item_default indices 1.
(* Definition get_reg (n: nat): reg_t := reg_ (get_nth_item_default indices n). *)

(* Fixpoint give_index (n: nat) : index nocsize :=
  match n with
  | 0 => thisone
  | S n' => anotherone (give_index n')
  end. *)

(* Equations to_action (rl : rule_name_t) : uaction reg_t empty_ext_fn_t := 
to_action (router_ idx) :=
  let idx_nat := index_to_nat idx in
  if Nat.eqb idx_nat 0 then
    routestartfn 0 (reg_ get_nth_item_default indices 1)
  else if Nat.eqb idx_nat regno then
    let idx' := index_of_nat (Nat.sub idx_nat - 1) in
    routeendfn regno (reg_ idx')
  else
    let idx' := index_of_nat (Nat.sub idx_nat - 1) in
    routecenterfn idx_nat (reg_ idx') (reg_ idx). *)





End NOCSetup.


