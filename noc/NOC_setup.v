Require Import Koika.Frontend.
Require Import Koika.Std.
Require Import Router.
Require Import Types.
From Coq Require Import Arith Lia Program.
From Equations Require Import Equations.
Require Import Coq.Vectors.Fin.

Module Type NOC_data.
  Parameter nocsize: nat.
  Axiom nocprop: nocsize>1.
End NOC_data.

Module NOCSetup(ND:NOC_data)(MyTypes: Typesize).
Import ND. 
Module NOC_type := Types(MyTypes).
Import NOC_type.
Definition interfacesize := Nat.mul nocsize 2. 
Definition regno := Nat.add nocsize (Nat.sub nocsize 1).


Inductive reg_t : nat -> Type :=
  | reg_ : forall num, Fin.t num -> reg_t num.

  Inductive rule_name_t : nat -> Type :=
  | rule_ : forall num, Fin.t num -> rule_name_t num.

  Inductive ext_fn_t : nat -> Type :=
  | ex_ : forall num, Fin.t num -> ext_fn_t num.

  Print Fin.

(* Inductive reg_t: nat->Type := reg_ (n: Vect.index regno).
Inductive rule_name_t := rule_ (n: Vect.index nocsize).

Inductive ext_fn_t := ex_ (n: Vect.index interfacesize). *)

Module MyRegs <: Registers.
Definition reg_t:=reg_t regno.
Definition ext_fn_t:= ext_fn_t interfacesize.
End MyRegs.

Module Routerfns:= Router(MyRegs)(MyTypes).        
Import Routerfns.

Locate "<".
Print lt.
Locate "<=".
Print le.
Locate "<>".
Print not. 

 (* Fixpoint nat_to_fin {n : nat} (m : nat) : option (Fin.t n) :=
  match n return option (Fin.t n) with
  | 0 => None (* No valid index if the bound is 0 *)
  | S n' => match m with
            | 0 => Some Fin.F1 (* The 0th index corresponds to Fin.F1 *)
            | S m' => match nat_to_fin m' with
                      | Some fin' => Some (Fin.FS fin') (* Successor index *)
                      | None => None
                      end
            end
  end. *)

  Check Nat.nlt_0_r.
  Check Fin.of_nat_lt.
  Definition nat_to_fin {n : nat} (i : nat) (pf : i < n) : Fin.t n :=
  Fin.of_nat_lt pf.
  Check Nat.nlt_0_r.

  Example example_fin_auto : 0 < 7.
Proof.
  lia. (* auto and info_auto dont work for some numbers*)
Qed.

Checl
Compute Fin.of_nat_lt example_fin_auto.
  Compute @nat_to_fin nocsize 6.
Check Nat.lt_0_succ.

Fail Check rule_ nocsize Fin.F1.
Equations to_action' (nocsize:nat) (H: 1<=nocsize) (rl : rule_name_t nocsize) : uaction (reg_t regno) (ext_fn_t interfacesize) := 
(* to_action 0 H _ := { }; *)
(* to_action 1 (le_S n H1) _ with H1 := {} ;  *)
to_action' 1 H (rule_ nocsize Fin.F1) := routestartfn 0 (reg_ regno Fin.F1) (reg_ regno (Fin.FS Fin.F1)) 
(ex_ interfacesize Fin.F1) (ex_ interfacesize (Fin.FS Fin.F1)) ;
to_action' _ H r with r := 
to_action' nocsize H (rule_ nocsize Fin.F1) => routecenterfn 0 (reg_ ) (reg_ 1) (ex_ 0) (ex_ 1).

(* to_action nocsize H (rule_ nocsize n) := routecenterfn n (reg_ n) (reg_ (Nat.add nocsize n) ex_ 2n ex_ 2n+1) *)

Equations to_action (nocsize:nat) (H: 2<=nocsize) (rl : rule_name_t nocsize) : uaction (reg_t regno) (ext_fn_t interfacesize) := 
(* to_action 0 H _ := { }; *)
to_action 1 (le_S n H1) _ with H1 := {} ; 
to_action 2 H r with r := 
| rule_ 1 => routeendfn 1 (reg_ 1) (reg_fn (Nat.add nocsize 1)) (ex_ 2) (ex_ 3)
to_action _ H r with r := 
to_action' (Nat.sub nocsize 1) H rl.


  let idx_nat := index_to_nat idx in
  if Nat.eqb idx_nat 0 then
    routestartfn 0 (reg_  indices 1)
  else if Nat.eqb idx_nat regno then
    let idx' := index_of_nat (Nat.sub idx_nat - 1) in
    routeendfn regno (reg_ idx')
  else
    let idx' := index_of_nat (Nat.sub idx_nat - 1) in
    routecenterfn idx_nat (reg_ idx') (reg_ idx).

 
(* Fixpoint nat_to_fin {n : nat} (m : nat) : option (Fin.t n) :=
  match n return option (Fin.t n) with
  | 0 => None (* No valid index if the bound is 0 *)
  | S n' => match m with
            | 0 => Some Fin.F1 (* The 0th index corresponds to Fin.F1 *)
            | S m' => match nat_to_fin m' with
                      | Some fin' => Some (Fin.FS fin') (* Successor index *)
                      | None => None
                      end
            end
  end.

Compute @nat_to_fin 4 2.

Inductive reg_t (num : nat) : Type :=
  | reg_ : Fin.t num -> reg_t num.

Inductive rule_name_t (num : nat) : Type :=
  | rule_ : Fin.t num -> rule_name_t num.

Inductive ext_fn_t (num : nat) : Type :=
  | ext_ : Fin.t num -> ext_fn_t num.


(*How is num correctly determined*)
Definition reg_fn (num : nat) (n : nat) : option (reg_t num) :=  
    match Fin.of_nat n num with
    | inleft fin_idx => Some (reg_ num fin_idx)  (* Valid index, return register *)
    | inright _ => None  (* Index out of bounds, return None *)
    end.

Definition rule_fn (num : nat) (n : nat) : option (rule_name_t num) :=
    match Fin.of_nat n num with
    | inleft fin_idx => Some (rule_ num fin_idx)  (* Valid index, return register *)
    | inright _ => None  (* Index out of bounds, return None *)
    end.

Definition e_fn (num : nat) (n : nat) : option (ext_fn_t num) :=
    match Fin.of_nat n num with
    | inleft fin_idx => Some (ext_ num fin_idx)  (* Valid index, return register *)
    | inright _ => None  (* Index out of bounds, return None *)
    end.

Search Fin.t. 
Compute rule_ 2 (Fin.FS Fin.F1).
Check rule_fn nocsize 0.
(* Axiom rego_ge_1 : regno >= 1. (*
  unfold regno.
  induction nocsize eqn:H.
  - set (H1 := nocprop).
    rewrite H in H1.
    unfold ">"%nat in H1.
    apply Nat.nlt_succ_diag_l in H1.
    contradiction.
  - apply IHn. *)
Definition reg_of_nat (n:nat) :reg_t.
  set (a := index_of_nat regno n).
  destruct a eqn:H.
  - exact (reg_ i).
  - unfold a in H.
    destruct regno eqn:H1.
    + admit.
    + simpl in H.
    unfold index_of_nat in H.
    Admitted.

Print index_of_nat.
Definition reg_of_nat n :=
  reg_ (match index_of_nat regno n with
        | Some n => n
        | None => thisone
        end). *)

 (* Definition router n :=
  router_ (match index_of_nat nocsize n with
        | Some n => n
        | None => thisone
        end).   *)
 
(* Compute index 3.
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
  
Fixpoint get_nth_item_fin {A : Type} (l : list A) (n : Fin.t regno) : A :=
  match l with
  | [] => match n with end (* This case is impossible due to the dependent type *)
  | x :: xs =>
    match n with
    | Fin.F1 => x
    | Fin.FS n' => get_nth_item_fin xs n'
    end
  end. *)

Module MyRegs <: Registers.
Definition reg_t:=reg_t regno.
Definition ext_fn_t:= ext_fn_t regno.
End MyRegs.

Module Routerfns:= Router(MyRegs)(MyTypes).        
Import Routerfns.

Check rule_fn.

Definition to_action (rl: rule_name_t nocsize) := 
match rl with
| (rule_fn nocsize 0) => routestartfn 0 reg_fn regno 0 reg_fn regno 1 extfn interfacesize 0 extfn interfacesize 1
| rule_ => routecenterfn 1 r1 r2 r5 extfn_3 extfn_4
| rule_ => routecenterfn 2 r2 r3 r6 extfn_5 extfn_6
| rule_ => routeendfn 3 r3 r7 extfn_7 extfn_8
end.


Equations to_action
 (rl : rule_name_t nocsize) : uaction (reg_t regno) (ext_fn_t interfacesize) := 
to_action (rule_ nocsize) :=
  let idx_nat := index_to_nat idx in
  if Nat.eqb idx_nat 0 then
    routestartfn 0 (reg_  indices 1)
  else if Nat.eqb idx_nat regno then
    let idx' := index_of_nat (Nat.sub idx_nat - 1) in
    routeendfn regno (reg_ idx')
  else
    let idx' := index_of_nat (Nat.sub idx_nat - 1) in
    routecenterfn idx_nat (reg_ idx') (reg_ idx).

 *)



End NOCSetup.


