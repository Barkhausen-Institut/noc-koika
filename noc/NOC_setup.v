Require Import Koika.Frontend.
Require Import Koika.Std.
Require Import noc.Router.
Require Import noc.Types.
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

Definition regno' := fun nsize => nsize + (nsize-1).


Inductive reg_t : nat -> Type :=
  | reg_ : forall num, Fin.t num -> reg_t num.

  Inductive rule_name_t : nat -> Type :=
  | rule_ : forall num, Fin.t num -> rule_name_t num.

  Inductive ext_fn_t : nat -> Type :=
  | ex_ : forall num, Fin.t num -> ext_fn_t num.

(* Inductive reg_t: nat->Type := reg_ (n: Vect.index regno).
Inductive rule_name_t := rule_ (n: Vect.index nocsize).

Inductive ext_fn_t := ex_ (n: Vect.index interfacesize). *)

Module MyRegs <: Registers.
Definition reg_t:=reg_t regno.
Definition ext_fn_t:= ext_fn_t interfacesize.
End MyRegs.

Module Routerfns:= Router(MyRegs)(MyTypes).        
Import Routerfns.


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


  Definition nat_to_fin {n : nat} (i : nat) (pf : i < n) : Fin.t n :=
    Fin.of_nat_lt pf. 
  
  Example example_fin_auto : 2 < 7.
Proof.
  info_auto 8. (* auto and info_auto dont work for some numbers*)
Qed.

Fixpoint fin_to_nat {n : nat} (f : Fin.t n) : nat :=
  match f with
  | Fin.F1 => 0
  | Fin.FS f' => S (fin_to_nat f')
  end.


Search Fin.t.
Compute Nat.pred nocsize.
Compute Nat.mul 2 3.

Lemma regno_gt_0 : 0 < regno.
Proof.
  unfold regno.
  apply Nat.add_pos_pos.
  - apply Nat.lt_le_incl. exact nocprop.
  - 
    assert (aaa : 1 < nocsize). { exact nocprop. }
    destruct nocsize.
    + inversion aaa.
    + simpl. 
      rewrite Nat.sub_0_r.
      apply Nat.succ_lt_mono.
      exact aaa.
Qed.

Lemma xxx: 2<=nocsize.
Proof.
  exact nocprop.
Qed.

(* Set Equations Debug. *)


Notation "!" := (False_rect _ _).


(* 
    Equations? to_action (nocsize:nat) (H: 2<=nocsize) (rl : rule_name_t nocsize) :
    uaction (reg_t regno ) (ext_fn_t interfacesize) :=
        
       to_action 1 (le_S nocsize H1) _ with H1 := {} ; 
       to_action (S nocsize') H (rule_ nocsize' idx) :=
           let n_idx := fin_to_nat idx in
           (* let interfacesize := Nat.mul nocsize' 2 in 
           let regno := Nat.add (S nocsize') (Nat.sub (S nocsize') 1) in *)
           if Nat.eqb n_idx 0 then
                         routestartfn 0 
                               (reg_ regno (nat_to_fin 0 _)) 
                               (reg_ regno (nat_to_fin nocsize' _)) 
                               (ex_ interfacesize (nat_to_fin 0 _)) 
                               (ex_ interfacesize (nat_to_fin 1 _))
           else if Nat.eqb n_idx nocsize' then
                         routeendfn nocsize'
                               (reg_ regno (nat_to_fin (Nat.pred n_idx) _ ))
                               (reg_ regno (nat_to_fin  (Nat.add (Nat.pred n_idx) nocsize') _))
                               (ex_ interfacesize (nat_to_fin (Nat.mul n_idx 2) _ )) 
                               (ex_ interfacesize (nat_to_fin (S (Nat.mul n_idx 2)) _))
           else
                          routecenterfn n_idx 
                               (reg_ regno (nat_to_fin (Nat.pred n_idx) _ ))
                               (reg_ regno (nat_to_fin  n_idx _))
                               (reg_ regno (nat_to_fin  (Nat.add (Nat.pred n_idx) nocsize') _))
                               (ex_ interfacesize (nat_to_fin (Nat.mul n_idx 2) _ )) 
                               (ex_ interfacesize (nat_to_fin (S (Nat.mul n_idx 2)) _)). *)

Check fin_to_nat.
Print t.
Print nat_to_fin.
Print of_nat_lt.
Equations to_action {n:nat} {H1:n=nocsize} (rl : rule_name_t nocsize) :
  uaction (reg_t regno) (ext_fn_t interfacesize) :=

  @to_action O pf _rl := ! ;
  @to_action 1 pf _rl := ! ;
  @to_action (S noc_size') _pf (rule_ noc_size' idx) with idx :=
    @to_action (S noc_size') _pf (rule noc_size' idx) (F1 0) :=
      routestartfn 0
        (reg_ regno idx) (* travel *)
        (reg_ regno (nat_to_fin (0 + nocsize) ((nocsize-1) + nocsize)) (* output *)
        (ex_ interfacesize (nat_to_fin 0 (nocsize * 2))) (* external in *)
        (ex_ interfacesize (nat_to_fin 1 (nocsize * 2))); (* external out *)

  @to_action (S noc_size') _pf (rule noc_size' idx) (F1 nocsize') :=
    routeendfn noc_size'
      (reg_ regno (nat_to_fin (Nat.pred n_idx) _ ))
      (reg_ regno (nat_to_fin  (Nat.add (Nat.pred n_idx) noc_size') _))
      (ex_ interfacesize (nat_to_fin (Nat.mul n_idx 2) _ ))i
      (ex_ interfacesize (nat_to_fin (S (Nat.mul n_idx 2)) _))

  @to_action (S noc_size) _pf (rule noc_size' idx) (F1 (S n)) :=
      routecenterfn n_idx
        (reg_ regno (nat_to_fin (Nat.pred n_idx) _ ))
        (reg_ regno (nat_to_fin  n_idx _))
        (reg_ regno (nat_to_fin  (Nat.add (Nat.pred n_idx) noc_size') _))
        (ex_ interfacesize (nat_to_fin (Nat.mul n_idx 2) _ ))
        (ex_ interfacesize (nat_to_fin (S (Nat.mul n_idx 2)) _))
    @to_action (S noc_size) pf (rule noc_size' idx) (FS s) := to_action (S nocsize) pf (rule noc_size' s)



      let n_idx := fin_to_nat idx in
        if Nat.eqb n_idx 0 then
        else if Nat.eqb n_idx noc_size' then
        else
.
Next Obligation.
  exfalso.
  assert (bla : 1<nocsize). 1: { exact nocprop. }
  rewrite <- pf in bla.
  inversion bla.
Qed.
Next Obligation.
  exfalso.
  assert (bla : 1<nocsize). 1: { exact nocprop. }
  rewrite <- pf in bla.
  inversion bla.
  inversion H0.
Qed.
Next Obligation. apply regno_gt_0. Qed.
Next Obligation.
  unfold regno.
  rewrite <- _pf.
  simpl.
  rewrite <- Nat.succ_lt_mono.
  rewrite -> plus_n_Sm.
  apply Nat.lt_lt_add_l.
  lia.
Qed.
Next Obligation. unfold interfacesize; lia. Qed.
Next Obligation. unfold interfacesize; lia. Qed.
Next Obligation.
  unfold regno.
  destruct nocsize.
  - inversion _pf.
  - inversion _pf.
    subst. clear _pf.
    induction idx eqn:E.
    * unfold fin_to_nat; simpl; lia.
    * specialize (IHt t eq_refl).
      unfold fin_to_nat; fold (fin_to_nat t).
      Search Nat.pred.
  revert idx.
  rewrite <- _pf.
  intro idx.
  dependent induction idx.
  + unfold fin_to_nat.
    simpl.
    lia.
  + unfold fin_to_nat.
    simpl.
    fold fin_to_nat.
  dependent destruction idx.
  - clear.
  rewrite <- _pf in idx.
  revert _pf.
  destruct idx eqn:H.
Obligations.
 
                            - apply regno_gt_0.
 - unfold regno. simpl.
Qed.
apply regno_gt_0.
Next Obligation.

Search nocsize.
Check le_plus_trans.
apply le_plus_l, nocprop.
Search plus.
apply nocprop.
omega.
Check le_S.
Check le_n.  
replace (nocsize + (nocsize - 1)) with (2 * nocsize - 1).
apply Nat.lt_le_incl.

Search nat. 
Check Nat.lt.
Check Nat.lt_le_incl.
Check Nat.lt_alt.

apply Nat.lt_le_incl.






Definition R ( reg : reg_t regno ) :=
  match reg with
  |  _ => bits_t (struct_sz basic_flit)
  end.
  
Definition r (reg : reg_t regno) : R reg :=
  match reg with
  |  _ => Bits.zero
  end.

Definition Sigma' (fn: ext_fn_t interfacesize) : ExternalSignature :=
  match fn with
  | _ => {$ bits_t sz ~> bits_t sz $}
  end.

End NOCSetup.
  (* Check tc_rules. *)
(* 
  Definition rules :=
  tc_rules R Sigma'  to_action. *)

(* Equations to_action' (nocsize:nat) (H: 1<=nocsize) (rl : rule_name_t nocsize) : uaction (reg_t regno) (ext_fn_t interfacesize) := 
  (* to_action 0 H _ := { }; *)
   to_action 1 (le_S n H1) _ with H1 := {} ; 
   let idx := nat_to_fin nocsize 

  to_action' (S nocsize') H (rule_ nocsize Fin.F1) :=
    routestartfn 0 
                (reg_ regno (nat_to_fin 0 _)) 
                (reg_ regno (nat_to_fin nocsize' _)) 
                (ex_ interfacesize (nat_to_fin 0 _)) 
                (ex_ interfacesize (nat_to_fin 1 _));

  to_action' (S nocsize') H (rule_ (S nocsize) n)  with n == (nat_to_fin nocsize') :=
    | := routerend ...
    | nocsize H (rule_ nocsize idx) :=
        let n_idx := fin_to_nat idx in
        routecenterfn n_idx 
                (reg_ regno (nat_to_fin (Nat.pred n_idx) _ ))
                (reg_ regno (nat_to_fin  n_idx _))
                (reg_ regno (nat_to_fin  (Nat.add (Nat.pred n_idx) nocsize) _))
                (ex_ interfacesize (nat_to_fin (Nat.mul n_idx 2) _ )) 
                (ex_ interfacesize (nat_to_fin (S (Nat.mul n_idx 2)) _)).
(* to_action nocsize H (rule_ nocsize n) := routecenterfn n (reg_ n) (reg_ (Nat.add nocsize n) ex_ 2n ex_ 2n+1) *)

Equations to_action (nocsize:nat) (H: 2<=nocsize) (rl : rule_name_t nocsize) : uaction (reg_t regno) (ext_fn_t interfacesize) := 
(* to_action 0 H _ := { }; *)
  to_action 1 (le_S n H1) _ with H1 := {} ; 
  to_action nocsize H _  := to_action' nocsize _ _;


  to_action _ H r with r := 
to_action' (Nat.sub nocsize 1) H rl.


Definition to_action rl :=
match rl with
| router_ idx => let idx_nat := index_to_nat idx in
  if Nat.eqb idx_nat 0 then (routestartfn 0 (reg 0)) 
  else if Nat.eqb idx_nat regno then (routeendfn regno (reg (Nat.sub regno 1))) 
  else (routecenterfn idx_nat (reg (Nat.sub idx_nat 1)) (reg idx_nat))  
end.
 *)

 
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


(* Compute Fin.of_nat_lt example_fin_auto.
Compute @nat_to_fin 7 1 _.
Check nat_to_fin.
Compute Fin.of_nat_lt example_fin_auto.  
Compute fin_to_nat (Fin.FS Fin.F1). *)

(* Equations get_rule {nocsize:nat} (H: 1<=nocsize) (idx:Fin.t nocsize) : rule_name_t nocsize :=
  (* get_rule 0   -> dicharged by equations *)
  @get_rule (S n) _ idx := rule_ (S n) idx.

Definition idx_zero (n:nat) : Fin.t (S n) := Fin.F1.
Definition idx_one (n:nat) : Fin.t (S (S n)) := Fin.FS (idx_zero n).

Definition lower_bound : Fin.t 4 := Fin.FS (Fin.FS (Fin.FS Fin.F1)).
Print lower_bound.
Print vect_nil.
Print Fin.t.
Inductive vec (T:Type) : nat -> Type :=
  | vec_nil : vec T 0
  | vec_append : forall n, T -> vec T n -> vec T (S n).

Inductive myfin : nat -> Type :=
  | myf1 : forall n, myfin (S n)
  | myfs : forall n, myfin n -> myfin (S n).

Check Fin.F1.

Definition t_2 : Fin.t 3 :=  (Fin.FS (Fin.FS Fin.F1)).
Equations idx' {n:nat} (i:Fin.t n) (ub:nat) :Fin.t n :=
let 
  idx' i'  0    := i';
  idx' i' (S n) := idx' (Fin.FS i') n. 

Equations idx (i:nat) (upper_bound:nat) (H: i<upper_bound)(H2: upper_bound>0) : Fin.t (S upper_bound) :=
  idx 0 ub _ _ := @Fin.F1 ub;
  idx (S n)

Equations idx (i:nat) (sz:nat) (H: i<sz)(H2: sz>0)  : Fin.t sz :=
  idx 0 _ _ _ := Fin.F1;
  idx (S n) sz _ _ := @Fin.FS (S n) (idx n sz _ _ ).

Equations rule_1 (nocsize:nat) (H: 1<=nocsize) (idx:Fin.t n) :rule_name_t nocsize:=
  (* rule_1 0   *)
  rule_1 (S 0) (le_S n H1) _ with H1 := {};
  rule_1 (S (S n)) := rule_ nocsize (Fin.FS (Fin.FS (Fin.F1 n)). *)
