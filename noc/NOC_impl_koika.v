Require Import Koika.Frontend.
Require Import Koika.Std.
Require Import Koika.Testing.
Require Import NOC_setup.
Require Import Router.
Require Import Types.
Set Equations Transparent.
Import Types.
Module MyNOCSize <: NOC_data.
  Definition nocsize := 4.  
End MyNOCSize.

Module Design:= NOCSetup(MyNOCSize).
Import Design.
Import MyNOCSize.
Import Types.

Definition reg n :=
  reg_ (match index_of_nat regno n with
        | Some n => n
        | None => thisone
        end).
Print MyNOCSize.nocsize.
(* Definition router n :=
  router_ (match index_of_nat nocsize n with
        | Some n => n
        | None => thisone
        end).  *)

        
Module MyRegs <: Registers.
Definition reg_t:=reg_t.
End MyRegs.

Print rule_name_t.
Module Routerfns:= Router(MyRegs).        
Import Routerfns.
(*
Module Routerfns:= Router(MyRegs).        
Import Routerfns. 
*)

Definition _routetest (r0_send r0_receive: UInternalFunction reg_t empty_ext_fn_t) 
: uaction reg_t empty_ext_fn_t :=
{{
    let m0 := r0_receive() in (*router input policy will be added here*)
    r0_send(m0)
}}.

Compute _routetest.
Print USugar.
  
Definition routetest (reg : reg_t):= _routetest (r_send reg) (r_receive reg).
(* Definition to_action rl :=
  match rl with
  | route0_r => _routestart_r Ob~0~0~0~0 (r_send r0) (r_receive r0)
  | route1_r => _routecenter_r Ob~0~0~0~1 (r_send r0) (r_send r1) (r_receive r0) (r_receive r1)
  | route2_r => _routecenter_r Ob~0~0~1~0 (r_send r1) (r_send r2) (r_receive r1) (r_receive r2)
  | route3_r => _routeend_r Ob~0~0~1~1 (r_send r2) (r_receive r2)
  end. *)

  Equations to_action (rl:rule_name_t) : uaction reg_t empty_ext_fn_t :=
  to_action route0_r  := routestartfn 0 (reg_ (thisone));
  to_action route1_r := routecenterfn 1 (reg_ (thisone)) (reg_ (anotherone thisone));
  to_action route2_r := routecenterfn 2 (reg_ (anotherone thisone)) (reg_ (anotherone (anotherone thisone)));
  to_action route3_r := routeendfn 3 (reg_ (anotherone (anotherone thisone))).

  Definition schedule : scheduler :=
    route3_r |> route2_r |> route1_r |>  route0_r |> done.
(* Equations to_action (rl:rule_name_t) : uaction reg_t empty_ext_fn_t :=
  to_action (router_ thisone)  := routestartfn 0 (reg_ (thisone));
  to_action (router_ (anotherone thisone)) := routecenterfn 1 (reg_ (thisone)) (reg_ (anotherone thisone));
  to_action (router_ (anotherone (anotherone thisone))) := routecenterfn 2 (reg_ (anotherone thisone)) (reg_ (anotherone (anotherone thisone)));
  to_action (router_ (anotherone (anotherone (anotherone thisone)))) := routeendfn 3 (reg_ (anotherone (anotherone thisone))). *)

  (* Equations to_action (rl : rule_name_t) : uaction reg_t empty_ext_fn_t := 
  to_action (router_ idx) :=
    let idx_nat := index_to_nat idx in
    if Nat.eqb idx_nat 0 then
      routestartfn 0 (reg_ idx)
    else if Nat.eqb idx_nat regno then
      let idx' := index_of_nat (Nat.sub idx_nat - 1) in
      routeendfn regno (reg_ idx')
    else
      let idx' := index_of_nat (Nat.sub idx_nat - 1) in
      routecenterfn idx_nat (reg_ idx') (reg_ idx). *)
     


(* Definition to_action rl :=
match rl with
| router_ idx => let idx_nat := index_to_nat idx in
  if Nat.eqb idx_nat 0 then (routestartfn 0 (reg 0)) 
  else if Nat.eqb idx_nat regno then (routeendfn regno (reg (Nat.sub regno 1))) 
  else (routecenterfn idx_nat (reg (Nat.sub idx_nat 1)) (reg idx_nat))  
end. *)

Definition R ( reg : reg_t ) :=
  match reg with
  |  _ => bits_t (struct_sz basic_flit)
  end.
  
Definition r (reg : reg_t) : R reg :=
  match reg with
  |  _ => Bits.zero
  end.

  Definition rules :=
  tc_rules R empty_Sigma to_action.


  
  
  Ltac solve_eqdec_t :=
    repeat match goal with
    | |- context [EqDec.eq_dec ?x ?x] =>
      try rewrite eq_dec_refl || vm_compute (EqDec.eq_dec x x)
    | |- context [EqDec.eq_dec ?x ?y] =>
      vm_compute (EqDec.eq_dec x y)
    end.
  
  
  Ltac tc_action_dependent_t :=
    cbv zeta;
    unfold Koika.TypeInference.tc_action;
    repeat match goal with
    | _ => progress with_strategy opaque [ EqDec.eq_dec ] cbn
    | _ => progress solve_eqdec_t
    | |- context [type_action] => unfold type_action
    | |- context [cast_action] => unfold cast_action
    | |- context [cast_action'] => unfold cast_action'
    end;
    reflexivity.
  (* Compute
    tc_rules R empty_Sigma to_action. *)

    From Coq Require Import ssreflect ssrfun ssrbool.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(*
    Instance reg_t_eq_dec : EqDec reg_t. 
    Proof.
      exact (eq_dec eq_refl).
    := @EqDec_FiniteType _ _.
    Print Instances EqDec.
*)

Notation "` x" := (projT1 x) (at level 0).
Notation "`` x" := (projT2 x) (at level 0).

Check type_action.
 
Lemma ubind x e dummy_pos b R Sigma e' b':
     e' = type_action R Sigma dummy_pos (@List.nil (var_t * type)) e ->
     b' = type_action R Sigma dummy_pos ((x, `e') :: (@List.nil (var_t * type))) b ->
     type_action R Sigma dummy_pos (@List.nil (var_t * type)) (UBind x e b) = Bind x ``e' ``b'.
    Proof.
    Admitted.

    Lemma xxx :
    forall  Sigma rl,
    { x | TypeInference.tc_action R Sigma dummy_pos (@List.nil (var_t * type)) unit_t
    (desugar_action dummy_pos (to_action rl)) = Success x }.
    destruct rl.
    - intros.
      eexists.
      rewrite /to_action/routestartfn/_routestart_r.
      rewrite /desugar_action/desugar_action' -/desugar_action'.
      rewrite /TypeInference.tc_action.
      Check UBind. 
      remember (@UBind dummy_pos _ _ _ _ "m0" _ _).
      rewrite /type_action -/type_action. rewrite /=.
      rewrite /cast_action. rewrite /cast_action' -/cast_action'.
      rewrite /eq_dec.
      rewrite /=.
      reflexivity.
progress solve_eqdec_t.
(* progress with_strategy opaque [ EqDec.eq_dec ] cbn. *)
progress solve_eqdec_t.
unfold type_action.
unfold cast_action.
unfold cast_action'.
      unfold type_action.
      unfold cast_action at 1.
      unfold cast_action'.
      with_strategy opaque [ EqDec.eq_dec ] cbn.
      solve_eqdec_t.
      unfold cast_action at 1.
      unfold cast_action'.
      progress with_strategy opaque [ EqDec.eq_dec ] cbn.
      progress solve_eqdec_t.
      vm_compute.
      repeat match goal with
      | _ => progress with_strategy opaque [ EqDec.eq_dec ] cbn
      | _ => progress solve_eqdec_t
      | |- context [type_action] => unfold type_action
      | |- context [cast_action] => unfold cast_action
      | |- context [cast_action'] => unfold cast_action'
      end.

    Lemma xxx R tau sig rl x:
    Koika.TypeInference.tc_action 
      R 
      empty_Sigma 
      dummy_pos 
      tau 
      sig 
    (desugar_action dummy_pos (to_action rl)) = Success x.
  Proof.
    destruct rl.
    unfold to_action.
    unfold Koika.TypeInference.tc_action.
    -unfold type_action.
    vm_compute.
    Print e.
    cast_action. unfold cast_action'. unfold routestartfn. unfold _routestart_r.
    intros.
    repeat match goal with
    | _ => progress with_strategy opaque [ EqDec.eq_dec ] cbn
    | _ => progress solve_eqdec_t
    | |- context [type_action] => unfold type_action
    | |- context [cast_action] => unfold cast_action
    | |- context [cast_action'] => unfold cast_action'
    end.

  

    Check is_success.
    Lemma xxx R Sigma tau sig rl:
    is_success (desugar_and_tc_action
      R 
      Sigma 
      tau 
      sig 
     (to_action rl)) = true.
     Proof.
     destruct rl.
     unfold to_action.
     -  unfold Koika.TypeInference.tc_action. unfold is_success.
     cbv delta. unfold routetest. unfold _routetest.
intros. unfold type_action.  unfold cast_action. unfold cast_action'.
repeat match goal with
     | _ => progress with_strategy opaque [ EqDec.eq_dec ] cbn
     | _ => progress solve_eqdec_t
     | |- context [type_action] => unfold type_action
     | |- context [cast_action] => unfold cast_action
     | |- context [cast_action'] => unfold cast_action'
     end.
     solve_eqdec_t.
     apply is_success.
     reflexivity.

     

  (* Fixpoint schedule_gen (n:nat): scheduler:=
  match n with
  | 0 => done
  | S n' => (router n') |> (schedule_gen n')
  end.

  Definition schedule : scheduler := schedule_gen nocsize.
    (router 3) |> (router 2) |> (router 1) |>  (router 0) |> done.  *)


  Check Koika.TypeInference.tc_action.
  Check Koika.SyntaxFunctions.reposition.
  Check PThis.
  Check reposition.
  Context {var_t fn_name_t reg_t ext_fn_t: Type}.
(* Lemma mytry R Sigma x:
tc_rules R sigma to_action = x. *)
  (* Lemma m2 R Sigma sig tau rl x:
  Koika.TypeInference.tc_action 
  R 
  Sigma 
  dummy_pos 
  tau 
  sig 
 (desugar_action dummy_pos (reposition PThis (to_action rl))) 
   = Success x.
   Proof.
   destruct rl.
   unfold to_action.
   destruct n.
   - simpl. unfold desugar_action. unfold Koika.TypeInference.tc_action.
   unfold cast_action. unfold cast_action'. unfold reposition. *)


(* Check r.

  Lemma xxx R Sigma tau sig rl x:
    Koika.TypeInference.tc_action 
      R 
      Sigma 
      dummy_pos 
      tau 
      sig 
    (desugar_action dummy_pos (to_action rl)) = Success x.
  Proof.
    destruct rl.
    unfold to_action.
    unfold Koika.TypeInference.tc_action.
    (* destruct n. *)
    - unfold desugar_action.
    unfold cast_action. unfold cast_action'. unfold routestartfn. unfold _routestart_r.
    intros.
    repeat match goal with
    | _ => progress with_strategy opaque [ EqDec.eq_dec ] cbn
    | _ => progress solve_eqdec_t
    | |- context [type_action] => unfold type_action
    | |- context [cast_action] => unfold cast_action
    | |- context [cast_action'] => unfold cast_action'
    end.


 *)

 Ltac _arg_type R :=
  match type of R with
  | ?t -> _ => t
  end.

 Goal. 
 Proof.
  let rule_name_t := _arg_type uactions in
  let res := constr:(fun r: rule_name_t =>
                      ltac:(destruct r eqn:? ;
                            lazymatch goal with
                            | [ H: _ = ?rr |- _ ] =>
                              (* FIXME: why does the ‘<:’ above need this hnf? *)
                              let ua := constr:(uactions rr) in
                              let ua := (eval hnf in ua) in
                              _tc_action R Sigma (@List.nil (var_t * type)) constr:(unit_t) ua
                            end)) in
  exact res.

Notation tc_rules R Sigma actions :=
  (ltac:(_tc_rules R Sigma actions)) (only parsing).

Definition rules := 

(* End Design. Cant end functor instance?  *)

Module Proofs.
Import Design.

Definition r_r2l (reg : reg_t) : R reg :=
  match reg with
  | reg_ (thisone)  => Bits.zero
  | reg_ (anotherone thisone) => Bits.zero
  | reg_ (anotherone (anotherone thisone))  => Bits.of_nat 14 9729
  | _ => Bits.zero
  end.

Goal
run_schedule r_r2l rules empty_sigma schedule
(fun ctxt =>
let r' := (fun idx => 
match idx with
  | reg_ (thisone)  => ctxt[(reg 0)]
  | reg_ (anotherone thisone) => ctxt[(reg 1)]
  | reg_ (anotherone (anotherone thisone))  => ctxt[(reg 2)]
  | _ => Bits.zero
  end ) in

run_schedule r' rules empty_sigma schedule
(fun ctxt2 =>
let bits_r0 := ctxt2.[(reg 0)] in
Bits.to_nat bits_r0 = 8705)).
  Proof.
    check.
  Defined.


(*8289 = 1 0000 0011 00001*)
Definition r_l2r (reg : reg_t) : R reg :=
  match reg with
  |  r0 => Bits.of_nat 14 8289 
  |  r1 => Bits.zero
  |  r2 => Bits.zero
  | debug => Bits.zero
  end.

Goal
run_schedule r_l2r rules empty_sigma schedule
(fun ctxt =>
let r' := (fun idx => 
match idx with
  | r0=> ctxt.[r0]
  | r1=> ctxt.[r1]
  | r2=> ctxt.[r2]
  | debug => ctxt.[debug]
  end ) in

run_schedule r' rules empty_sigma schedule
(fun ctxt2 =>
let bits_r0 := ctxt2.[r2] in
Bits.to_nat bits_r0 = 9313)).
  Proof.
    check.
  Defined.

Lemma left_to_right: forall nocsize


End Proofs.