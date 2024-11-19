Require Import Koika.Frontend.
Require Import Koika.Std.
Require Import Koika.TypedParsing.
Require Import noc.Types.
Require Import noc.helpers.
Require Import Coq.Vectors.Fin.

Module Setup
  (b : Typesize).

  Module c := Types b.
  Import c Helpers.

  (** Router state

      Every router owns an internal state register.
      For the pipeline every router owns the downstream transfer.
   *)
  Inductive router_reg_t : Type :=
  | state
  | downstream
  .

  (** The pipeline

      The pipeline is essentially a list of routers.
   *)
  Inductive reg_t : nat -> Type :=
  | router : forall x_dim, Fin.t (S x_dim) -> router_reg_t -> reg_t (S x_dim)
  .

  (** The router interface

      Every router can receive packets and emit packets from and
      to its attached component.
   *)
  Inductive ext_com_t : Type :=
  | input
  | output
  .

  (** The NOC interface

      Every router has an interface.
   *)
  Inductive ext_fn_t : nat -> Type :=
  | ext_fun : forall x_dim, Fin.t (S x_dim) -> ext_com_t -> ext_fn_t (S x_dim)
  .

  (** The Rules

      In our current design, every router is essentially
      a dedicated rule/action.
      Hence, the schedule is simple: all routers run in parallel.
   *)

  Inductive rule_name_t : nat -> Type :=
  | rule : forall x_dim, Fin.t (S x_dim) -> rule_name_t (S x_dim).


  Module Instances.

    Definition fin_idx n (r: (reg_t (S n))) : nat :=
      match r with
      | router _ n state      => 2 * proj1_sig (Fin.to_nat n)
      | router _ n downstream => 2 * proj1_sig (Fin.to_nat n) + 1
      end.

    Fixpoint fin_elems n : list (reg_t (S n)) :=
      match n with
      | 0 => cons (router 0 F1 state)
             cons (router 0 F1 downstream) 
             nil
      | S n => cons (router n (widen_fin (@F1 n)) state)
               cons (router n F1 downstream) 
               fin_elems n
      end. 



Instance Fin_regt : forall n, FiniteType (reg_t (S n)) :=
{ 
  finite_index := fin_idx;
  finite_elements := fin_elems;
  finite_surjective: forall a: T, List.nth_error finite_elements (finite_index a) = Some a;
  finite_injective: NoDup (List.map finite_index finite_elements) 
}

  End Instances.

End Setup.