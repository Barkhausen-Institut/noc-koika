Require Import Koika.Frontend.
Require Import Koika.Std.
Require Import Koika.TypedParsing.
Require Import noc.Types.
Require Import Coq.Vectors.Fin.

Module Setup
  (b : Typesize).

  Module c := Types b.
  Import c.

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

End Setup.


