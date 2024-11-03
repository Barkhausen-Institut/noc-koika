Require Import Koika.Frontend.
Require Import Koika.Std.
Require Import noc.Router.
Require Import noc.Types.
From Coq Require Import Arith Lia Program.
From Equations Require Import Equations.
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

Module Actions
  (* (a : Config) *)
  (b : Typesize).

  Module s := Setup b.
  Module Routerfns:= Router b.
  Import s s.c Routerfns.

  Equations absurd_fin {T} (x:Fin.t 0) : T := .

  Derive NoConfusion for nat.
  Derive NoConfusion for Fin.t.
  Derive Signature for le.

  (* Equations cannot recurse on [Prop]. *)
  Fail Derive NoConfusion for le.

  (* Set Equations Debug. *)

  Equations widen_fin {n n'} (H: n<=n') (x : Fin.t n) : Fin.t n' :=
    widen_fin (n:=0)   (n':=0)   _H          x := x;
    widen_fin (n:=S a) (n':=S a) (le_n a)    x := x;
    widen_fin (n:=0)   (n':=S a) _H  x := absurd_fin x; (* absurd *)
    widen_fin (n:=S a) (n':=0)   H           x := _; (* absurd *)
    widen_fin (n:=S a) (n':=S b) (le_S b H1) x with widen_fin H1 x => {
        widen_fin (n:=S a) (n':=S b) (le_S b H2) _x y := FS y
     }.
  Next Obligation. lia.
  Fail Qed.
  (* Use [Set Equations Debug] to see more.
     The problem is that Equations cannot recurse into [Prop] because
     then the function become undefinable/extractable.
   *)
  Abort.


  (* We recover from this situation by redefining [le] in [Type]. *)
  Reserved Notation "a <<= b" (at level 99).
  Inductive le_t (n : nat) : nat -> Type :=
    | le_n : n <<= n
    | le_S : forall m : nat, n <<= m -> n <<= S m
  where "a <<= b" := (le_t a b).

  Derive Signature NoConfusion for le_t.

  Equations widen_fin {n n'} (H: n<<=n') (x : Fin.t n) : Fin.t n' :=
    widen_fin (n:=0)   (n':=0)   _H          x := x;
    widen_fin (n:=S a) (n':=S a) (le_n a)    x := x;
    widen_fin (n:=0)   (n':=S a) _H  x := absurd_fin x; (* absurd *)
    widen_fin (n:=S a) (n':=0)   H           x := _; (* absurd *)
    widen_fin (n:=S a) (n':=S b) (le_S b H1) x with widen_fin H1 x => {
        widen_fin (n:=S a) (n':=S b) (le_S b H2) _x y := FS y
      }.
  Next Obligation. inversion H. Qed.

  (* A much nicer definition of [widen_fin] can be found here:
     https://github.com/mattam82/Coq-Equations/blob/ded4baada11f9434333e53d9eb3c21ded33e67ad/examples/Fin.v#L58
   *)

  (*
Inductive t : nat -> Set :=  F1 : forall n : nat, t (S n) | FS : forall n : nat, t n -> t (S n).
   *)

  Equations le_t_inj {n m} (H : S n <<= m) : n <<= m :=
    le_t_inj (n:=n')         le_n := le_S n' n' (le_n n');
    le_t_inj (n:=n') (m:=?(S (S m'))) (le_S (S m') H') with le_t_inj H' => {
        le_t_inj (n:=n') (m:=?(S (S m'))) (le_S (S m') H') H'' := le_S _ _ H''
      }.

  Equations to_action {x_dim'} (rl : rule_name_t (S x_dim')) {x_dim_max : nat} (H: S x_dim' <<= S x_dim_max)
    : uaction (reg_t (S x_dim_max)) (ext_fn_t (S x_dim_max)) :=

    (* case: single router *)
    to_action (rule 0 (@F1 ?(0))) le_n :=
      routestartfn 0
        (router  0 F1 state)
        (router  0 F1 downstream)
        (ext_fun 0 F1 input)
        (ext_fun 0 F1 output);

    (* case: first router in the pipeline *)
    to_action (rule 0 (@F1 ?(0))) (x_dim_max:=n) H :=
      let f1 := widen_fin H (@F1 0) in
      routestartfn 0
        (router  n f1 state)
        (router  n f1 downstream)
        (ext_fun n f1 input)
        (ext_fun n f1 output);

    (* case : last router in the pipeline *)
    to_action (rule (S c) (@F1 ?(S c))) (x_dim_max:=n) le_n :=
      let f1  := @F1 (S c) in
      let f1' := FS (@F1 c) in (* upstream *)
      routeendfn (S c)
        (router  (S c) f1  state)
        (router  (S c) f1' downstream) (* upstream *)
        (ext_fun (S c) f1  input)
        (ext_fun (S c) f1  output);

    (* case: center routers in the pipeline
       (base case of the recursion)
     *)
    to_action (rule (S c) (@F1 ?(S c))) (x_dim_max:=n) (le_S n H) :=
      let f1  := widen_fin (le_S _ _ H) (@F1 (S c)) in
      let f1' := FS (widen_fin H (FS (@F1 c))) in (* upstream *)
      routecenterfn n
        (router  n f1  state)
        (router  n f1' downstream) (* upstream *)
        (router  n f1  downstream)
        (ext_fun n f1  input)
        (ext_fun n f1  output);

    (* recursion *)

    (* case: the fin space of the rule is smaller than the desired one *)
    to_action (rule (S c) (FS c')) (x_dim_max:=n) (@le_S ?(S c) n H) :=
      to_action (rule c c') (le_S _ n (le_t_inj H));

    (* case: the types of the fin space match up  *)
    to_action (rule (S c) (FS c')) (x_dim_max:=?(S c)) H :=
      to_action (rule c c') (le_t_inj H).


End Actions.
