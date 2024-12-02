Require Import Koika.Frontend.
Require Import Koika.Std.
Require Import Koika.TypedParsing.
Require Import noc.Types.
Require Import noc.helpers.
Require Import Coq.Vectors.Fin.

From Equations Require Import Equations.
Set Equations Transparent.


Module Setup.

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

Module Instances.

  Import Setup Helpers.
  Derive Signature for reg_t.
  Derive NoConfusion for reg_t.
  
  Equations lift_router {m} (r: reg_t m) : reg_t (S m) :=
    lift_router (router m f s) := router (S m) (FS f) s.
  
  Equations regt_elems {m} : list (reg_t (S m)) :=
    regt_elems (m:=0)      := cons (router 0 F1 state) (cons (router 0 F1 downstream) nil);
    regt_elems (m:=(S m')) with regt_elems => {
      | tl := cons (router (S m') (@F1 (S m')) state)
                (cons (router (S m') (@F1 (S m')) downstream)
                   (map lift_router tl))
        }.

  Equations regt_idx {n} (r: (reg_t (S n))) : nat :=
    regt_idx (router 0 (FS f) r)      := absurd_fin f;
    regt_idx (router m F1 state)      := 0;
    regt_idx (router m F1 downstream) := 1;
    regt_idx (router (S m) (FS f) r)  := S (S (regt_idx (router m f r))).

  Lemma regt_error {n} :
    forall (r: (reg_t (S n))),
      List.nth_error regt_elems (regt_idx r) = Some r.
  Proof.
    induction n; intros r; depelim r; depelim t; destruct r; simp regt_idx; simp regt_elems; simpl; try (reflexivity || depelim t).
    - specialize (IHn (router n F1 state)).
      fold (lift_router (router n F1 state)).
      apply map_nth_error.
      exact IHn.
    - specialize (IHn (router n (FS t) state)).
      fold (lift_router (router n (FS t) state)).
      apply map_nth_error.
      exact IHn.
    - specialize (IHn (router n F1 downstream)).
      fold (lift_router (router n F1 downstream)).
      apply map_nth_error.
      exact IHn.
    - specialize (IHn (router n (FS t) downstream)).
      fold (lift_router (router n (FS t)downstream)).
      apply map_nth_error.
      exact IHn.
  Qed.

  Lemma regt_injective {n} :
    NoDup (List.map (@regt_idx n) regt_elems).
  Proof.
    assert (is_seq : (List.map (@regt_idx n) regt_elems) = seq 0 ((S n)*2)).
    induction n; simp regt_elems; simp regt_idx; try reflexivity.
    - do 2 rewrite map_cons.
      rewrite map_map.
      erewrite map_ext.
      2:{
        intros a.
        depelim a; simp lift_router; simp regt_idx.
        instantiate (1:= fun x => S (S (regt_idx x))).
        cbn beta.
        exact eq_refl.
      }
      rewrite <- map_map.
      rewrite <- (map_map _ S regt_elems).
      rewrite IHn.
      cbn.
      repeat f_equal.
      repeat rewrite seq_shift.
      reflexivity.
    - rewrite is_seq. apply seq_NoDup.
  Qed.

  Instance Fin_regt {n} : FiniteType (reg_t (S n)) :=
    Build_FiniteType
      (reg_t (S n))
      regt_idx
      regt_elems
      regt_error
      regt_injective.

End Instances.
