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
  Derive Signature for ext_fn_t.
  Derive NoConfusion for ext_fn_t.
  Derive Signature for rule_name_t.
  Derive NoConfusion for rule_name_t.
  
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

  Equations lift_ext {m} (r: ext_fn_t m) : ext_fn_t (S m) :=
    lift_ext (ext_fun m f s) := ext_fun (S m) (FS f) s.

  Equations ext_elems {m} : list (ext_fn_t (S m)) :=
    ext_elems (m:=0)      := cons (ext_fun 0 F1 input) (cons (ext_fun 0 F1 output) nil);
    ext_elems (m:=(S m')) with ext_elems => {
      | tl := cons (ext_fun (S m') (@F1 (S m')) input)
                (cons (ext_fun (S m') (@F1 (S m')) output)
                   (map lift_ext tl))
        }.

    Equations ext_idx {n} (r: (ext_fn_t (S n))) : nat :=
    ext_idx (ext_fun 0 (FS f) r)      := absurd_fin f;
    ext_idx (ext_fun m F1 input)      := 0;
    ext_idx (ext_fun m F1 output) := 1;
    ext_idx (ext_fun (S m) (FS f) r)  := S (S (ext_idx (ext_fun m f r))).

  Lemma ext_error {n} :
    forall (r: (ext_fn_t (S n))),
    List.nth_error ext_elems (ext_idx r) = Some r.
  Proof.
    induction n;
     intros r; depelim r; depelim t; destruct e; simp ext_idx; simp ext_elems; simpl; try (reflexivity || depelim t).
    - specialize (IHn (ext_fun n F1 input)).
      fold (lift_ext (ext_fun n F1 input)).
      apply map_nth_error.
      exact IHn.
    - specialize (IHn (ext_fun n (FS t) input)).
      fold (lift_ext (ext_fun n (FS t) input)).
      apply map_nth_error.
      exact IHn.
    - specialize (IHn (ext_fun n F1 output)).
      fold (lift_ext (ext_fun n F1 output)).
      apply map_nth_error.
      exact IHn.
    - specialize (IHn (ext_fun n (FS t) output)).
      fold (lift_ext (ext_fun n (FS t)output)).
      apply map_nth_error.
      exact IHn.
  Qed. 

  Lemma ext_injective {n} :
    NoDup (List.map (@ext_idx n) ext_elems).
  Proof.
    assert (is_seq : (List.map (@ext_idx n) ext_elems) = seq 0 ((S n)*2)).
    induction n; simp ext_elems; simp ext_idx; try reflexivity.
    - do 2 rewrite map_cons.
      rewrite map_map.
      erewrite map_ext.
      2:{
        intros a.
        depelim a; simp lift_router; simp ext_idx.
        instantiate (1:= fun x => S (S (ext_idx x))).
        cbn beta.
        exact eq_refl.
      }
      rewrite <- map_map.
      rewrite <- (map_map _ S ext_elems).
      rewrite IHn.
      cbn.
      repeat f_equal.
      repeat rewrite seq_shift.
      reflexivity.
    - rewrite is_seq. apply seq_NoDup.
    Qed.

  Instance Fin_ext {n} : FiniteType (ext_fn_t (S n)) :=
    Build_FiniteType
      (ext_fn_t (S n))
      ext_idx
      ext_elems
      ext_error
      ext_injective.

  Equations lift_rule {m} (r: rule_name_t m) : rule_name_t (S m) :=
    lift_rule (rule m f) := rule (S m) (FS f).
  
  Equations rule_elems {m} : list (rule_name_t (S m)) :=
    rule_elems (m:=0)      := cons (rule 0 F1) nil;
    rule_elems (m:=(S m')) with rule_elems => {
      | tl := cons (rule (S m') (@F1 (S m'))) (map lift_rule tl)
        }.

  Equations rule_idx {n} (r: (rule_name_t (S n))) : nat :=
    rule_idx (rule 0 (FS f))      := absurd_fin f;
    rule_idx (rule m F1)      := 0;
    rule_idx (rule (S m) (FS f))  := (S (rule_idx (rule m f))).

  Lemma rule_injective {n} :
    NoDup (List.map (@rule_idx n) rule_elems).
  Proof.
    assert (is_seq : (List.map (@rule_idx n) rule_elems) = seq 0 (S n)).
    induction n; simp rule_elems; simp rule_idx; try reflexivity.
    - rewrite map_cons.
      rewrite map_map.
      erewrite map_ext.
      2:{
        intros a.
        depelim a; simp lift_rule; simp rule_idx.
        instantiate (1:= fun x => S (rule_idx x)).
        cbn beta.
        exact eq_refl.
      }
      rewrite <- map_map.
      (* rewrite <- (map_map _ S rule_elems). *)
      rewrite IHn. 
      cbn.
      repeat f_equal.
      repeat rewrite seq_shift.
      reflexivity.
    - rewrite is_seq. apply seq_NoDup.
    Qed.

  Lemma rule_error {n} :
    forall (r: (rule_name_t (S n))),
    List.nth_error rule_elems (rule_idx r) = Some r.
  Proof.
    induction n; intros r; depelim r; depelim t; simp rule_idx; simp rule_elems; simpl; try (reflexivity || depelim t).
    - specialize (IHn (rule n F1)).
      fold (lift_rule (rule n F1)).
      apply map_nth_error.
      exact IHn.
    - specialize (IHn (rule n (FS t))).
      fold (lift_rule (rule n (FS t))).
      apply map_nth_error.
      exact IHn.
    Qed.

  Instance Fin_rule {n} : FiniteType (rule_name_t (S n)) :=
    Build_FiniteType
      (rule_name_t (S n))
      rule_idx
      rule_elems
      rule_error
      rule_injective.


End Instances.
