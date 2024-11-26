Require Import Koika.Frontend.
Require Import Koika.Std.
Require Import Koika.TypedParsing.
Require Import noc.Types.
Require Import noc.helpers.
Require Import Coq.Vectors.Fin.

From Equations Require Import Equations.
(* Set Equations Transparent. *)

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

  Equations fin_idx {n} (r: (reg_t (S n))) : nat :=
    fin_idx (router _ n' state)      := 2 * proj1_sig (Fin.to_nat n');
    fin_idx (router _ n' downstream) := 2 * proj1_sig (Fin.to_nat n') + 1.

  (* TODO move rename to [widen_le_t] *)
  Equations widen_fin_left {m} (H: m <<= S (S m)) : S m <<= S (S m) :=
    widen_fin_left (m:=m') H' := le_S _ _ (le_n (S m')).

  Equations widen_fin_left0 {m} (H: 0 <<= S (S m)) : S 0 <<= S (S m) :=
    widen_fin_left0 (m:=0)    H' := widen_fin_left H';
    widen_fin_left0 (m:=S m') (le_S _ _ H') := le_S _ _ (widen_fin_left0 H').

  Equations widen_le_t_S {n m} (H: n <<= m) : S n <<= S m :=
    widen_le_t_S (n:=n') (m:=?(n')) (le_n ?(n')) :=  le_n (S n');
    widen_le_t_S (n:=n') (m:=?(S m'))  (le_S n' m' H') :=
     le_S _ _ (widen_le_t_S H').

  Equations fin_elems' n m (H: n <<= m) : list (reg_t (S m)) :=
    fin_elems' 0      0     _  :=
      [router 0 F1 state; router 0 F1 downstream];

    fin_elems' 0     (S 0) (le_S 0 ?(0) H') :=
      let f1 := FS (@F1 0) in
      [router (S 0) f1 state; router (S 0) f1 downstream];

    fin_elems' 0     (S (S m')) H' :=
      let f1 := FS (widen_fin (widen_fin_left0 H') (@F1 0)) in
      [router (S (S m')) f1 state; router (S (S m')) f1 downstream];

    fin_elems' (S n') (S m') H' with fin_elems' n' (S m') (le_t_inj H') :=
      | tl := let f1 := widen_fin (widen_le_t_S H') (@F1 (S n')) in
              cons (router (S m') f1 state)
                (cons (router (S m') f1 downstream) tl).


  Definition fin_elems {n} : list (reg_t (S n)) :=
    fin_elems' n n (le_n n).

  Lemma regt_error :
    forall n, forall a: (reg_t (S n)),
      List.nth_error fin_elems (fin_idx a) = Some a.
  Proof.
    intros n r.
    unfold fin_elems.
    funelim (fin_elems' n n (le_n n)).
    - simp fin_elems'.
      depelim r.
      depelim t; try inversion t.
      funelim (fin_idx (router 0 F1 r));
      rewrite <- Heqcall;
      depelim n'; simpl; inversion H; rewrite H1; reflexivity.
    - simp fin_elems'.
      cbv zeta.
      (* rewrite <- H0; rewrite <- H1; clear H0 H1. *)
      (* simp widen_le_t_S. *)
      depelim r.
      depelim t.
      + funelim (fin_idx (router (S n') F1 r));
        inversion H; clear H;
        simp fin_idx; simpl; reflexivity.
      + specialize (Hind (S n') (router (S n') (FS t) r)).
        simp le_t_inj in Hind.
        revert Hind.
        funelim (fin_idx (router (S n') (FS t) r)).
        * inversion H; clear H;
          simp fin_idx; simpl.

          rewrite Nat.add_0_r.
          assert (n'_eq_fs_t := inj_right_pair H1).
          (* rewrite <- n'_eq_fs_t. *)
          simpl.
          destruct (to_nat t).
          simpl proj1_sig.

          simpl.
          rewrite <- plus_n_Sm.
          simpl.
          simp fin_elems'.
          cbv zeta.
          simpl.
          simp widen_le_t_S.
          intro Hind.
          apply Hind.

          specialize (H eq_refl).
          apply H.
          specialize (H (S n'0) (router (S n'0) n' state)).
          simp le_t_inj in H.

          clear H2.
          apply H.
          rewrite n'_eq_fs_t in H.
          rewrite <- Heqcall in H.

  Instance Fin_regt : forall n, FiniteType (reg_t (S n)) :=
  {
    finite_index := fin_idx;
    finite_elements := fin_elems;
    finite_surjective: forall a: T, List.nth_error finite_elements (finite_index a) = Some a;
    finite_injective: NoDup (List.map finite_index finite_elements)
  }

End Instances.
