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
  
  Equations fin_idx {n} (r: (reg_t (S n))) : nat :=
    fin_idx (router _ (@F1 n')   state) := 2 * n';
    fin_idx (router _ (@FS n' _) state) := 2 * n';
    fin_idx (router _ (@F1 n')   downstream) := 2 * n' + 1;
    fin_idx (router _ (@FS n' _) downstream) := 2 * n' + 1.

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
    fin_elems' 0      0     _               := cons (router 0 F1 state) (cons (router 0 F1 downstream) nil);
    fin_elems' 0     (S 0) (le_S 0 ?(0) H') :=
      let f1 := FS (@F1 0) in
      cons (router (S 0) f1 state) (cons (router (S 0) f1 downstream) nil);

  fin_elems' 0     (S (S m')) H' :=
    let f1 := FS (widen_fin (widen_fin_left0 H') (@F1 0)) in
    cons (router (S (S m')) f1 state) (cons (router (S (S m')) f1 downstream) nil);

  fin_elems' (S n') (S m') H' with fin_elems' n' (S m') (le_t_inj H') :=
    | tl := let f1 := widen_fin (widen_le_t_S H') (@F1 (S n')) in
            cons (router (S m') f1 state)
              (cons (router (S m') f1 downstream) tl).   

  Definition fin_elems {n} : list (reg_t (S n)) :=
    fin_elems' n n (le_n n).

  Equations lift {m} (l: list (reg_t m)) : list (reg_t (S m)) :=
    lift nil := nil;
    lift (cons (router m f s) tl) with lift tl => {
        | tl' := cons (router (S m) (FS f) s) tl'
      }.

  Equations lift_router {m} (r: reg_t m) : reg_t (S m) :=
    lift_router (router m f s) := router (S m) (FS f) s.
  
  Equations fin_elems'' {m} : list (reg_t (S m)) :=
    fin_elems'' (m:=0)      := cons (router 0 F1 state) (cons (router 0 F1 downstream) nil);
    fin_elems'' (m:=(S m')) with fin_elems'' => {
      | tl := cons (router (S m') (@F1 (S m')) state)
                (cons (router (S m') (@F1 (S m')) downstream)
                   (map lift_router tl))
        }.

  Equations fin_idx'' {n} (idx:nat) (r: (reg_t (S n))) : nat :=
    fin_idx'' idx' (router 0 (FS f) r)      := absurd_fin f;
    fin_idx'' idx' (router (S m) (FS f) r)  := fin_idx'' (S idx') (router m f r);
    fin_idx'' idx' (router m F1 state)      := 2 * idx' + 1;
    fin_idx'' idx' (router m F1 downstream) := 2 * idx'.

  Definition fin_idx' {n} (r: (reg_t (S n))) : nat := fin_idx'' 0 r.

  Fixpoint finite_index_Fint {n} (f : Fin.t n) : nat :=
    match f with
    | Fin.F1 => 0
    | Fin.FS f' => S (finite_index_Fint f')
    end.

  Definition a := @F1 2.
  Definition b := FS a.

  Check a.
  Check b.
  Compute (finite_index_Fint a).
  Compute (finite_index_Fint b).

  Compute (fin_idx' (router 2 a state)).
  Compute (fin_idx' (router 2 a downstream)).
  Compute (fin_idx' (router 3 b state)).
  Compute (fin_idx' (router 3 b downstream)).

  Definition c := FS (FS (FS (@F1 1))).

  Compute (finite_index_Fint c).

  Fixpoint finite_elements_Fint {n} : list (Fin.t n) :=
    match n with
    | O => []
    | S _ => Fin.F1 :: map Fin.FS finite_elements_Fint
    end.

  Definition mod5 : list (Fin.t 5) := finite_elements_Fint.

  Compute mod5.
  Compute c.
  Compute (finite_index_Fint c).

  Definition router_mod5 := router 4 c state.
  Definition routers_mod5 : list (reg_t 5) := fin_elems''.

  Compute routers_mod5.

  Equations fint_idx {n} (r: (reg_t (S n))) : nat :=
    fint_idx (router 0 (FS f) r)              := absurd_fin f;
    fint_idx (router m F1 state)      := 0;
    fint_idx (router m F1 downstream) := 1;
    fint_idx (router (S m) (FS f) r) := S (S (fint_idx (router m f r))).

  Lemma regt_error {n} :
    forall (r: (reg_t (S n))),
      List.nth_error fin_elems'' (fint_idx r) = Some r.
  Proof.
    induction n; intros r; depelim r; depelim t; destruct r; simp fint_idx; simp fin_elems''; simpl; try (reflexivity || depelim t).
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
    NoDup (List.map (@fint_idx n) fin_elems'').
  Proof.
    assert (is_seq : (List.map (@fint_idx n) fin_elems'') = seq 0 ((S n)*2)).
    induction n; simp fin_elems''; simp fint_idx; try reflexivity.
    - do 2 rewrite map_cons.
      rewrite map_map.
      Check map_ext.
      erewrite map_ext.
      2:{
        clear IHn.
        intros a.
        depelim a. simp lift_router. simp fint_idx.
        instantiate (1:= fun x => S (S (fint_idx g))).

        exact eq_refl. reflexivity.
        funelim (lift_router n t r). depelim t.
        simp lift_router.
      }
      Search map.
      funelim (lift_router x).  rewrite <- map_map. unfold lift_router.
      rewrite IHn.
      unfold map. fold map.
      unfold map in IHn.
      rewrite IHn.

  Instance Fin_regt {n} : FiniteType (reg_t (S n)) :=
  {
    finite_index := fin_idx;
    finite_elements := fin_elems;
    finite_surjective: regt_eror;
    finite_injective: NoDup (List.map finite_index finite_elements)
  }

End Instances.
