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
  
  Equations fin_elems'' m : list (reg_t (S m)) :=
    fin_elems'' 0      := cons (router 0 F1 state) (cons (router 0 F1 downstream ) nil);
    fin_elems'' (S m') with fin_elems'' m' => {
      | tl := cons (router (S m') (@F1 (S m')) state)
                (cons (router (S m') (@F1 (S m')) downstream)
                   (lift tl))
        }.
  
  Lemma help: forall n m',
    List.nth_error (fin_elems'' m') n = Some (router m' F1 state) ->
    List.nth_error (lift (fin_elems'' m')) n = Some (router (S m') F1 state).
  Admitted.

    Lemma regt_error :
    forall n, forall (r: (reg_t (S n))),
      List.nth_error (fin_elems'' n) (fin_idx r) = Some r.
  Proof.
  intros n r.
  funelim (fin_elems'' n).
  - funelim (fin_idx r). simp fin_idx; simpl; try (reflexivity || depelim f).
  - funelim (fin_idx r); simp fin_idx; simpl; rewrite <- plus_n_O.
    + Search (_ + S _).
      rewrite <- plus_n_Sm.
      simpl.
      specialize (Hind (mk m' F1 A)).
      simp fin_idx in Hind.
      simpl in Hind.
      rewrite <- plus_n_O in Hind.

  

  Instance Fin_regt : forall n, FiniteType (reg_t (S n)) :=
  {
    finite_index := fin_idx;
    finite_elements := fin_elems;
    finite_surjective: forall a: T, List.nth_error finite_elements (finite_index a) = Some a;
    finite_injective: NoDup (List.map finite_index finite_elements)
  }

End Instances.
