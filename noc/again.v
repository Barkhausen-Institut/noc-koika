From Equations Require Import Equations.

(* Extracted from lib *)
Inductive Fin : nat -> Set :=
| F1 : forall {n : nat}, Fin (S n)
| FS : forall {n : nat}, Fin n -> Fin (S n).

Fixpoint to_nat (m : nat) (n : Fin m) {struct n} : {i : nat | i < m} :=
  match n in (Fin n0) return {i : nat | i < n0} with
  | @F1 j => exist (fun i : nat => i < S j) 0 (PeanoNat.Nat.lt_0_succ j)
  | @FS n0 p =>
      let (i, P) := to_nat n0 p in exist (fun i0 : nat => i0 < S n0) (S i) (proj1 (PeanoNat.Nat.succ_lt_mono i n0) P)
  end.

Arguments to_nat {m}%nat_scope n.
(* End lib code *)


Derive Signature NoConfusion for Fin.
Equations absurd_fin {T} (x:Fin 0) : T := .

Reserved Notation "a <<= b" (at level 99).
Inductive le_t (n : nat) : nat -> Type :=
| le_n : n <<= n
| le_S : forall m : nat, n <<= m -> n <<= S m
where "a <<= b" := (le_t a b).

Derive Signature NoConfusion for le_t.

Equations absurd_le_t {n:nat} {T} (H: (S n) <<= 0) : T := .

Equations widen_fin {n n'} (H: n<<=n') (x : Fin n) : Fin n' :=
  widen_fin (n:=0)   (n':=0)   _H          x := x;
  widen_fin (n:=S a) (n':=S a) (le_n a)    x := x;
  widen_fin (n:=0)   (n':=S a) _H          x := absurd_fin x;
  widen_fin (n:=S a) (n':=0)   H           x := absurd_le_t H;
  widen_fin (n:=S a) (n':=S b) (le_S b H1) x with widen_fin H1 x => {
      widen_fin (n:=S a) (n':=S b) (le_S b H2) _x y := FS y
    }.

Equations le_t_inj {n m} (H : S n <<= m) : n <<= m :=
  le_t_inj (n:=n')         le_n := le_S n' n' (le_n n');
  le_t_inj (n:=n') (m:=?(S (S m'))) (le_S (S m') H') with le_t_inj H' => {
      le_t_inj (n:=n') (m:=?(S (S m'))) (le_S (S m') H') H'' := le_S _ _ H''
    }.


Inductive SomeType : Type := A | B.

Inductive SomeOtherType : nat -> Type :=
| mk : forall x, Fin (S x) -> SomeType -> SomeOtherType (S x).

Derive Signature for SomeOtherType.
Derive NoConfusion for SomeOtherType.

Equations fin_idx {n} (r: (SomeOtherType (S n))) : nat :=
  fin_idx (mk _ (@F1 n')   A) := 2 * n';
  fin_idx (mk _ (@FS n' _) A) := 2 * n';
  fin_idx (mk _ (@F1 n')   B) := 2 * n' + 1;
  fin_idx (mk _ (@FS n' _) B) := 2 * n' + 1.

Equations widen_fin_left {m} (H: m <<= S (S m)) : S m <<= S (S m) :=
  widen_fin_left (m:=m') H' := le_S _ _ (le_n (S m')).

Equations widen_fin_left0 {m} (H: 0 <<= S (S m)) : S 0 <<= S (S m) :=
  widen_fin_left0 (m:=0)    H'            := widen_fin_left H';
  widen_fin_left0 (m:=S m') (le_S _ _ H') := le_S _ _ (widen_fin_left0 H').

Equations widen_le_t_S {n m} (H: n <<= m) : S n <<= S m :=
  widen_le_t_S (n:=n') (m:=?(n'))   (le_n ?(n'))    := le_n (S n');
  widen_le_t_S (n:=n') (m:=?(S m')) (le_S n' m' H') := le_S _ _ (widen_le_t_S H').

Equations fin_elems' n m (H: n <<= m) : list (SomeOtherType (S m)) :=
  fin_elems' 0      0     _               := cons (mk 0 F1 A) (cons (mk 0 F1 B) nil);
  fin_elems' 0     (S 0) (le_S 0 ?(0) H') :=
    let f1 := FS (@F1 0) in
    cons (mk (S 0) f1 A) (cons (mk (S 0) f1 B) nil);

  fin_elems' 0     (S (S m')) H' :=
    let f1 := FS (widen_fin (widen_fin_left0 H') (@F1 0)) in
    cons (mk (S (S m')) f1 A) (cons (mk (S (S m')) f1 B) nil);

  fin_elems' (S n') (S m') H' with fin_elems' n' (S m') (le_t_inj H') :=
    | tl := let f1 := widen_fin (widen_le_t_S H') (@F1 (S n')) in
            cons (mk (S m') f1 A)
              (cons (mk (S m') f1 B) tl).

Check fin_elems'_elim.
Check FunctionalElimination_fin_elems'.
Print FunctionalInduction_fin_elems'.
Print fin_elems'_graph.
Check fin_elems'_clause_4.
Print fin_elems'_clause_4_graph.
Check fin_elems'_graph_correct.

Definition fin_elems {n} : list (SomeOtherType (S n)) :=
  fin_elems' n n (le_n n).

Equations lift {m} (l: list (SomeOtherType m)) : list (SomeOtherType (S m)) :=
  lift nil := nil;
  lift (cons (mk m f s) tl) with lift tl => {
      | tl' := cons (mk (S m) (FS f) s) tl'
    }.

Equations fin_elems'' m : list (SomeOtherType (S m)) :=
  fin_elems'' 0      := cons (mk 0 F1 A) (cons (mk 0 F1 B) nil);
  fin_elems'' (S m') with fin_elems'' m' => {
    | tl := cons (mk (S m') (@F1 (S m')) A)
              (cons (mk (S m') (@F1 (S m')) B)
                 (lift tl))
      }.

Lemma help: forall n m',
  List.nth_error (fin_elems'' m') n = Some (mk m' F1 A) ->
  List.nth_error (lift (fin_elems'' m')) n = Some (mk (S m') F1 A).


Lemma regt_error :
  forall n, forall (r: (SomeOtherType (S n))),
    List.nth_error (fin_elems'' n) (fin_idx r) = Some r.
Proof.
  intros n r.
  funelim (fin_elems'' n).
  - funelim (fin_idx r); simp fin_idx; simpl; try (reflexivity || depelim f).
  - funelim (fin_idx r); simp fin_idx; simpl; rewrite <- plus_n_O.
    + Search (_ + S _).
      rewrite <- plus_n_Sm.
      simpl.
      specialize (Hind (mk m' F1 A)).
      simp fin_idx in Hind.
      simpl in Hind.
      rewrite <- plus_n_O in Hind.

Lemma regt_error :
  forall n m H, forall (r: (SomeOtherType (S m))),
    List.nth_error (fin_elems' n m H) (fin_idx r) = Some r.
Proof.
  intros m.
  induction m.
  - intros m H r.
    depelim m.
    + simp fin_elems'.
      funelim (fin_idx r); simp fin_idx; simpl; try (reflexivity || inversion f).
    + (* FIXME At this point our mistake is obvious:
               We assume that the list build from the top to the bottom,
               while statement assumes a construction from the bottom to the top.
       *)

      funelim (fin_elems' 0 (S m) H).
      * simpl. simp fin_elems'. cbv zeta.
        depelim r.
        depelim f.
        ** destruct s.
           *** simp fin_idx.
               simpl.


      
  funelim (fin_idx r).
    + induction n0.
      * simp fin_elems'.
        simp fin_idx.
        simpl.
        exact eq_refl.
      * simp fin_elems'.
        simp fin_idx.
        cbv zeta.


  funelim (fin_elems' n m H).
  - simp fin_elems'.
    funelim (fin_idx r).
    + simp fin_idx. auto.
    + simp fin_idx. auto.
    + depelim f.
    + depelim f.
  - simp fin_elems'. cbv zeta.
    (* FIXME The whole case is two levels deep but we are generating only a single level.  *)
    depelim r.
    depelim f.
    + funelim (fin_idx (mk 1 F1 s)).
    + depelim f.
      * funelim (fin_idx _).
        ** rewrite <- Heqcall; simpl.
      * depelim f.
    funelim (fin_idx r).
    + simp fin_idx. simpl.
      depelim n'.
  - admit.
  - admit.
  - admit.

    - simp fin_elems'.
      depelim r.
      depelim f; try inversion t.
      funelim (fin_idx (mk 0 F1 s));
      rewrite <- Heqcall;
      depelim n'; simpl; inversion H; rewrite H1; reflexivity.
      inversion f.
    - simp fin_elems'.
      cbv zeta.
      depelim r.
      depelim f.
      + funelim (fin_idx (mk (S n') F1 s));
        inversion H; clear H;
        simp fin_idx; simpl; reflexivity.
      + specialize (Hind (S n') (mk (S n') (FS f) s)).
        simp le_t_inj in Hind.
        revert Hind.
        funelim (fin_idx (mk (S n') (FS f) s)).
        * inversion H; clear H;
          simp fin_idx; simpl.

          Search (_ + 0).
          rewrite <- plus_n_O.
          assert (n'_eq_fs_t := inj_right_pair H1).
          (* rewrite <- n'_eq_fs_t. *)
          simpl.
          destruct (to_nat f).
          simpl proj1_sig.

          simpl.
          rewrite <- plus_n_Sm.
          simpl.
          simp fin_elems'.
          cbv zeta.
          simpl.
          simp widen_le_t_S.
          intro Hind.
          Fail apply Hind.
(*
  Hind : forall
           eqargs : {| pr1 := n'0; pr2 := {| pr1 := S n'0; pr2 := le_S n'0 n'0 (le_n n'0) |} |} =
                    {| pr1 := S n'0; pr2 := {| pr1 := S n'0; pr2 := le_n (S n'0) |} |},
         eq_rect {| pr1 := n'0; pr2 := {| pr1 := S n'0; pr2 := le_S n'0 n'0 (le_n n'0) |} |}
           (fun projs : sigma (fun n : nat => sigma (fun m : nat => n <<= m)) =>
            list (SomeOtherType (S (pr1 (pr2 projs)))))
           (fin_elems' n'0 (S n'0) (le_S n'0 n'0 (le_n n'0)))
           {| pr1 := S n'0; pr2 := {| pr1 := S n'0; pr2 := le_n (S n'0) |} |} eqargs =
         (mk (S n'0) (widen_fin (le_n (S (S n'0))) F1) A
          :: mk (S n'0) (widen_fin (le_n (S (S n'0))) F1) B
             :: fin_elems' n'0 (S n'0) (le_t_inj (le_n (S n'0))))%list ->
         List.nth_error (fin_elems' n'0 (S n'0) (le_t_inj (le_n (S n'0)))) (x + x) =
         Some (mk (S n'0) (FS f) A)
  ============================
  List.nth_error (fin_elems' n'0 (S n'0) (le_t_inj (le_n (S n'0)))) (x + x) =
  Some (mk (S n'0) (FS f) A)
 *)


  intros n a.
  unfold fin_elems.
  generalize (le_n n); intro l.
  funelim (fin_elems' n n l).
  - admit.
  - simpl.
    specialize (Hind (S n') a H').
    simpl in Hind.

    (*
  n' : nat
  Hind : forall (n : nat) (a : SomeOtherType (S n))
           (eqargs : {| pr1 := n'; pr2 := {| pr1 := S n'; pr2 := le_t_inj (le_n (S n')) |} |} =
                     {| pr1 := n; pr2 := {| pr1 := n; pr2 := le_n n |} |}),
         eq_rect {| pr1 := n'; pr2 := {| pr1 := S n'; pr2 := le_t_inj (le_n (S n')) |} |}
           (fun projs : sigma (fun n0 : nat => sigma (fun m : nat => n0 <<= m)) =>
            list (SomeOtherType (S (pr1 (pr2 projs))))) (fin_elems' n' (S n') (le_t_inj (le_n (S n'))))
           {| pr1 := n; pr2 := {| pr1 := n; pr2 := le_n n |} |} eqargs = fin_elems' n n (le_n n) ->
         List.nth_error (fin_elems' n n (le_n n)) (fin_idx a) = Some a
  a : SomeOtherType (S (S n'))
  ============================
     *)


Lemma regt_error :
  forall n, forall a: (SomeOtherType (S n)),
    List.nth_error fin_elems (fin_idx a) = Some a.
P
