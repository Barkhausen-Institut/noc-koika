From Coq Require Import Arith Lia Program.
From Equations Require Import Equations.
Require Import Coq.Vectors.Fin.
Set Equations Transparent.

Module Helpers.

Equations absurd_fin {T} (x:Fin.t 0) : T := .

Derive NoConfusion for nat.
Derive Signature NoConfusion for Fin.t.
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

Equations absurd_le_t {n:nat} {T} (H: (S n) <<= 0) : T := .

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

End Helpers.