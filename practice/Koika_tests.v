Require Import Koika.Frontend.
Require Import Koika.Std.


Module KoikaTests.

Parameter regno:nat.


Inductive reg_t := reg_ (n: Vect.index regno).
 Definition reg0:= reg_ thisone.

Inductive reg_t2 (regno: nat) : Type :=
  | reg_2 : Vect.index regno -> reg_t2 regno.

  Definition reg0 (regno: nat) (H: 1 <= regno) : reg_t2 regno.
  Proof.
    destruct regno as [| regno0].
    - (* Case regno = 0: This is impossible since 1 <= 0 is false *)
      exfalso. inversion H.
    - (* Case regno = S regno0: regno is positive, so we can use Fin.F1 *)
      exact (reg_2 (S regno0) thisone).
  Defined.

  Check reg0.

Inductive vec (A : Type) : nat -> Type :=
  | vnil : vec A 0
  | vcons : A -> forall n, vec A n -> vec A (S n).

(* Function to create a register at a given index n, assuming n < regno *)
Fixpoint reg_n (regno: nat) (n: nat) : option (reg_t2 regno) :=
  match regno, n with
  | S _, 0 => Some (reg_2 regno thisone) (* Index 0 *)
  | S regno', S n' => 
      match reg_n regno' n' with
      | Some (reg_2 _ fin) => Some (reg_2 regno (anotherone fin)) (* Index n+1 *)
      | None => None
      end
  | _, _ => None (* No valid index if regno = 0 or n >= regno *)
  end.
