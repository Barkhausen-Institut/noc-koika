From Equations Require Import Equations.
    Module Type Number.
   Parameter x: nat.
   Axiom xprop: 1<x.
 End Number.
 
 Module Setup(ND:Number).
   Import ND. 
 
   Notation "!" := (False_rect _ _).
   Check le_n.

     Equations? foo (x : nat) (H: 1<x) (y : nat) : nat :=
      foo 0 H2 _ := !;
      foo 1 (le_S x H1) _ with H1 := {} ; 
      foo x' H y' := _.
    Proof.
    - 
    - 
    Admit Obligations.
    
 
  Equations foo (y : nat) : nat :=
     foo y with xprop :=
     foo y (le_S ?(0) H) := {!};
     foo y (le_S ?(1) (le_S ?(0) H)) := {!}; 
     foo y _ := x + y.
 
 End Setup.