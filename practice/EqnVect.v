From Coq Require Import Arith Lia Program.
From Equations Require Import Equations.

Inductive index' {A} := thisone | anotherone (a: A).
Arguments index': clear implicits.

Equations index (n:nat) : Type :=
    index 0 := False;
    index (S n) := index' (index n).
    

Check False. 
Compute index' False.

Inductive rule_t := router_ (n:index 4).

Compute router_ (thisone).



