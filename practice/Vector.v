Require Import Coq.Vectors.Vector.
Module VectorNotations := VectorNotations.
Import VectorNotations.

(* Open the scope for vector notations *)
(*Open Scope vector_scope.*)


Definition myVector'':= (cons _ 1 _ (cons _ 2 _ (nil _))).
Check myVector''.
Definition myVector: Vector.t nat 3 := [1;2;3]. 
Definition myVector':= [1;2;3].
Check myVector'.
Definition array2d := [[1]].
Check array2d.

Fixpoint vector_sum {n : nat} (v : t nat n) : nat :=
  match v with
  | nil _ => 0
  | cons _ h _ t => h + vector_sum t
  end.

Compute (vector_sum myVector').