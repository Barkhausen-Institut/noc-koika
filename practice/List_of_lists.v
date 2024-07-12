Require Import List.
Import ListNotations.

(* A 2D array is a list of lists *)
Definition array2D (A : Type) := list (list A).

(* Create a 2D array of given dimensions filled with a default value *)
Fixpoint initialize_2d_array {A : Type} (rows cols : nat) (default : A) : array2D A :=
  match rows with
  | 0 => []
  | S r => (repeat default cols) :: (initialize_2d_array r cols default)
  end.

(* Get the nth element of a list *)
Definition nth_option {A : Type} (l : list A) (n : nat) : option A :=
  nth_error l n.

(* Get the element at (i, j) in a 2D array *)
Definition get_element {A : Type} (arr : array2D A) (i j : nat) : option A :=
  match nth_option arr i with
  | Some row => nth_option row j
  | None => None
  end.

(* Update the nth element of a list *)
Fixpoint update_nth {A : Type} (l : list A) (n : nat) (x : A) : list A :=
  match l, n with
  | [], _ => []
  | _::t, 0 => x :: t
  | h::t, S n' => h :: (update_nth t n' x)
  end.

(* Update the element at (i, j) in a 2D array *)
Definition update_element {A : Type} (arr : array2D A) (i j : nat) (x : A) : array2D A :=
  update_nth arr i
    (match nth_option arr i with
     | Some row => update_nth row j x
     | None => []
     end).

Example init_array : array2D nat := initialize_2d_array 3 4 0. 
Example get_elem : option nat := get_element init_array 1 2.
Compute get_element init_array 1 2.
Example updated_array : array2D nat := update_element init_array 1 2 5.
