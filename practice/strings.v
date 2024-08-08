Import String.


Definition x:= append "a" "b".
Print x.



Definition make_constructors (n : nat) : list (ident * term * nat) :=
  let fix aux i :=
      match i with
      | 0 => []
      | S i' => ("Ctor" ++ string_of_nat i, tProd nAnon (tInd {| inductive_mind := (MPfile ["MetaCoqRun"], "nat"); inductive_ind := 0 |} []) (tInd {| inductive_mind := (MPfile ["MetaCoqRun"], "user_defined_ind"); inductive_ind := 0 |} []), 1) :: aux i'
      end
  in aux n.