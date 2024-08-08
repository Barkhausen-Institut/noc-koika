(* Import necessary modules *)
Require Import MetaCoq.Template.All.
Require Import List.
Import ListNotations.
Open Scope string_scope.

From MetaCoq Require Import bytestring.
Import String.
Open Scope bs.


MetaCoq Run (
  tmMkInductive' (
    {|
      ind_name := "color";
      ind_type := tSort (Universe.make (Level.lSet)); (* Type *)
      ind_kelim := IntoPropSProp; (* Allowed sort levels for constructors *)
      ind_ctors := [
        ("Red", tInd {| inductive_mind := (MPfile ["MetaCoqRun"], "color"); inductive_ind := 0 |} [], 0);
        ("Blue", tInd {| inductive_mind := (MPfile ["MetaCoqRun"], "color"); inductive_ind := 0 |} [], 0)
      ];
      ind_projs := []
    |}
  )
).

