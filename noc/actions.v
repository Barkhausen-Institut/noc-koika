Require Import Koika.Frontend.
Require Import Koika.Std.
Require Import noc.Router_typed.
Require Import Koika.TypedParsing.
Require Import noc.Types.
Require Import noc.setup.
From Coq Require Import Arith Lia Program.
From Equations Require Import Equations.
Require Import Coq.Vectors.Fin.
Set Equations Transparent.


Module Actions
  (* (a : Config) *)
  (b : Typesize).

  (* Module s := Setup b. *)
  Module Routerfns := Router b.
  Import Routerfns Routerfns.NOC_setup.

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

  Equations to_action {x_dim'} (rl : rule_name_t (S x_dim')) {x_dim_max : nat} (H: S x_dim' <<= S x_dim_max)
    : action (tau:= unit_t) (R (x_dim:=x_dim_max)) (Sigma (x_dim:=x_dim_max)) := (* Q: why S x_dim_max (tau:= unit_t)*)

    (* case: single router *)
    to_action (rule 0 (@F1 ?(0))) le_n :=
      routestartfn
        0
        (router  0 F1 state)
        (router  0 F1 downstream)
        (ext_fun 0 F1 input)
        (ext_fun 0 F1 output);

    (* case: first router in the pipeline *)
    to_action (rule 0 (@F1 ?(0))) (x_dim_max:=n) H :=
      let f1 := widen_fin H (@F1 0) in
      routestartfn 0
        (router  n f1 state)
        (router  n f1 downstream)
        (ext_fun n f1 input)
        (ext_fun n f1 output);

    (* case : last router in the pipeline *)
    to_action (rule (S c) (@F1 ?(S c))) (x_dim_max:=n) le_n :=
      let f1  := @F1 (S c) in
      let f1' := FS (@F1 c) in (* upstream *)
      routeendfn (S c)
        (router  (S c) f1  state)
        (router  (S c) f1' downstream) (* upstream *)
        (ext_fun (S c) f1  input)
        (ext_fun (S c) f1  output);

    (* case: center routers in the pipeline
       (base case of the recursion)
     *)
    to_action (rule (S c) (@F1 ?(S c))) (x_dim_max:=n) (le_S n H) :=
      let f1  := widen_fin (le_S _ _ H) (@F1 (S c)) in
      let f1' := FS (widen_fin H (FS (@F1 c))) in (* upstream *)
      routecenterfn n
        (router  n f1  state)
        (router  n f1' downstream) (* upstream *)
        (router  n f1  downstream)
        (ext_fun n f1  input)
        (ext_fun n f1  output);

    (* recursion *)

    (* case: the fin space of the rule is smaller than the desired one *)
    to_action (rule (S c) (FS c')) (x_dim_max:=n) (@le_S ?(S c) n H) :=
      to_action (rule c c') (le_S _ n (le_t_inj H));

    (* case: the types of the fin space match up  *)
    to_action (rule (S c) (FS c')) (x_dim_max:=?(S c)) H :=
      to_action (rule c c') (le_t_inj H).

Equations schedule {x_dim'} {x_dim_max : nat} (H: S x_dim' <<= S x_dim_max)
  : Syntax.scheduler pos_t (rule_name_t (S x_dim_max)) :=

    (* rule 0 for max_dim 1 *)
    schedule (x_dim':= 0) (x_dim_max:= 0) (@le_n ?(S 0)) :=
      rule 0 (@F1 0) |> done;

    (* rule 0 for max_dim n *)
    schedule (x_dim':=0) (x_dim_max:=(S m)) (@le_S (S (S x)) ?(S m) h) :=
      rule (S m) (FS (widen_fin h (@F1 0))) |> done;

    (* absurd *)
    schedule (x_dim':=(S n)) (x_dim_max:=0) (le_S x h) := absurd_le_t h;

    schedule (x_dim':=(S n)) (x_dim_max:=(S n)) (@le_n ?(S n)) with
      (schedule (x_dim':=n) (x_dim_max:=(S n)) (le_S (S n) (S n) (@le_n (S n)))) => {
        schedule (x_dim':=(S n)) (x_dim_max:=(S n)) (@le_n ?(S n)) tl :=
          rule (S n) (@F1 (S n)) |> tl
      };

    schedule (x_dim':=(S n)) (x_dim_max:=(S m)) (@le_S ?(S m) h) with
      (schedule (x_dim':=n) (x_dim_max:=(S m)) (le_S (S n) (S m) (le_t_inj h))) => {
      schedule (x_dim':=(S n)) (x_dim_max:=(S m)) (@le_S ?(S m) h) tl :=
      rule (S m) (FS (widen_fin h (@F1 (S n)))) |> tl
      }.

End Actions.

Module FNoc
  (b: Typesize).

  Module d := Actions b.
  Import d d.Routerfns d.Routerfns.NOC_setup.

  Equations to_action (rl : rule_name_t (S b.nocsize)) : 
    action (tau:= unit_t) (R (x_dim:=b.nocsize)) (Sigma (x_dim:=b.nocsize)) :=
    to_action rl := @d.to_action b.nocsize rl b.nocsize (@le_n (S b.nocsize)).

  Equations schedule : Syntax.scheduler pos_t (rule_name_t (S b.nocsize)) :=
    schedule := @d.schedule b.nocsize b.nocsize (@le_n (S b.nocsize)).

End FNoc.
