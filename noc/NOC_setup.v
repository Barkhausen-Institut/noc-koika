Require Import Koika.Frontend.
Require Import Koika.Std.
Require Import Koika.Testing.

Module Type NOC_data.
  Parameter nocsize: nat.
End NOC_data.

Module NOCSetup(ND:NOC_data).
Import ND. 
Import Types.
Definition regno := (Nat.sub nocsize 1).

Inductive reg_t := reg_ (n: Vect.index regno).
Inductive rule_name_t := router_ (n: Vect.index nocsize).


Definition routefail(r_addr2: nat) (r0: reg_t) 
: uaction reg_t empty_ext_fn_t :=
{{ fail }}.


End NOCSetup.


