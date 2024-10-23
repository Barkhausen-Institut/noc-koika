Require Import Koika.Frontend.
Require Import Koika.Std.

Module Type Typesize.
Parameter nocsize : nat.
Parameter data_sz : nat.
End Typesize.


Module Types (TS:Typesize).
Import TS.
Definition addr_sz := log2 nocsize.
Definition sz := Nat.add (Nat.add (Nat.mul 2 addr_sz) data_sz) 1.


Definition basic_flit :=
    {|
    struct_name := "basic_flit";
    struct_fields :=
      [
        ("new", bits_t 1);
        ("src" , bits_t addr_sz);
        ("dest" , bits_t addr_sz);
        ("data" , bits_t data_sz)
      ]
    |}.
  
Definition router_address :=
    {|
    struct_name := "router_address";
    struct_fields :=
      [
        ("raddr" , bits_t addr_sz)
      ]
    |}.


End Types.