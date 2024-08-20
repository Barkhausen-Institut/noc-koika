Require Import Koika.Frontend.
Require Import Koika.Std.
Require Import Koika.Testing.

Module Types.

Definition sz := 14.

Definition basic_flit :=
    {|
    struct_name := "basic_flit";
    struct_fields :=
      [
        ("new", bits_t 1);
        ("src" , bits_t 4);
        ("trg_y" , bits_t 2);
        ("trg_x" , bits_t 2);
        ("data" , bits_t 5)
      ]
    |}.
  
Definition router_address :=
    {|
    struct_name := "router_address";
    struct_fields :=
      [
        ("y" , bits_t 2);
        ("x" , bits_t 2)
      ]
    |}.


End Types.