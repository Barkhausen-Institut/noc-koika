Require Import Koika.Frontend.
Require Import Koika.Std.
Require Import noc.Types.


Module Interface.
Import Types.

Inductive reg_t:=
| r1.

Definition unwrap: UInternalFunction reg_t empty_ext_fn_t :=
    {{ fun unwrap (packet: struct_t basic_flit) : bits_t 5 =>
    let data := get(packet, data) in
    data
    }}.

Definition wrap : UInternalFunction reg_t empty_ext_fn_t :=
    {{ fun wrap (data: bits_t 5) (source: bits_t 4) (tx: bits_t 2)(ty: bits_t 2): struct_t basic_flit  =>
    let packet := struct basic_flit
            {
             new := Ob~1;
             src := source;
             trg_x := tx;
             trg_y := ty;
             data := data
            } in
    data
    }}.

Print UInternalFunction.
Print wrap.
Print uaction.
Check uaction.
End Interface.