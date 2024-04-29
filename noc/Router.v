Require Import Koika.Frontend.
Require Import Koika.Std.

(* Structure of standard flit *)
(* also used as burst header *)
(* HW-Doc.pdf page 8 *)
(* Definition standard_flit :=
{|
 struct_name := "standard_flit";
 struct_fields :=
   [
     (* if this flit starts burst - if it is a burst header *)
     ("burst"     , bits_t 1 );
     (* if this flit expects and acknowledgement *)
     ("arq"       , bits_t 1 );
     (* byte selector of payload *)
     (*
     header flit only: specifies the first [3:0] and last [7:4]
     valid byte of the data in the payload flits
     *)
     ("bsel"      , bits_t 8 );
     ("src_modid" , bits_t 8 ); //separate x,y,z
     ("src_chipid", bits_t 6 );
     ("trg_modid" , bits_t 8 );
     ("trg_chipid", bits_t 6 );
     (* read, write .. etc *)
     ("mode"      , bits_t 4 );
     (* destination address *)
     ("addr"      , bits_t 32);
     (* header flit only: number of upcomming payload flits *)
     ("data"      , bits_t 64)
   ]
|}. *)

Notation sz := 138.

Inductive reg_t :=
    | reg0.

Definition R reg :=
    match reg with
    | reg0 => bits_t sz
    end.


(* Definition route : UInternalFunction reg_t empty_ext_fn_t :=
{{
fun route (struct_t standard_flit) : struct_t standard_flit =>
    xm=standard_flit.trg_modid[0:2];
    ym=standard_flit.trg_modid[3:5];

    if xm<xr then
    \\external function?

    else if ym<yr then
    

    else
}}. *)









