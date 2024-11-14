Require Import Koika.Frontend.
Require Import Koika.Std.
Require Import Koika.Testing.
Require Import noc.Types.
Require Import Koika.TypedParsing.
From Equations Require Import Equations.

Module Router
  (MyTypes: Typesize).

  Module NOC_type := Types MyTypes.
  Import NOC_type.


  Section Funs.

    Context {reg_t : Type} {ext_fn_t : Type}.

    Check basic_flit.

    Definition R ( reg : reg_t ) :=
      match reg with
        |  _ => bits_t (struct_sz basic_flit)
      end.
    
    Definition Sigma (fn: ext_fn_t) : ExternalSignature :=
      match fn with
      | _ => {$ bits_t sz ~> bits_t sz $}
      end.
    
    Definition r_send (reg_name: reg_t) : function R Sigma :=
      <{ fun r_send (value: bits_t sz) : unit_t =>
           write0(reg_name, value)
      }>.

    Definition r_receive (reg_name: reg_t) : function R Sigma :=
      <{ fun r_receive () : bits_t sz =>
           read0(reg_name)
      }>.
      
    Definition _routestart_r
      (r_addr2: nat)
      (r0_send: function R Sigma (tau:=unit_t) (sig:=[("value", bits_t sz)]))  
      (r0_receive: function R Sigma (tau:=bits_t sz))
      (rtile_send: function R Sigma (tau:=unit_t) (sig:=[("value", bits_t sz)]))
      (Tile_In Tile_Out : ext_fn_t )
      : action R Sigma :=
      (Bind "r_addr" (Const (tau := bits_t addr_sz )(Bits.of_nat addr_sz r_addr2))
      ((Bind "zero" (Const (tau := bits_t sz )(Bits.of_nat sz 0)))
        <{
            let m_input := (extcall Tile_In(zero)) in
            let msg := unpack(struct_t basic_flit, m_input) in
            let new_data := get@basic_flit(msg, new) in
            let src_p := get@basic_flit(msg, src) in
            (( if (new_data && src_p == r_addr) then
                 r0_send(m_input)
               else
                 let m0 := r0_receive() in
                 (*router input policy will be added here*)
                 let msg := unpack(struct_t basic_flit, m0) in
                 let new_data := get@basic_flit(msg, new) in
                 let src_p := get@basic_flit(msg, src) in

                 (( if (src_p != r_addr && new_data) then
                      let dest := get@basic_flit(msg, dest) in
                      (* let src_x := get(unpack(struct_t router_address, r_addr), x) in
        let src_y := get(unpack(struct_t router_address, r_addr), y) in *)
                      (*r_addr[|2`d0| :+ 2] if not using struct*)
                      if dest > r_addr then
                        r0_send(pack(subst(msg, src, r_addr)))  (* The pack changes the source content in the package*)
                      else if dest < r_addr then
                             fail
                           else
                             rtile_send(extcall Tile_Out(m0))
                                       (* r0_send(pack(subst(msg, new, |1`d0|)))  *)
                                       (* To stop the packet from being processed again *)
                    else
                      pass ))
            ))
        }>)).
      
    Definition _routeend_r
      (r_addr2: nat)
      (r0_send: function R Sigma (tau:=unit_t) (sig:=[("value", bits_t sz)]))  
      (r0_receive: function R Sigma (tau:=bits_t sz))
      (rtile_send: function R Sigma (tau:=unit_t) (sig:=[("value", bits_t sz)]))
      (Tile_In Tile_Out : ext_fn_t)
      : action R Sigma :=
      (Bind "r_addr" (Const (tau := bits_t addr_sz )(Bits.of_nat addr_sz r_addr2))
        ((Bind "zero" (Const (tau := bits_t sz )(Bits.of_nat sz 0)))
        <{

            let m_input := (extcall Tile_In(zero)) in
            let msg := unpack(struct_t basic_flit, m_input) in
            let new_data := get@basic_flit(msg, new) in
            let src_p := get@basic_flit(msg, src) in
            (( if (new_data && src_p == r_addr) then
                 r0_send(m_input)
               else
                 let m0 := r0_receive() in (*router input policy will be added here*)
                 let msg := unpack(struct_t basic_flit, m0) in
                 let new_data := get@basic_flit(msg, new) in
                 let src_p := get@basic_flit(msg, src) in
                 (( if (src_p != r_addr && new_data) then 
                      let dest := get@basic_flit(msg, dest) in
                      (*r_addr[|2`d0| :+ 2] if not using struct*)
                      if dest > r_addr then
                        fail
                      else if dest < r_addr then
                             r0_send(pack(subst(msg, src, r_addr)))
                           else (*Pass to tile from this block*)
                             rtile_send(extcall Tile_Out(m0))
                                       (* r0_send(pack(subst(msg, new, |1`d0|))) *)
                    else
                      pass ))
            ))
        }>)).
        
    Definition _routecenter_r
      (r_addr2: nat)
      (r0_send: function R Sigma (tau:=unit_t) (sig:=[("value", bits_t sz)]))  
      (r1_send: function R Sigma (tau:=unit_t) (sig:=[("value", bits_t sz)]))  
      (r0_receive: function R Sigma (tau:=bits_t sz))
      (r1_receive: function R Sigma (tau:=bits_t sz))
      (rtile_send: function R Sigma (tau:=unit_t) (sig:=[("value", bits_t sz)]))
      (Tile_In Tile_Out : ext_fn_t)
      : action R Sigma  :=
      (Bind "r_addr" (Const (tau := bits_t addr_sz )(Bits.of_nat addr_sz r_addr2))
      ((Bind "zero" (Const (tau := bits_t sz )(Bits.of_nat sz 0)))
        <{
            let m_input := (extcall Tile_In(zero)) in
            let msg := unpack(struct_t basic_flit, m_input) in
            let new_data := get@basic_flit(msg, new) in
            let dest := get@basic_flit(msg,dest) in
            let src_p := get@basic_flit(msg, src) in
            if (new_data && src_p == r_addr && dest>r_addr) then
                 r1_send(m_input)
               else if (new_data && src_p == r_addr && dest<r_addr) then
                      r0_send(m_input)
                    else 
                      let m0 := r0_receive() in (*router input policy will be added here*)
                      let m1 := r1_receive() in 
                      let msg := unpack(struct_t basic_flit, m0) in
                      let new_data := get@basic_flit(msg, new) in
                      let src_p := get@basic_flit(msg, src) in
                       (if (src_p != r_addr && new_data) then
                           r0_send(pack(subst(msg, new, Ob~0)));
                           let dest := get@basic_flit(msg, dest) in
                           (*r_addr[|2`d0| :+ 2] if not using struct*)
                           if dest > r_addr then
                             r1_send(pack(subst(msg, src, r_addr)))
                           else if dest < r_addr then
                                  r0_send(pack(subst(msg, src, r_addr)))
                                else
                                  rtile_send(extcall Tile_Out(m0))
                                            (* r0_send(pack(subst(msg, new, |1`d0|)))  *)
                                            (* To stop the packet from being processed again*)
                    );
               let msg := unpack(struct_t basic_flit, m1) in
               let new_data := get@basic_flit(msg, new) in
               let src_p := get@basic_flit(msg, src) in
               ( if (src_p != r_addr && new_data) then
                    r1_send(pack(subst(msg, new, Ob~0)));
                    let dest := get@basic_flit(msg, dest) in
                    (*r_addr[|2`d0| :+ 2] if not using struct*)
                    if dest > r_addr then
                      r1_send(pack(subst(msg, src, r_addr)))
                    else if dest < r_addr then
                           r0_send(pack(subst(msg, src, r_addr)))
                         else
                           rtile_send(extcall Tile_Out(m1))
                                     (* r1_send(pack(subst(msg, new, |1`d0|)))  *)
                                     (* To stop the packet from being processed again*)
                                     );
            
        }>)).
        Next Obligation.


    Definition routestartfn (n:nat) (r1 r_ack: reg_t) (e1 e2: ext_fn_t): action R Sigma :=
      _routestart_r n (r_send r1) (r_receive r1) (r_send r_ack) e1 e2. 

    Definition routeendfn (n:nat) (r1 r_ack: reg_t) (e1 e2: ext_fn_t): action R Sigma :=
      _routeend_r n (r_send r1) (r_receive r1) (r_send r_ack) e1 e2.

    Definition routeendfn (n:nat) (r1 r_ack: reg_t) (e1 e2: ext_fn_t): action R Sigma :=
      _routeend_r n (r_send r1) (r_receive r1) (r_send r_ack) e1 e2.

  End Funs.

End Router.
