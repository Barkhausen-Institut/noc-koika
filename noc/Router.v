Require Import Koika.Frontend.
Require Import Koika.Std.
Require Import Koika.Testing.
Require Import noc.Types.
Require Import Koika.TypedParsing.


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
    
    #[program] Definition r_send (reg_name: reg_t) : function R Sigma :=
      <{ fun r_send (value: bits_t sz) : unit_t =>
           write0(reg_name, value)
      }>.
    

    Definition r_receive (reg_name: reg_t) : function R Sigma :=
      <{ fun r_receive () : bits_t sz =>
           read0(reg_name)
      }>.

    Definition bz :=Bits.of_nat sz 0.
    Print UBind.

    Definition _routestart_r
      (r_addr2: nat)
      (r0_send r0_receive rtile_send: function R Sigma)
      (Tile_In Tile_Out : ext_fn_t)
      : action R Sigma :=
      UBind "r_addr" (USugar (UConstBits (Bits.of_nat addr_sz r_addr2)))
        <{
            let m_input := (extcall Tile_In(#bz)) in
            let msg := unpack(struct_t basic_flit, m_input) in
            let new_data := get(msg, new) in
            let src_p := get(msg, src) in
            (( if (new_data && src_p == r_addr) then
                 r0_send(m_input)
               else
                 let m0 := r0_receive() in
                 (*router input policy will be added here*)
                 let msg := unpack(struct_t basic_flit, m0) in
                 let new_data := get(msg, new) in
                 let src_p := get(msg, src) in

                 (( if (src_p != r_addr && new_data) then
                      let dest := get(msg, dest) in
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
        }>.

    Definition _routeend_r
      (r_addr2: nat)
      (r0_send r0_receive rtile_send: UInternalFunction reg_t ext_fn_t)
      (Tile_In Tile_Out : ext_fn_t)
      : uaction reg_t ext_fn_t :=
      UBind "r_addr" (USugar (UConstBits (Bits.of_nat addr_sz r_addr2)))
        (UBind "zero" (USugar (UConstBits (Bits.of_nat addr_sz r_addr2)))
        {{

            let m_input := (extcall Tile_In(#bz)) in
            let msg := unpack(struct_t basic_flit, m_input) in
            let new_data := get(msg, new) in
            let src_p := get(msg, src) in
            (( if (new_data && src_p == r_addr) then
                 r0_send(m_input)
               else
                 let m0 := r0_receive() in (*router input policy will be added here*)
                 let msg := unpack(struct_t basic_flit, m0) in
                 let new_data := get(msg, new) in
                 let src_p := get(msg, src) in
                 (( if (src_p != r_addr && new_data) then 
                      let dest := get(msg, dest) in
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
        }}).

    (* Router needs to decide which packet will go first then send the packet*)
    Definition _routecenter_r
      (r_addr2: nat)
      (r0_send r1_send r0_receive r1_receive rtile_send: UInternalFunction reg_t ext_fn_t)
      (Tile_In Tile_Out : ext_fn_t)
      : uaction reg_t ext_fn_t :=
      UBind "r_addr" (USugar (UConstBits (Bits.of_nat addr_sz r_addr2)))
        {{
            let m_input := (extcall Tile_In(#bz)) in
            let msg := unpack(struct_t basic_flit, m_input) in
            let new_data := get(msg, new) in
            let dest := get(msg,dest) in
            let src_p := get(msg, src) in
            (( if (new_data && src_p == r_addr && dest>r_addr) then
                 r1_send(m_input)
               else if (new_data && src_p == r_addr && dest<r_addr) then
                      r0_send(m_input)
                    else 
                      let m0 := r0_receive() in (*router input policy will be added here*)
                      let m1 := r1_receive() in 
                      let msg := unpack(struct_t basic_flit, m0) in
                      let new_data := get(msg, new) in
                      let src_p := get(msg, src) in
                      (( if (src_p != r_addr && new_data) then
                           r0_send(pack(subst(msg, new, Ob~0)));
                           let dest := get(msg, dest) in
                           (*r_addr[|2`d0| :+ 2] if not using struct*)
                           if dest > r_addr then
                             r1_send(pack(subst(msg, src, r_addr)))
                           else if dest < r_addr then
                                  r0_send(pack(subst(msg, src, r_addr)))
                                else
                                  rtile_send(extcall Tile_Out(m0))
                                            (* r0_send(pack(subst(msg, new, |1`d0|)))  *)
                                            (* To stop the packet from being processed again*)
                         else
                           pass ));
               let msg := unpack(struct_t basic_flit, m1) in
               let new_data := get(msg, new) in
               let src_p := get(msg, src) in
               (( if (src_p != r_addr && new_data) then
                    r1_send(pack(subst(msg, new, Ob~0)));
                    let dest := get(msg, dest) in
                    (*r_addr[|2`d0| :+ 2] if not using struct*)
                    if dest > r_addr then
                      r1_send(pack(subst(msg, src, r_addr)))
                    else if dest < r_addr then
                           r0_send(pack(subst(msg, src, r_addr)))
                         else
                           rtile_send(extcall Tile_Out(m1))
                                     (* r1_send(pack(subst(msg, new, |1`d0|)))  *)
                                     (* To stop the packet from being processed again*)
                  else
                    pass ))
            ))
        }}.



    Definition routecenterfn (n:nat) (r1 r2 r_ack: reg_t) (e1 e2: ext_fn_t): uaction reg_t ext_fn_t :=
      _routecenter_r n (r_send r1) (r_send r2) (r_receive r1) (r_receive r2) (r_send r_ack) e1 e2.

    Definition routestartfn (n:nat) (r1 r_ack: reg_t) (e1 e2: ext_fn_t): uaction reg_t ext_fn_t :=
      _routestart_r n (r_send r1) (r_receive r1) (r_send r_ack) e1 e2. 

    Definition routeendfn (n:nat) (r1 r_ack: reg_t) (e1 e2: ext_fn_t): uaction reg_t ext_fn_t :=
      _routeend_r n (r_send r1) (r_receive r1) (r_send r_ack) e1 e2.

  End Funs.

End Router.
