// -*- mode: verilog -*-
// Generated by cuttlec from a Kôika module
module NoC(input wire[0:0] CLK, input wire[0:0] RST_N, output wire[13:0] tile_out_arg, input wire[13:0] tile_in_out, input wire[13:0] tile_out_out, output wire[13:0] tile_in_arg);
	reg[13:0] r1 /* verilator public */ = 14'b0;
	reg[13:0] r2 /* verilator public */ = 14'b0;
	reg[13:0] r3 /* verilator public */ = 14'b0;

	assign tile_in_arg = 14'b0;
	wire[13:0] _0 = r1 ^ tile_in_out;
	wire[0:0] _cond0 = _0[9 +: 4] != 4'b0 && _0[13 +: 1];
	wire[1:0] _1 = _0[5 +: 2];
	wire[0:0] _cond1 = $unsigned(_1) > $unsigned(2'b0);
	wire[0:0] _cond2 = $unsigned(_1) < $unsigned(2'b0);
	assign tile_in_arg = 14'b0;
	wire[13:0] _mux_ccontext0 = r2 ^ tile_in_out;
	wire[0:0] _cond3 = _mux_ccontext0[9 +: 4] != 4'b0001 && _mux_ccontext0[13 +: 1];
	wire[1:0] _2 = _mux_ccontext0[5 +: 2];
	wire[0:0] _cond4 = $unsigned(_2) > $unsigned(2'b01);
	assign tile_in_arg = 14'b0;
	wire[13:0] _3 = r1 ^ tile_in_out;
	wire[0:0] _cond5 = _3[9 +: 4] != 4'b0001 && _3[13 +: 1];
	wire[1:0] _4 = _3[5 +: 2];
	wire[0:0] _cond6 = $unsigned(_4) > $unsigned(2'b01);
	wire[0:0] _if_canFire0 = _cond5 ? _cond6 : 1'b1;
	wire[0:0] _if_mux0 = _cond5 && _cond6;
	assign tile_in_arg = 14'b0;
	wire[13:0] _mux_ccontext1 = r3 ^ tile_in_out;
	wire[0:0] _cond7 = _mux_ccontext1[9 +: 4] != 4'b0010 && _mux_ccontext1[13 +: 1];
	wire[1:0] _5 = _mux_ccontext1[5 +: 2];
	wire[0:0] _cond8 = $unsigned(_5) > $unsigned(2'b10);
	assign tile_in_arg = 14'b0;
	wire[13:0] _6 = r2 ^ tile_in_out;
	wire[0:0] _cond9 = _6[9 +: 4] != 4'b0010 && _6[13 +: 1];
	wire[1:0] _7 = _6[5 +: 2];
	wire[0:0] _cond10 = $unsigned(_7) > $unsigned(2'b10);
	wire[0:0] _if_canFire1 = _cond9 ? _cond10 : 1'b1;
	wire[0:0] _if_mux1 = _cond9 && _cond10;
	assign tile_in_arg = 14'b0;
	wire[13:0] _8 = r3 ^ tile_in_out;
	wire[0:0] _cond11 = _8[9 +: 4] != 4'b0011 && _8[13 +: 1];
	wire[1:0] _9 = _8[5 +: 2];
	wire[0:0] _cond12 = $unsigned(_9) > $unsigned(2'b11);
	wire[0:0] _if_canFire2 = _cond11 ? ~_cond12 : 1'b1;
	wire[0:0] _router_4_out0 = _if_canFire2 && (_cond11 && ~_cond12);
	wire[0:0] _wF_router_30 = (_cond7 ? (_cond8 ? 1'b0 : (_if_canFire1 && ~_if_mux1) && ~_cond9) : _if_canFire1) && (~_router_4_out0 && (~(_cond7 || _if_mux1) || ~_router_4_out0));
	wire[0:0] _router_3_out0 = _wF_router_30 && (_cond7 && ~_cond8 || _cond9);
	wire[0:0] _wF_router_20 = (_cond3 ? (_cond4 ? 1'b0 : (_if_canFire0 && ~_if_mux0) && ~_cond5) : _if_canFire0) && (~_router_3_out0 && (~(_cond3 || _if_mux0) || ~_router_3_out0));
	wire[0:0] _router_2_out0 = _wF_router_20 && (_cond3 && ~_cond4 || _cond5);
	assign tile_out_arg = _mux_ccontext0;
	assign tile_out_arg = _3;
	wire[13:0] _router_2_out1 = _wF_router_20 ? (_cond3 && ~_cond4 ? ($unsigned(_2) < $unsigned(2'b01) ? {{_mux_ccontext0[13 +: 1], 4'b0001}, _mux_ccontext0[0 +: 9]} : tile_out_out) : (_cond5 ? (_cond6 ? {1'b0, _3[0 +: 13]} : ($unsigned(_4) < $unsigned(2'b01) ? {{_3[13 +: 1], 4'b0001}, _3[0 +: 9]} : tile_out_out)) : r1)) : r1;
	assign tile_out_arg = _0;
	assign tile_out_arg = _mux_ccontext1;
	assign tile_out_arg = _6;
	wire[13:0] _router_3_out1 = _wF_router_30 ? (_cond7 && ~_cond8 ? ($unsigned(_5) < $unsigned(2'b10) ? {{_mux_ccontext1[13 +: 1], 4'b0010}, _mux_ccontext1[0 +: 9]} : tile_out_out) : (_cond9 ? (_cond10 ? {1'b0, _6[0 +: 13]} : ($unsigned(_7) < $unsigned(2'b10) ? {{_6[13 +: 1], 4'b0010}, _6[0 +: 9]} : tile_out_out)) : r2)) : r2;
	assign tile_out_arg = _8;
	wire[13:0] _router_4_out1 = _if_canFire2 && (_cond11 && ~_cond12) ? ($unsigned(_9) < $unsigned(2'b11) ? {{_8[13 +: 1], 4'b0011}, _8[0 +: 9]} : tile_out_out) : r3;

	always @(posedge CLK) begin
		if (!RST_N) begin
			r1 <= 14'b0;
			r2 <= 14'b0;
			r3 <= 14'b0;
		end else begin
			r1 <= ((_cond0 ? _cond1 || ~_cond2 : 1'b1) && (~_router_2_out0 && (~(_cond0 && (_cond1 || ~_cond2)) || ~_router_2_out0))) && _cond0 ? (_cond1 ? {{_0[13 +: 1], 4'b0}, _0[0 +: 9]} : (_cond2 ? _router_2_out1 : tile_out_out)) : _router_2_out1;
			r2 <= _wF_router_20 ? (_cond3 ? (_cond4 ? {{_mux_ccontext0[13 +: 1], 4'b0001}, _mux_ccontext0[0 +: 9]} : {1'b0, _mux_ccontext0[0 +: 13]}) : (_cond5 && _cond6 ? {{_3[13 +: 1], 4'b0001}, _3[0 +: 9]} : _router_3_out1)) : _router_3_out1;
			r3 <= _wF_router_30 ? (_cond7 ? (_cond8 ? {{_mux_ccontext1[13 +: 1], 4'b0010}, _mux_ccontext1[0 +: 9]} : {1'b0, _mux_ccontext1[0 +: 13]}) : (_cond9 && _cond10 ? {{_6[13 +: 1], 4'b0010}, _6[0 +: 9]} : _router_4_out1)) : _router_4_out1;
		end
	end
endmodule
