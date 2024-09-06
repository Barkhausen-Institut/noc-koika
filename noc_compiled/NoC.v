// -*- mode: verilog -*-
// Generated by cuttlec from a Kôika module
module NoC(input wire[0:0] CLK, input wire[0:0] RST_N, input wire[13:0] tile_intf_out, output wire[13:0] tile_intf_arg);
	reg[13:0] r1 /* verilator public */ = 14'b0;
	reg[13:0] r2 /* verilator public */ = 14'b0;
	reg[13:0] r3 /* verilator public */ = 14'b0;

	assign tile_intf_arg = 14'b0;
	wire[13:0] _var_m00 = r1 ^ tile_intf_out;
	wire[0:0] _cond0 = _var_m00[9 +: 4] != 4'b0 && _var_m00[13 +: 1];
	wire[1:0] _0 = _var_m00[5 +: 2];
	wire[0:0] _cond1 = $unsigned(_0) > $unsigned(2'b0);
	assign tile_intf_arg = 14'b0;
	wire[13:0] _mux_ccontext0 = r2 ^ tile_intf_out;
	wire[0:0] _cond2 = _mux_ccontext0[9 +: 4] != 4'b0001 && _mux_ccontext0[13 +: 1];
	wire[1:0] _1 = _mux_ccontext0[5 +: 2];
	wire[0:0] _cond3 = $unsigned(_1) > $unsigned(2'b01);
	wire[0:0] _cond4 = $unsigned(_1) < $unsigned(2'b01);
	assign tile_intf_arg = 14'b0;
	wire[13:0] _var_m01 = r1 ^ tile_intf_out;
	wire[0:0] _cond5 = _var_m01[9 +: 4] != 4'b0001 && _var_m01[13 +: 1];
	wire[1:0] _2 = _var_m01[5 +: 2];
	wire[0:0] _cond6 = $unsigned(_2) > $unsigned(2'b01);
	wire[0:0] _cond7 = $unsigned(_2) < $unsigned(2'b01);
	wire[0:0] _if_canFire0 = _cond5 ? _cond6 || ~_cond7 : 1'b1;
	wire[0:0] _if_mux0 = _cond5 && _cond6;
	wire[0:0] _write0_canFire0 = _if_canFire0 && ~_if_mux0;
	assign tile_intf_arg = 14'b0;
	wire[13:0] _mux_ccontext1 = r3 ^ tile_intf_out;
	wire[0:0] _cond8 = _mux_ccontext1[9 +: 4] != 4'b0010 && _mux_ccontext1[13 +: 1];
	wire[1:0] _3 = _mux_ccontext1[5 +: 2];
	wire[0:0] _cond9 = $unsigned(_3) > $unsigned(2'b10);
	wire[0:0] _cond10 = $unsigned(_3) < $unsigned(2'b10);
	assign tile_intf_arg = 14'b0;
	wire[13:0] _var_m02 = r2 ^ tile_intf_out;
	wire[0:0] _cond11 = _var_m02[9 +: 4] != 4'b0010 && _var_m02[13 +: 1];
	wire[1:0] _4 = _var_m02[5 +: 2];
	wire[0:0] _cond12 = $unsigned(_4) > $unsigned(2'b10);
	wire[0:0] _cond13 = $unsigned(_4) < $unsigned(2'b10);
	wire[0:0] _if_canFire1 = _cond11 ? _cond12 || ~_cond13 : 1'b1;
	wire[0:0] _if_mux1 = _cond11 && _cond12;
	wire[0:0] _write0_canFire1 = _if_canFire1 && ~_if_mux1;
	assign tile_intf_arg = 14'b0;
	wire[13:0] _var_m03 = r3 ^ tile_intf_out;
	wire[0:0] _cond14 = _var_m03[9 +: 4] != 4'b0011 && _var_m03[13 +: 1];
	wire[1:0] _5 = _var_m03[5 +: 2];
	wire[0:0] _cond15 = $unsigned(_5) > $unsigned(2'b11);
	wire[0:0] _if_canFire2 = _cond14 ? ~_cond15 : 1'b1;
	wire[0:0] _cond16 = $unsigned(_5) < $unsigned(2'b11);
	wire[0:0] _router_4_out0 = _if_canFire2 && (_cond14 && (_cond15 ? 1'b0 : _cond16));
	wire[0:0] _wF_router_30 = (_cond8 ? (_cond9 ? 1'b0 : (_cond10 ? _write0_canFire1 && ~_cond11 : _write0_canFire1)) : _if_canFire1) && (~_router_4_out0 && (~(_cond8 || _if_mux1) || ~_router_4_out0));
	wire[0:0] _router_3_out0 = _wF_router_30 && (_cond8 && ~_cond9 ? _cond10 || _cond11 : _cond11);
	wire[0:0] _wF_router_20 = (_cond2 ? (_cond3 ? 1'b0 : (_cond4 ? _write0_canFire0 && ~_cond5 : _write0_canFire0)) : _if_canFire0) && (~_router_3_out0 && (~(_cond2 || _if_mux0) || ~_router_3_out0));
	wire[0:0] _router_2_out0 = _wF_router_20 && (_cond2 && ~_cond3 ? _cond4 || _cond5 : _cond5);
	assign tile_intf_arg = 14'b0;
	assign tile_intf_arg = 14'b0;
	assign tile_intf_arg = 14'b0;
	assign tile_intf_arg = 14'b0;
	assign tile_intf_arg = 14'b0;
	assign tile_intf_arg = 14'b0;
	assign tile_intf_arg = 14'b0;
	assign tile_intf_arg = 14'b0;
	assign tile_intf_arg = 14'b0;
	assign tile_intf_arg = 14'b0;
	wire[13:0] _router_3_out1 = _wF_router_30 ? (_cond8 && ~(_cond9 || ~_cond10) ? {{_mux_ccontext1[13 +: 1], 4'b0010}, _mux_ccontext1[0 +: 9]} ^ tile_intf_out : (_cond11 ? (_cond12 || ~_cond13 ? {1'b0, _var_m02[0 +: 13]} ^ tile_intf_out : {{_var_m02[13 +: 1], 4'b0010}, _var_m02[0 +: 9]} ^ tile_intf_out) : r2)) : r2;
	assign tile_intf_arg = 14'b0;
	assign tile_intf_arg = 14'b0;
	assign tile_intf_arg = 14'b0;
	assign tile_intf_arg = 14'b0;
	wire[13:0] _router_4_out1 = _if_canFire2 && (_cond14 && ~(_cond15 || ~_cond16)) ? {{_var_m03[13 +: 1], 4'b0011}, _var_m03[0 +: 9]} ^ tile_intf_out : r3;

	always @(posedge CLK) begin
		if (!RST_N) begin
			r1 <= 14'b0;
			r2 <= 14'b0;
			r3 <= 14'b0;
		end else begin
			r1 <= ((_cond0 ? _cond1 || ~($unsigned(_0) < $unsigned(2'b0)) : 1'b1) && (~_router_2_out0 && (~(_cond0 && _cond1) || ~_router_2_out0))) && (_cond0 && _cond1) ? {{_var_m00[13 +: 1], 4'b0}, _var_m00[0 +: 9]} ^ tile_intf_out : (_wF_router_20 ? (_cond2 && ~(_cond3 || ~_cond4) ? {{_mux_ccontext0[13 +: 1], 4'b0001}, _mux_ccontext0[0 +: 9]} ^ tile_intf_out : (_cond5 ? (_cond6 || ~_cond7 ? {1'b0, _var_m01[0 +: 13]} ^ tile_intf_out : {{_var_m01[13 +: 1], 4'b0001}, _var_m01[0 +: 9]} ^ tile_intf_out) : r1)) : r1);
			r2 <= _wF_router_20 ? (_cond2 ? (_cond3 ? {{_mux_ccontext0[13 +: 1], 4'b0001}, _mux_ccontext0[0 +: 9]} ^ tile_intf_out : {1'b0, _mux_ccontext0[0 +: 13]} ^ tile_intf_out) : (_cond5 && _cond6 ? {{_var_m01[13 +: 1], 4'b0001}, _var_m01[0 +: 9]} ^ tile_intf_out : _router_3_out1)) : _router_3_out1;
			r3 <= _wF_router_30 ? (_cond8 ? (_cond9 ? {{_mux_ccontext1[13 +: 1], 4'b0010}, _mux_ccontext1[0 +: 9]} ^ tile_intf_out : {1'b0, _mux_ccontext1[0 +: 13]} ^ tile_intf_out) : (_cond11 && _cond12 ? {{_var_m02[13 +: 1], 4'b0010}, _var_m02[0 +: 9]} ^ tile_intf_out : _router_4_out1)) : _router_4_out1;
		end
	end
endmodule
