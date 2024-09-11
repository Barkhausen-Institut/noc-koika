// -*- mode: verilog -*-
// Generated by cuttlec from a Kôika module
module NoC(input wire[0:0] CLK, input wire[0:0] RST_N, output wire[13:0] extfn_5_arg, output wire[13:0] extfn_8_arg, input wire[13:0] extfn_7_out, input wire[13:0] extfn_1_out, output wire[13:0] extfn_3_arg, input wire[13:0] extfn_3_out, output wire[13:0] extfn_4_arg, output wire[13:0] extfn_7_arg, output wire[13:0] extfn_6_arg, input wire[13:0] extfn_4_out, output wire[13:0] extfn_1_arg, input wire[13:0] extfn_2_out, input wire[13:0] extfn_6_out, output wire[13:0] extfn_2_arg, input wire[13:0] extfn_5_out, input wire[13:0] extfn_8_out);
	reg[13:0] r1 /* verilator public */ = 14'b0;
	reg[13:0] r2 /* verilator public */ = 14'b0;
	reg[13:0] r3 /* verilator public */ = 14'b0;

	assign extfn_1_arg = 14'b0;
	wire[13:0] _0 = r1 ^ extfn_1_out;
	wire[0:0] _cond0 = _0[9 +: 4] != 4'b0 && _0[13 +: 1];
	wire[1:0] _1 = _0[5 +: 2];
	wire[0:0] _cond1 = $unsigned(_1) > $unsigned(2'b0);
	wire[0:0] _cond2 = $unsigned(_1) < $unsigned(2'b0);
	assign extfn_3_arg = 14'b0;
	wire[13:0] _2 = r2 ^ extfn_3_out;
	wire[0:0] _cond3 = _2[9 +: 4] != 4'b0001 && _2[13 +: 1];
	wire[1:0] _3 = _2[5 +: 2];
	wire[0:0] _cond4 = $unsigned(_3) > $unsigned(2'b01);
	wire[0:0] _cond5 = $unsigned(_3) < $unsigned(2'b01);
	assign extfn_3_arg = 14'b0;
	wire[13:0] _var_m00 = r1 ^ extfn_3_out;
	wire[0:0] _cond6 = _var_m00[9 +: 4] != 4'b0001 && _var_m00[13 +: 1];
	wire[1:0] _4 = _var_m00[5 +: 2];
	wire[0:0] _cond7 = $unsigned(_4) > $unsigned(2'b01);
	wire[0:0] _if_canFire0 = _cond6 ? _cond7 : 1'b1;
	wire[0:0] _if_mux0 = _cond6 && _cond7;
	wire[0:0] _write0_canFire0 = _if_canFire0 && ~_if_mux0;
	assign extfn_5_arg = 14'b0;
	wire[13:0] _5 = r3 ^ extfn_5_out;
	wire[0:0] _cond8 = _5[9 +: 4] != 4'b0010 && _5[13 +: 1];
	wire[1:0] _6 = _5[5 +: 2];
	wire[0:0] _cond9 = $unsigned(_6) > $unsigned(2'b10);
	wire[0:0] _cond10 = $unsigned(_6) < $unsigned(2'b10);
	assign extfn_5_arg = 14'b0;
	wire[13:0] _var_m01 = r2 ^ extfn_5_out;
	wire[0:0] _cond11 = _var_m01[9 +: 4] != 4'b0010 && _var_m01[13 +: 1];
	wire[1:0] _7 = _var_m01[5 +: 2];
	wire[0:0] _cond12 = $unsigned(_7) > $unsigned(2'b10);
	wire[0:0] _if_canFire1 = _cond11 ? _cond12 : 1'b1;
	wire[0:0] _if_mux1 = _cond11 && _cond12;
	wire[0:0] _write0_canFire1 = _if_canFire1 && ~_if_mux1;
	assign extfn_7_arg = 14'b0;
	wire[13:0] _8 = r3 ^ extfn_7_out;
	wire[0:0] _cond13 = _8[9 +: 4] != 4'b0011 && _8[13 +: 1];
	wire[1:0] _9 = _8[5 +: 2];
	wire[0:0] _cond14 = $unsigned(_9) > $unsigned(2'b11);
	wire[0:0] _if_canFire2 = _cond13 ? ~_cond14 : 1'b1;
	wire[0:0] _router_4_out0 = _if_canFire2 && (_cond13 && ~_cond14);
	wire[0:0] _wF_router_30 = (_cond8 ? (_cond9 ? 1'b0 : (_cond10 ? _write0_canFire1 && ~_cond11 : _write0_canFire1)) : _if_canFire1) && (~_router_4_out0 && (~(_cond8 || _if_mux1) || ~_router_4_out0));
	wire[0:0] _router_3_out0 = _wF_router_30 && (_cond8 && ~_cond9 ? _cond10 || _cond11 : _cond11);
	wire[0:0] _wF_router_20 = (_cond3 ? (_cond4 ? 1'b0 : (_cond5 ? _write0_canFire0 && ~_cond6 : _write0_canFire0)) : _if_canFire0) && (~_router_3_out0 && (~(_cond3 || _if_mux0) || ~_router_3_out0));
	wire[0:0] _router_2_out0 = _wF_router_20 && (_cond3 && ~_cond4 ? _cond5 || _cond6 : _cond6);
	assign extfn_4_arg = _2;
	wire[13:0] _router_2_out1 = _wF_router_20 ? (_cond3 && ~(_cond4 || ~_cond5) ? {{_2[13 +: 1], 4'b0001}, _2[0 +: 9]} : (_cond6 ? (_cond7 ? {1'b0, _var_m00[0 +: 13]} : ($unsigned(_4) < $unsigned(2'b01) ? {{_var_m00[13 +: 1], 4'b0001}, _var_m00[0 +: 9]} : extfn_4_out)) : r1)) : r1;
	assign extfn_2_arg = _0;
	assign extfn_6_arg = _5;
	wire[13:0] _router_3_out1 = _wF_router_30 ? (_cond8 && ~(_cond9 || ~_cond10) ? {{_5[13 +: 1], 4'b0010}, _5[0 +: 9]} : (_cond11 ? (_cond12 ? {1'b0, _var_m01[0 +: 13]} : ($unsigned(_7) < $unsigned(2'b10) ? {{_var_m01[13 +: 1], 4'b0010}, _var_m01[0 +: 9]} : extfn_6_out)) : r2)) : r2;
	assign extfn_8_arg = _8;
	wire[13:0] _router_4_out1 = _if_canFire2 && (_cond13 && ~_cond14) ? ($unsigned(_9) < $unsigned(2'b11) ? {{_8[13 +: 1], 4'b0011}, _8[0 +: 9]} : extfn_8_out) : r3;

	always @(posedge CLK) begin
		if (!RST_N) begin
			r1 <= 14'b0;
			r2 <= 14'b0;
			r3 <= 14'b0;
		end else begin
			r1 <= ((_cond0 ? _cond1 || ~_cond2 : 1'b1) && (~_router_2_out0 && (~(_cond0 && (_cond1 || ~_cond2)) || ~_router_2_out0))) && _cond0 ? (_cond1 ? {{_0[13 +: 1], 4'b0}, _0[0 +: 9]} : (_cond2 ? _router_2_out1 : extfn_2_out)) : _router_2_out1;
			r2 <= _wF_router_20 ? (_cond3 ? (_cond4 ? {{_2[13 +: 1], 4'b0001}, _2[0 +: 9]} : {1'b0, _2[0 +: 13]}) : (_cond6 && _cond7 ? {{_var_m00[13 +: 1], 4'b0001}, _var_m00[0 +: 9]} : _router_3_out1)) : _router_3_out1;
			r3 <= _wF_router_30 ? (_cond8 ? (_cond9 ? {{_5[13 +: 1], 4'b0010}, _5[0 +: 9]} : {1'b0, _5[0 +: 13]}) : (_cond11 && _cond12 ? {{_var_m01[13 +: 1], 4'b0010}, _var_m01[0 +: 9]} : _router_4_out1)) : _router_4_out1;
		end
	end
endmodule
