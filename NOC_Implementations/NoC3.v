// -*- mode: verilog -*-
// Generated by cuttlec from a Kôika module
module NoC3(input wire[0:0] CLK, input wire[0:0] RST_N, output wire[8:0] extinput1_arg, input wire[8:0] extinput2_out, output wire[8:0] extoutput3_arg, output wire[8:0] extinput0_arg, input wire[8:0] extinput1_out, input wire[8:0] extoutput1_out, input wire[8:0] extinput0_out, input wire[8:0] extoutput0_out, input wire[8:0] extoutput2_out, output wire[8:0] extoutput2_arg, output wire[8:0] extoutput1_arg, input wire[8:0] extoutput3_out, output wire[8:0] extinput2_arg, output wire[8:0] extoutput0_arg, input wire[8:0] extinput3_out, output wire[8:0] extinput3_arg);
	reg[8:0] routerstate0 /* verilator public */ = 9'b0;
	reg[8:0] routerdownstream0 /* verilator public */ = 9'b0;
	reg[8:0] routerstate1 /* verilator public */ = 9'b0;
	reg[8:0] routerdownstream1 /* verilator public */ = 9'b0;
	reg[8:0] routerstate2 /* verilator public */ = 9'b0;
	reg[8:0] routerdownstream2 /* verilator public */ = 9'b0;
	reg[8:0] routerstate3 /* verilator public */ = 9'b0;
	reg[8:0] routerdownstream3 /* verilator public */ = 9'b0;

	assign extinput0_arg = 9'b0;
	wire[0:0] _cond0 = extinput0_out[8 +: 1] && extinput0_out[6 +: 2] == 2'b11;
	wire[0:0] _cond1 = routerstate0[6 +: 2] != 2'b11 && routerstate0[8 +: 1];
	wire[1:0] _0 = routerstate0[4 +: 2];
	wire[0:0] _cond2 = $unsigned(_0) > $unsigned(2'b11);
	wire[0:0] _if_canFire0 = _cond0 || (_cond1 ? ~_cond2 : 1'b1);
	wire[0:0] _cond3 = $unsigned(_0) < $unsigned(2'b11);
	assign extinput1_arg = 9'b0;
	wire[0:0] _cond4 = (extinput1_out[8 +: 1] && $unsigned(extinput1_out[4 +: 2]) > $unsigned(2'b11)) && extinput1_out[6 +: 2] == 2'b11;
	wire[0:0] _cond5 = routerdownstream2[6 +: 2] != 2'b11 && routerdownstream2[8 +: 1];
	wire[1:0] _1 = routerdownstream2[4 +: 2];
	wire[0:0] _cond6 = $unsigned(_1) > $unsigned(2'b11);
	wire[0:0] _cond7 = $unsigned(_1) < $unsigned(2'b11);
	wire[0:0] _cond8 = routerstate1[6 +: 2] != 2'b11 && routerstate1[8 +: 1];
	wire[1:0] _2 = routerstate1[4 +: 2];
	wire[0:0] _cond9 = $unsigned(_2) > $unsigned(2'b11);
	wire[0:0] _cond10 = $unsigned(_2) < $unsigned(2'b11);
	wire[0:0] _if_canFire1 = _cond8 ? _cond9 || ~_cond10 : 1'b1;
	wire[0:0] _if_mux0 = _cond8 && _cond9;
	wire[0:0] _write0_canFire0 = _if_canFire1 && ~_if_mux0;
	wire[0:0] _if_mux1 = _cond8 && (_cond9 ? 1'b0 : ~_cond10);
	wire[0:0] _wF_rule10 = (_cond4 || (_cond5 ? (_cond6 ? 1'b0 : (_cond7 ? _write0_canFire0 && ~_cond8 : _write0_canFire0 && ~_if_mux1)) : _if_canFire1)) && (~(_cond4 ? 1'b0 : _cond5 && ~(_cond6 || _cond7) || _if_mux1) || ~(_if_canFire0 && (_cond0 ? 1'b0 : _cond1 && (_cond2 ? 1'b0 : ~_cond3))));
	assign extoutput1_arg = routerdownstream2;
	assign extoutput1_arg = routerstate1;
	assign extoutput0_arg = routerstate0;
	wire[8:0] _rule0_out0 = _if_canFire0 && ~(_cond0 || ~(_cond1 && ~(_cond2 || _cond3))) ? extoutput0_out : routerdownstream1;
	assign extinput2_arg = 9'b0;
	wire[0:0] _cond11 = (extinput2_out[8 +: 1] && $unsigned(extinput2_out[4 +: 2]) > $unsigned(2'b11)) && extinput2_out[6 +: 2] == 2'b11;
	wire[0:0] _cond12 = routerdownstream3[6 +: 2] != 2'b11 && routerdownstream3[8 +: 1];
	wire[1:0] _3 = routerdownstream3[4 +: 2];
	wire[0:0] _cond13 = $unsigned(_3) > $unsigned(2'b11);
	wire[0:0] _cond14 = $unsigned(_3) < $unsigned(2'b11);
	wire[0:0] _cond15 = routerstate2[6 +: 2] != 2'b11 && routerstate2[8 +: 1];
	wire[1:0] _4 = routerstate2[4 +: 2];
	wire[0:0] _cond16 = $unsigned(_4) > $unsigned(2'b11);
	wire[0:0] _cond17 = $unsigned(_4) < $unsigned(2'b11);
	wire[0:0] _if_canFire2 = _cond15 ? _cond16 || ~_cond17 : 1'b1;
	wire[0:0] _if_mux2 = _cond15 && _cond16;
	wire[0:0] _write0_canFire1 = _if_canFire2 && ~_if_mux2;
	wire[0:0] _if_mux3 = _cond15 && (_cond16 ? 1'b0 : ~_cond17);
	wire[0:0] _wF_rule20 = (_cond11 || (_cond12 ? (_cond13 ? 1'b0 : (_cond14 ? _write0_canFire1 && ~_cond15 : _write0_canFire1 && ~_if_mux3)) : _if_canFire2)) && (~(_cond11 ? 1'b0 : _cond12 && ~(_cond13 || _cond14) || _if_mux3) || ~(_wF_rule10 && (_cond4 || (_cond5 || _if_mux0))));
	assign extoutput2_arg = routerdownstream3;
	assign extoutput2_arg = routerstate2;
	wire[8:0] _rule1_out0 = _wF_rule10 ? (_cond4 ? extinput1_out : (_cond5 ? (_cond6 ? {{routerdownstream2[8 +: 1], 2'b11}, routerdownstream2[0 +: 6]} : {1'b0, routerdownstream2[0 +: 8]}) : (_cond8 && _cond9 ? {{routerstate1[8 +: 1], 2'b11}, routerstate1[0 +: 6]} : routerdownstream2))) : routerdownstream2;
	assign extinput3_arg = 9'b0;
	wire[0:0] _cond18 = extinput3_out[8 +: 1] && extinput3_out[6 +: 2] == 2'b0;
	wire[0:0] _cond19 = routerstate3[6 +: 2] != 2'b0 && routerstate3[8 +: 1];
	wire[1:0] _5 = routerstate3[4 +: 2];
	wire[0:0] _cond20 = $unsigned(_5) > $unsigned(2'b0);
	wire[0:0] _cond21 = $unsigned(_5) < $unsigned(2'b0);
	wire[0:0] _wF_rule30 = (_cond18 || (_cond19 ? _cond20 || ~_cond21 : 1'b1)) && (~(_cond18 ? 1'b0 : _cond19 && (_cond20 ? 1'b0 : ~_cond21)) || ~(_wF_rule20 && (_cond11 || (_cond12 || _if_mux2))));
	assign extoutput3_arg = routerstate3;

	always @(posedge CLK) begin
		if (!RST_N) begin
			routerstate0 <= 9'b0;
			routerdownstream0 <= 9'b0;
			routerstate1 <= 9'b0;
			routerdownstream1 <= 9'b0;
			routerstate2 <= 9'b0;
			routerdownstream2 <= 9'b0;
			routerstate3 <= 9'b0;
			routerdownstream3 <= 9'b0;
		end else begin
			routerstate0 <= _if_canFire0 ? (_cond0 ? extinput0_out : (_cond1 && ~(_cond2 || ~_cond3) ? {{routerstate0[8 +: 1], 2'b11}, routerstate0[0 +: 6]} : routerstate0)) : routerstate0;
			routerdownstream0 <= routerdownstream0;
			routerstate1 <= _wF_rule10 && ~_cond4 ? (_cond5 && ~(_cond6 || ~_cond7) ? {{routerdownstream2[8 +: 1], 2'b11}, routerdownstream2[0 +: 6]} : (_cond8 ? (_cond9 || ~_cond10 ? {1'b0, routerstate1[0 +: 8]} : {{routerstate1[8 +: 1], 2'b11}, routerstate1[0 +: 6]}) : routerstate1)) : routerstate1;
			routerdownstream1 <= _wF_rule10 && ~_cond4 ? (_cond5 && ~(_cond6 || _cond7) ? extoutput1_out : (_cond8 && ~(_cond9 || _cond10) ? extoutput1_out : _rule0_out0)) : _rule0_out0;
			routerstate2 <= _wF_rule20 && ~_cond11 ? (_cond12 && ~(_cond13 || ~_cond14) ? {{routerdownstream3[8 +: 1], 2'b11}, routerdownstream3[0 +: 6]} : (_cond15 ? (_cond16 || ~_cond17 ? {1'b0, routerstate2[0 +: 8]} : {{routerstate2[8 +: 1], 2'b11}, routerstate2[0 +: 6]}) : routerstate2)) : routerstate2;
			routerdownstream2 <= _wF_rule20 && ~_cond11 ? (_cond12 && ~(_cond13 || _cond14) ? extoutput2_out : (_cond15 && ~(_cond16 || _cond17) ? extoutput2_out : _rule1_out0)) : _rule1_out0;
			routerstate3 <= _wF_rule30 ? (_cond18 ? extinput3_out : (_cond19 && _cond20 ? {{routerstate3[8 +: 1], 2'b0}, routerstate3[0 +: 6]} : routerstate3)) : routerstate3;
			routerdownstream3 <= _wF_rule30 && ~(_cond18 || ~(_cond19 && ~(_cond20 || _cond21))) ? extoutput3_out : (_wF_rule20 ? (_cond11 ? extinput2_out : (_cond12 ? (_cond13 ? {{routerdownstream3[8 +: 1], 2'b11}, routerdownstream3[0 +: 6]} : {1'b0, routerdownstream3[0 +: 8]}) : (_cond15 && _cond16 ? {{routerstate2[8 +: 1], 2'b11}, routerstate2[0 +: 6]} : routerdownstream3))) : routerdownstream3);
		end
	end
endmodule
