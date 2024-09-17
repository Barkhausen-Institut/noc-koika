#ifndef MODULE_NOC_HPP
#define MODULE_NOC_HPP

//////////////
// PREAMBLE //
//////////////

#include "cuttlesim.hpp"

//////////////
// TYPEDEFS //
//////////////


struct struct_basic_flit {
bits<1> renamed_cppnew;
bits<4> src;
bits<4> dest;
bits<4> data;
};

static _unused bits<1>  operator==(const struct_basic_flit v1, const struct_basic_flit v2) {
return bits<1>::mk(bool(v1.renamed_cppnew == v2.renamed_cppnew) && bool(v1.src == v2.src) && bool(v1.dest == v2.dest) && bool(v1.data == v2.data));
}
static _unused bits<1>  operator!=(const struct_basic_flit v1, const struct_basic_flit v2) {
return !(v1 == v2);}

#ifndef SIM_MINIMAL
static _unused std::ostream& operator<<(std::ostream& os, const struct_basic_flit& val) {
return prims::fmt(os, val);
}
#endif

namespace prims {
#ifndef SIM_MINIMAL
static _unused std::ostream& fmt(std::ostream& os, const struct_basic_flit& val, const fmtopts opts) {
os << "basic_flit { ";
os << ".new = "; fmt(os, val.renamed_cppnew, opts) << "; ";
os << ".src = "; fmt(os, val.src, opts) << "; ";
os << ".dest = "; fmt(os, val.dest, opts) << "; ";
os << ".data = "; fmt(os, val.data, opts) << "; ";
os << "}";
return os;
}
#endif

template <> struct type_info<struct_basic_flit> {
static constexpr prims::bitwidth size = 13;
};

template <> _unused bits<13> pack<>(const struct_basic_flit val) {
bits<13> packed = 13'0_b;
packed |= prims::widen<13>(val.renamed_cppnew);
packed <<= 4;
packed |= prims::widen<13>(val.src);
packed <<= 4;
packed |= prims::widen<13>(val.dest);
packed <<= 4;
packed |= prims::widen<13>(val.data);
return packed;
}

template <> struct _unpack<struct_basic_flit, 13> {
static struct_basic_flit unpack(const bits<13> bs) {
struct_basic_flit unpacked = {};
unpacked.data = prims::truncate<4>(bs >> 0u);
unpacked.dest = prims::truncate<4>(bs >> 4u);
unpacked.src = prims::truncate<4>(bs >> 8u);
unpacked.renamed_cppnew = prims::truncate<1>(bs >> 12u);
return unpacked;
}
};
}

////////////////////
// IMPLEMENTATION //
////////////////////

template <typename extfuns_t> class module_NoC {
public:
struct state_t {
bits<13> r1;
bits<13> r2;
bits<13> r3;
bits<13> r4;
bits<13> r5;
bits<13> r6;
bits<13> r7;
bits<13> r8;
bits<13> r9;
bits<13> r10;
bits<13> r11;
bits<13> r12;
bits<13> r13;
bits<13> r14;
bits<13> r15;
bits<13> r16;
bits<13> r17;
bits<13> r18;
bits<13> r19;

#ifndef SIM_MINIMAL
void dump(std::ostream& os = std::cout) const {
os << "r1 = " << r1 << std::endl;
os << "r2 = " << r2 << std::endl;
os << "r3 = " << r3 << std::endl;
os << "r4 = " << r4 << std::endl;
os << "r5 = " << r5 << std::endl;
os << "r6 = " << r6 << std::endl;
os << "r7 = " << r7 << std::endl;
os << "r8 = " << r8 << std::endl;
os << "r9 = " << r9 << std::endl;
os << "r10 = " << r10 << std::endl;
os << "r11 = " << r11 << std::endl;
os << "r12 = " << r12 << std::endl;
os << "r13 = " << r13 << std::endl;
os << "r14 = " << r14 << std::endl;
os << "r15 = " << r15 << std::endl;
os << "r16 = " << r16 << std::endl;
os << "r17 = " << r17 << std::endl;
os << "r18 = " << r18 << std::endl;
os << "r19 = " << r19 << std::endl;
}

static _unused void vcd_header(std::ostream& os) {
#ifndef SIM_VCD_SCOPES
#define SIM_VCD_SCOPES { "TOP", "NoC" }
#endif
cuttlesim::vcd::begin_header(os, SIM_VCD_SCOPES);
cuttlesim::vcd::var(os, "r1", 13);
cuttlesim::vcd::var(os, "r2", 13);
cuttlesim::vcd::var(os, "r3", 13);
cuttlesim::vcd::var(os, "r4", 13);
cuttlesim::vcd::var(os, "r5", 13);
cuttlesim::vcd::var(os, "r6", 13);
cuttlesim::vcd::var(os, "r7", 13);
cuttlesim::vcd::var(os, "r8", 13);
cuttlesim::vcd::var(os, "r9", 13);
cuttlesim::vcd::var(os, "r10", 13);
cuttlesim::vcd::var(os, "r11", 13);
cuttlesim::vcd::var(os, "r12", 13);
cuttlesim::vcd::var(os, "r13", 13);
cuttlesim::vcd::var(os, "r14", 13);
cuttlesim::vcd::var(os, "r15", 13);
cuttlesim::vcd::var(os, "r16", 13);
cuttlesim::vcd::var(os, "r17", 13);
cuttlesim::vcd::var(os, "r18", 13);
cuttlesim::vcd::var(os, "r19", 13);
cuttlesim::vcd::end_header(os, SIM_VCD_SCOPES);
}

void vcd_dumpvars(std::uint_fast64_t cycle_id, _unused std::ostream& os, const state_t& previous, const bool force) const {
os << '#' << cycle_id << std::endl;
cuttlesim::vcd::dumpvar(os, "r1", r1, previous.r1, force);
cuttlesim::vcd::dumpvar(os, "r2", r2, previous.r2, force);
cuttlesim::vcd::dumpvar(os, "r3", r3, previous.r3, force);
cuttlesim::vcd::dumpvar(os, "r4", r4, previous.r4, force);
cuttlesim::vcd::dumpvar(os, "r5", r5, previous.r5, force);
cuttlesim::vcd::dumpvar(os, "r6", r6, previous.r6, force);
cuttlesim::vcd::dumpvar(os, "r7", r7, previous.r7, force);
cuttlesim::vcd::dumpvar(os, "r8", r8, previous.r8, force);
cuttlesim::vcd::dumpvar(os, "r9", r9, previous.r9, force);
cuttlesim::vcd::dumpvar(os, "r10", r10, previous.r10, force);
cuttlesim::vcd::dumpvar(os, "r11", r11, previous.r11, force);
cuttlesim::vcd::dumpvar(os, "r12", r12, previous.r12, force);
cuttlesim::vcd::dumpvar(os, "r13", r13, previous.r13, force);
cuttlesim::vcd::dumpvar(os, "r14", r14, previous.r14, force);
cuttlesim::vcd::dumpvar(os, "r15", r15, previous.r15, force);
cuttlesim::vcd::dumpvar(os, "r16", r16, previous.r16, force);
cuttlesim::vcd::dumpvar(os, "r17", r17, previous.r17, force);
cuttlesim::vcd::dumpvar(os, "r18", r18, previous.r18, force);
cuttlesim::vcd::dumpvar(os, "r19", r19, previous.r19, force);
}

std::uint_fast64_t vcd_readvars(_unused std::istream& is) {
std::string var{}, val{};
std::uint_fast64_t cycle_id = std::numeric_limits<std::uint_fast64_t>::max();
cuttlesim::vcd::read_header(is);
while (cuttlesim::vcd::readvar(is, cycle_id, var, val)) {
if (var == "r1") {
r1 = prims::unpack<bits<13>>(bits<13>::of_str(val));
}
else if (var == "r2") {
r2 = prims::unpack<bits<13>>(bits<13>::of_str(val));
}
else if (var == "r3") {
r3 = prims::unpack<bits<13>>(bits<13>::of_str(val));
}
else if (var == "r4") {
r4 = prims::unpack<bits<13>>(bits<13>::of_str(val));
}
else if (var == "r5") {
r5 = prims::unpack<bits<13>>(bits<13>::of_str(val));
}
else if (var == "r6") {
r6 = prims::unpack<bits<13>>(bits<13>::of_str(val));
}
else if (var == "r7") {
r7 = prims::unpack<bits<13>>(bits<13>::of_str(val));
}
else if (var == "r8") {
r8 = prims::unpack<bits<13>>(bits<13>::of_str(val));
}
else if (var == "r9") {
r9 = prims::unpack<bits<13>>(bits<13>::of_str(val));
}
else if (var == "r10") {
r10 = prims::unpack<bits<13>>(bits<13>::of_str(val));
}
else if (var == "r11") {
r11 = prims::unpack<bits<13>>(bits<13>::of_str(val));
}
else if (var == "r12") {
r12 = prims::unpack<bits<13>>(bits<13>::of_str(val));
}
else if (var == "r13") {
r13 = prims::unpack<bits<13>>(bits<13>::of_str(val));
}
else if (var == "r14") {
r14 = prims::unpack<bits<13>>(bits<13>::of_str(val));
}
else if (var == "r15") {
r15 = prims::unpack<bits<13>>(bits<13>::of_str(val));
}
else if (var == "r16") {
r16 = prims::unpack<bits<13>>(bits<13>::of_str(val));
}
else if (var == "r17") {
r17 = prims::unpack<bits<13>>(bits<13>::of_str(val));
}
else if (var == "r18") {
r18 = prims::unpack<bits<13>>(bits<13>::of_str(val));
}
else if (var == "r19") {
r19 = prims::unpack<bits<13>>(bits<13>::of_str(val));
}
}
return cycle_id;
}
#endif
};

using snapshot_t = cuttlesim::snapshot_t<state_t>;

protected:
struct rwset_t {
cuttlesim::reg_rwset r1;
cuttlesim::reg_rwset r2;
cuttlesim::reg_rwset r3;
cuttlesim::reg_rwset r4;
cuttlesim::reg_rwset r5;
cuttlesim::reg_rwset r6;
cuttlesim::reg_rwset r7;
cuttlesim::reg_rwset r8;
cuttlesim::reg_rwset r9;
cuttlesim::reg_rwset r11;
cuttlesim::reg_rwset r12;
cuttlesim::reg_rwset r13;
cuttlesim::reg_rwset r14;
cuttlesim::reg_rwset r15;
cuttlesim::reg_rwset r16;
cuttlesim::reg_rwset r17;
cuttlesim::reg_rwset r18;
};

struct log_t {
rwset_t rwset;
state_t state;

const state_t& snapshot() const {
return state;
}
explicit log_t(const state_t& init) : rwset{}, state(init) {
}
};

log_t log;
log_t Log;
extfuns_t extfuns;
cuttlesim::sim_metadata meta;

#ifndef SIM_MINIMAL
std::default_random_engine rng{};
std::uniform_int_distribution<int> uniform{0, 9};
#endif

#define RULE_NAME router_3
DEF_RESET(router_3) {
log.state.r2 = Log.state.r2;
log.state.r3 = Log.state.r3;
log.state.r12 = Log.state.r12;
log.rwset.r2 = Log.rwset.r2;
log.rwset.r3 = Log.rwset.r3;
log.rwset.r12 = Log.rwset.r12;
}

DEF_COMMIT(router_3) {
Log.state.r2 = log.state.r2;
Log.state.r3 = log.state.r3;
Log.state.r12 = log.state.r12;
Log.rwset.r2 = log.rwset.r2;
Log.rwset.r3 = log.rwset.r3;
Log.rwset.r12 = log.rwset.r12;
}

DECL_FN(r_send_0, unit)
DEF_FN(r_send_0, unit &_ret, bits<13> value) {
WRITE0(r3, value);
_ret = prims::tt;
return true;
}

DECL_FN(r_send_1, unit)
DEF_FN(r_send_1, unit &_ret, bits<13> value) {
WRITE0(r2, value);
_ret = prims::tt;
return true;
}

DECL_FN(r_receive_0, bits<13>)
DEF_FN(r_receive_0, bits<13> &_ret) {
_ret = READ0(r2);
return true;
}

DECL_FN(r_receive_1, bits<13>)
DEF_FN(r_receive_1, bits<13> &_ret) {
_ret = READ0(r3);
return true;
}

DECL_FN(r_send_2, unit)
DEF_FN(r_send_2, unit &_ret, bits<13> value) {
WRITE0(r2, value);
_ret = prims::tt;
return true;
}

DECL_FN(r_send_3, unit)
DEF_FN(r_send_3, unit &_ret, bits<13> value) {
WRITE0(r3, value);
_ret = prims::tt;
return true;
}

DECL_FN(r_send_4, unit)
DEF_FN(r_send_4, unit &_ret, bits<13> value) {
WRITE0(r2, value);
_ret = prims::tt;
return true;
}

DECL_FN(r_send_5, unit)
DEF_FN(r_send_5, unit &_ret, bits<13> value) {
WRITE0(r12, value);
_ret = prims::tt;
return true;
}

DECL_FN(r_send_6, unit)
DEF_FN(r_send_6, unit &_ret, bits<13> value) {
WRITE0(r3, value);
_ret = prims::tt;
return true;
}

DECL_FN(r_send_7, unit)
DEF_FN(r_send_7, unit &_ret, bits<13> value) {
WRITE0(r3, value);
_ret = prims::tt;
return true;
}

DECL_FN(r_send_8, unit)
DEF_FN(r_send_8, unit &_ret, bits<13> value) {
WRITE0(r2, value);
_ret = prims::tt;
return true;
}

DECL_FN(r_send_9, unit)
DEF_FN(r_send_9, unit &_ret, bits<13> value) {
WRITE0(r12, value);
_ret = prims::tt;
return true;
}
DEF_RULE(router_3) {
bits<4> r_addr = 4'0010_b;
bits<13> m_input = extfuns.extfn_5(13'0_b);
struct_basic_flit msg = prims::unpack<struct_basic_flit>(m_input);
bits<1> new_data = msg.renamed_cppnew;
bits<4> dest = msg.dest;
bits<4> src_p = msg.src;
if ((new_data & ((src_p == r_addr) & (dest > r_addr)))) {
CALL_FN(r_send_0, m_input);
}
else {
if ((new_data & ((src_p == r_addr) & (dest < r_addr)))) {
CALL_FN(r_send_1, m_input);
}
else {
bits<13> m0 = CALL_FN(r_receive_0);
bits<13> m1 = CALL_FN(r_receive_1);
struct_basic_flit msg = prims::unpack<struct_basic_flit>(m0);
bits<1> new_data = msg.renamed_cppnew;
bits<4> src_p = msg.src;
if (((src_p != r_addr) & new_data)) {
struct_basic_flit _x13 = msg;
_x13.renamed_cppnew = 1'0_b;
CALL_FN(r_send_2, prims::pack(_x13));
bits<4> dest = msg.dest;
if ((dest > r_addr)) {
struct_basic_flit _x16 = msg;
_x16.src = r_addr;
CALL_FN(r_send_3, prims::pack(_x16));
}
else {
if ((dest < r_addr)) {
struct_basic_flit _x18 = msg;
_x18.src = r_addr;
CALL_FN(r_send_4, prims::pack(_x18));
}
else {
bits<13> _value5 = extfuns.extfn_6(m0);
CALL_FN(r_send_5, _value5);
}
}
}
/* bind */ {
struct_basic_flit msg = prims::unpack<struct_basic_flit>(m1);
bits<1> new_data = msg.renamed_cppnew;
bits<4> src_p = msg.src;
if (((src_p != r_addr) & new_data)) {
struct_basic_flit _x24 = msg;
_x24.renamed_cppnew = 1'0_b;
CALL_FN(r_send_6, prims::pack(_x24));
bits<4> dest = msg.dest;
if ((dest > r_addr)) {
struct_basic_flit _x27 = msg;
_x27.src = r_addr;
CALL_FN(r_send_7, prims::pack(_x27));
}
else {
if ((dest < r_addr)) {
struct_basic_flit _x29 = msg;
_x29.src = r_addr;
CALL_FN(r_send_8, prims::pack(_x29));
}
else {
bits<13> _value9 = extfuns.extfn_6(m1);
CALL_FN(r_send_9, _value9);
}
}
}
}
}
}

COMMIT();
}
#undef RULE_NAME

#define RULE_NAME router_7
DEF_RESET(router_7) {
log.state.r6 = Log.state.r6;
log.state.r7 = Log.state.r7;
log.state.r16 = Log.state.r16;
log.rwset.r6 = Log.rwset.r6;
log.rwset.r7 = Log.rwset.r7;
log.rwset.r16 = Log.rwset.r16;
}

DEF_COMMIT(router_7) {
Log.state.r6 = log.state.r6;
Log.state.r7 = log.state.r7;
Log.state.r16 = log.state.r16;
Log.rwset.r6 = log.rwset.r6;
Log.rwset.r7 = log.rwset.r7;
Log.rwset.r16 = log.rwset.r16;
}

DECL_FN(r_send_10, unit)
DEF_FN(r_send_10, unit &_ret, bits<13> value) {
WRITE0(r7, value);
_ret = prims::tt;
return true;
}

DECL_FN(r_send_11, unit)
DEF_FN(r_send_11, unit &_ret, bits<13> value) {
WRITE0(r6, value);
_ret = prims::tt;
return true;
}

DECL_FN(r_receive_2, bits<13>)
DEF_FN(r_receive_2, bits<13> &_ret) {
_ret = READ0(r6);
return true;
}

DECL_FN(r_receive_3, bits<13>)
DEF_FN(r_receive_3, bits<13> &_ret) {
_ret = READ0(r7);
return true;
}

DECL_FN(r_send_12, unit)
DEF_FN(r_send_12, unit &_ret, bits<13> value) {
WRITE0(r6, value);
_ret = prims::tt;
return true;
}

DECL_FN(r_send_13, unit)
DEF_FN(r_send_13, unit &_ret, bits<13> value) {
WRITE0(r7, value);
_ret = prims::tt;
return true;
}

DECL_FN(r_send_14, unit)
DEF_FN(r_send_14, unit &_ret, bits<13> value) {
WRITE0(r6, value);
_ret = prims::tt;
return true;
}

DECL_FN(r_send_15, unit)
DEF_FN(r_send_15, unit &_ret, bits<13> value) {
WRITE0(r16, value);
_ret = prims::tt;
return true;
}

DECL_FN(r_send_16, unit)
DEF_FN(r_send_16, unit &_ret, bits<13> value) {
WRITE0(r7, value);
_ret = prims::tt;
return true;
}

DECL_FN(r_send_17, unit)
DEF_FN(r_send_17, unit &_ret, bits<13> value) {
WRITE0(r7, value);
_ret = prims::tt;
return true;
}

DECL_FN(r_send_18, unit)
DEF_FN(r_send_18, unit &_ret, bits<13> value) {
WRITE0(r6, value);
_ret = prims::tt;
return true;
}

DECL_FN(r_send_19, unit)
DEF_FN(r_send_19, unit &_ret, bits<13> value) {
WRITE0(r16, value);
_ret = prims::tt;
return true;
}
DEF_RULE(router_7) {
bits<4> r_addr = 4'0110_b;
bits<13> m_input = extfuns.extfn_13(13'0_b);
struct_basic_flit msg = prims::unpack<struct_basic_flit>(m_input);
bits<1> new_data = msg.renamed_cppnew;
bits<4> dest = msg.dest;
bits<4> src_p = msg.src;
if ((new_data & ((src_p == r_addr) & (dest > r_addr)))) {
CALL_FN(r_send_10, m_input);
}
else {
if ((new_data & ((src_p == r_addr) & (dest < r_addr)))) {
CALL_FN(r_send_11, m_input);
}
else {
bits<13> m0 = CALL_FN(r_receive_2);
bits<13> m1 = CALL_FN(r_receive_3);
struct_basic_flit msg = prims::unpack<struct_basic_flit>(m0);
bits<1> new_data = msg.renamed_cppnew;
bits<4> src_p = msg.src;
if (((src_p != r_addr) & new_data)) {
struct_basic_flit _x13 = msg;
_x13.renamed_cppnew = 1'0_b;
CALL_FN(r_send_12, prims::pack(_x13));
bits<4> dest = msg.dest;
if ((dest > r_addr)) {
struct_basic_flit _x16 = msg;
_x16.src = r_addr;
CALL_FN(r_send_13, prims::pack(_x16));
}
else {
if ((dest < r_addr)) {
struct_basic_flit _x18 = msg;
_x18.src = r_addr;
CALL_FN(r_send_14, prims::pack(_x18));
}
else {
bits<13> _value5 = extfuns.extfn_14(m0);
CALL_FN(r_send_15, _value5);
}
}
}
/* bind */ {
struct_basic_flit msg = prims::unpack<struct_basic_flit>(m1);
bits<1> new_data = msg.renamed_cppnew;
bits<4> src_p = msg.src;
if (((src_p != r_addr) & new_data)) {
struct_basic_flit _x24 = msg;
_x24.renamed_cppnew = 1'0_b;
CALL_FN(r_send_16, prims::pack(_x24));
bits<4> dest = msg.dest;
if ((dest > r_addr)) {
struct_basic_flit _x27 = msg;
_x27.src = r_addr;
CALL_FN(r_send_17, prims::pack(_x27));
}
else {
if ((dest < r_addr)) {
struct_basic_flit _x29 = msg;
_x29.src = r_addr;
CALL_FN(r_send_18, prims::pack(_x29));
}
else {
bits<13> _value9 = extfuns.extfn_14(m1);
CALL_FN(r_send_19, _value9);
}
}
}
}
}
}

COMMIT();
}
#undef RULE_NAME

#define RULE_NAME router_9
DEF_RESET(router_9) {
log.state.r8 = Log.state.r8;
log.state.r9 = Log.state.r9;
log.state.r18 = Log.state.r18;
log.rwset.r8 = Log.rwset.r8;
log.rwset.r9 = Log.rwset.r9;
log.rwset.r18 = Log.rwset.r18;
}

DEF_COMMIT(router_9) {
Log.state.r8 = log.state.r8;
Log.state.r9 = log.state.r9;
Log.state.r18 = log.state.r18;
Log.rwset.r8 = log.rwset.r8;
Log.rwset.r9 = log.rwset.r9;
Log.rwset.r18 = log.rwset.r18;
}

DECL_FN(r_send_20, unit)
DEF_FN(r_send_20, unit &_ret, bits<13> value) {
WRITE0(r9, value);
_ret = prims::tt;
return true;
}

DECL_FN(r_send_21, unit)
DEF_FN(r_send_21, unit &_ret, bits<13> value) {
WRITE0(r8, value);
_ret = prims::tt;
return true;
}

DECL_FN(r_receive_4, bits<13>)
DEF_FN(r_receive_4, bits<13> &_ret) {
_ret = READ0(r8);
return true;
}

DECL_FN(r_receive_5, bits<13>)
DEF_FN(r_receive_5, bits<13> &_ret) {
_ret = READ0(r9);
return true;
}

DECL_FN(r_send_22, unit)
DEF_FN(r_send_22, unit &_ret, bits<13> value) {
WRITE0(r8, value);
_ret = prims::tt;
return true;
}

DECL_FN(r_send_23, unit)
DEF_FN(r_send_23, unit &_ret, bits<13> value) {
WRITE0(r9, value);
_ret = prims::tt;
return true;
}

DECL_FN(r_send_24, unit)
DEF_FN(r_send_24, unit &_ret, bits<13> value) {
WRITE0(r8, value);
_ret = prims::tt;
return true;
}

DECL_FN(r_send_25, unit)
DEF_FN(r_send_25, unit &_ret, bits<13> value) {
WRITE0(r18, value);
_ret = prims::tt;
return true;
}

DECL_FN(r_send_26, unit)
DEF_FN(r_send_26, unit &_ret, bits<13> value) {
WRITE0(r9, value);
_ret = prims::tt;
return true;
}

DECL_FN(r_send_27, unit)
DEF_FN(r_send_27, unit &_ret, bits<13> value) {
WRITE0(r9, value);
_ret = prims::tt;
return true;
}

DECL_FN(r_send_28, unit)
DEF_FN(r_send_28, unit &_ret, bits<13> value) {
WRITE0(r8, value);
_ret = prims::tt;
return true;
}

DECL_FN(r_send_29, unit)
DEF_FN(r_send_29, unit &_ret, bits<13> value) {
WRITE0(r18, value);
_ret = prims::tt;
return true;
}
DEF_RULE(router_9) {
bits<4> r_addr = 4'1000_b;
bits<13> m_input = extfuns.extfn_17(13'0_b);
struct_basic_flit msg = prims::unpack<struct_basic_flit>(m_input);
bits<1> new_data = msg.renamed_cppnew;
bits<4> dest = msg.dest;
bits<4> src_p = msg.src;
if ((new_data & ((src_p == r_addr) & (dest > r_addr)))) {
CALL_FN(r_send_20, m_input);
}
else {
if ((new_data & ((src_p == r_addr) & (dest < r_addr)))) {
CALL_FN(r_send_21, m_input);
}
else {
bits<13> m0 = CALL_FN(r_receive_4);
bits<13> m1 = CALL_FN(r_receive_5);
struct_basic_flit msg = prims::unpack<struct_basic_flit>(m0);
bits<1> new_data = msg.renamed_cppnew;
bits<4> src_p = msg.src;
if (((src_p != r_addr) & new_data)) {
struct_basic_flit _x13 = msg;
_x13.renamed_cppnew = 1'0_b;
CALL_FN(r_send_22, prims::pack(_x13));
bits<4> dest = msg.dest;
if ((dest > r_addr)) {
struct_basic_flit _x16 = msg;
_x16.src = r_addr;
CALL_FN(r_send_23, prims::pack(_x16));
}
else {
if ((dest < r_addr)) {
struct_basic_flit _x18 = msg;
_x18.src = r_addr;
CALL_FN(r_send_24, prims::pack(_x18));
}
else {
bits<13> _value5 = extfuns.extfn_18(m0);
CALL_FN(r_send_25, _value5);
}
}
}
/* bind */ {
struct_basic_flit msg = prims::unpack<struct_basic_flit>(m1);
bits<1> new_data = msg.renamed_cppnew;
bits<4> src_p = msg.src;
if (((src_p != r_addr) & new_data)) {
struct_basic_flit _x24 = msg;
_x24.renamed_cppnew = 1'0_b;
CALL_FN(r_send_26, prims::pack(_x24));
bits<4> dest = msg.dest;
if ((dest > r_addr)) {
struct_basic_flit _x27 = msg;
_x27.src = r_addr;
CALL_FN(r_send_27, prims::pack(_x27));
}
else {
if ((dest < r_addr)) {
struct_basic_flit _x29 = msg;
_x29.src = r_addr;
CALL_FN(r_send_28, prims::pack(_x29));
}
else {
bits<13> _value9 = extfuns.extfn_18(m1);
CALL_FN(r_send_29, _value9);
}
}
}
}
}
}

COMMIT();
}
#undef RULE_NAME

#define RULE_NAME router_4
DEF_RESET(router_4) {
log.state.r3 = Log.state.r3;
log.state.r4 = Log.state.r4;
log.state.r13 = Log.state.r13;
log.rwset.r3 = Log.rwset.r3;
log.rwset.r4 = Log.rwset.r4;
log.rwset.r13 = Log.rwset.r13;
}

DEF_COMMIT(router_4) {
Log.state.r3 = log.state.r3;
Log.state.r4 = log.state.r4;
Log.state.r13 = log.state.r13;
Log.rwset.r3 = log.rwset.r3;
Log.rwset.r4 = log.rwset.r4;
Log.rwset.r13 = log.rwset.r13;
}

DECL_FN(r_send_30, unit)
DEF_FN(r_send_30, unit &_ret, bits<13> value) {
WRITE0(r4, value);
_ret = prims::tt;
return true;
}

DECL_FN(r_send_31, unit)
DEF_FN(r_send_31, unit &_ret, bits<13> value) {
WRITE0(r3, value);
_ret = prims::tt;
return true;
}

DECL_FN(r_receive_6, bits<13>)
DEF_FN(r_receive_6, bits<13> &_ret) {
_ret = READ0(r3);
return true;
}

DECL_FN(r_receive_7, bits<13>)
DEF_FN(r_receive_7, bits<13> &_ret) {
_ret = READ0(r4);
return true;
}

DECL_FN(r_send_32, unit)
DEF_FN(r_send_32, unit &_ret, bits<13> value) {
WRITE0(r3, value);
_ret = prims::tt;
return true;
}

DECL_FN(r_send_33, unit)
DEF_FN(r_send_33, unit &_ret, bits<13> value) {
WRITE0(r4, value);
_ret = prims::tt;
return true;
}

DECL_FN(r_send_34, unit)
DEF_FN(r_send_34, unit &_ret, bits<13> value) {
WRITE0(r3, value);
_ret = prims::tt;
return true;
}

DECL_FN(r_send_35, unit)
DEF_FN(r_send_35, unit &_ret, bits<13> value) {
WRITE0(r13, value);
_ret = prims::tt;
return true;
}

DECL_FN(r_send_36, unit)
DEF_FN(r_send_36, unit &_ret, bits<13> value) {
WRITE0(r4, value);
_ret = prims::tt;
return true;
}

DECL_FN(r_send_37, unit)
DEF_FN(r_send_37, unit &_ret, bits<13> value) {
WRITE0(r4, value);
_ret = prims::tt;
return true;
}

DECL_FN(r_send_38, unit)
DEF_FN(r_send_38, unit &_ret, bits<13> value) {
WRITE0(r3, value);
_ret = prims::tt;
return true;
}

DECL_FN(r_send_39, unit)
DEF_FN(r_send_39, unit &_ret, bits<13> value) {
WRITE0(r13, value);
_ret = prims::tt;
return true;
}
DEF_RULE(router_4) {
bits<4> r_addr = 4'0011_b;
bits<13> m_input = extfuns.extfn_7(13'0_b);
struct_basic_flit msg = prims::unpack<struct_basic_flit>(m_input);
bits<1> new_data = msg.renamed_cppnew;
bits<4> dest = msg.dest;
bits<4> src_p = msg.src;
if ((new_data & ((src_p == r_addr) & (dest > r_addr)))) {
CALL_FN(r_send_30, m_input);
}
else {
if ((new_data & ((src_p == r_addr) & (dest < r_addr)))) {
CALL_FN(r_send_31, m_input);
}
else {
bits<13> m0 = CALL_FN(r_receive_6);
bits<13> m1 = CALL_FN(r_receive_7);
struct_basic_flit msg = prims::unpack<struct_basic_flit>(m0);
bits<1> new_data = msg.renamed_cppnew;
bits<4> src_p = msg.src;
if (((src_p != r_addr) & new_data)) {
struct_basic_flit _x13 = msg;
_x13.renamed_cppnew = 1'0_b;
CALL_FN(r_send_32, prims::pack(_x13));
bits<4> dest = msg.dest;
if ((dest > r_addr)) {
struct_basic_flit _x16 = msg;
_x16.src = r_addr;
CALL_FN(r_send_33, prims::pack(_x16));
}
else {
if ((dest < r_addr)) {
struct_basic_flit _x18 = msg;
_x18.src = r_addr;
CALL_FN(r_send_34, prims::pack(_x18));
}
else {
bits<13> _value5 = extfuns.extfn_8(m0);
CALL_FN(r_send_35, _value5);
}
}
}
/* bind */ {
struct_basic_flit msg = prims::unpack<struct_basic_flit>(m1);
bits<1> new_data = msg.renamed_cppnew;
bits<4> src_p = msg.src;
if (((src_p != r_addr) & new_data)) {
struct_basic_flit _x24 = msg;
_x24.renamed_cppnew = 1'0_b;
CALL_FN(r_send_36, prims::pack(_x24));
bits<4> dest = msg.dest;
if ((dest > r_addr)) {
struct_basic_flit _x27 = msg;
_x27.src = r_addr;
CALL_FN(r_send_37, prims::pack(_x27));
}
else {
if ((dest < r_addr)) {
struct_basic_flit _x29 = msg;
_x29.src = r_addr;
CALL_FN(r_send_38, prims::pack(_x29));
}
else {
bits<13> _value9 = extfuns.extfn_8(m1);
CALL_FN(r_send_39, _value9);
}
}
}
}
}
}

COMMIT();
}
#undef RULE_NAME

#define RULE_NAME router_8
DEF_RESET(router_8) {
log.state.r7 = Log.state.r7;
log.state.r8 = Log.state.r8;
log.state.r17 = Log.state.r17;
log.rwset.r7 = Log.rwset.r7;
log.rwset.r8 = Log.rwset.r8;
log.rwset.r17 = Log.rwset.r17;
}

DEF_COMMIT(router_8) {
Log.state.r7 = log.state.r7;
Log.state.r8 = log.state.r8;
Log.state.r17 = log.state.r17;
Log.rwset.r7 = log.rwset.r7;
Log.rwset.r8 = log.rwset.r8;
Log.rwset.r17 = log.rwset.r17;
}

DECL_FN(r_send_40, unit)
DEF_FN(r_send_40, unit &_ret, bits<13> value) {
WRITE0(r8, value);
_ret = prims::tt;
return true;
}

DECL_FN(r_send_41, unit)
DEF_FN(r_send_41, unit &_ret, bits<13> value) {
WRITE0(r7, value);
_ret = prims::tt;
return true;
}

DECL_FN(r_receive_8, bits<13>)
DEF_FN(r_receive_8, bits<13> &_ret) {
_ret = READ0(r7);
return true;
}

DECL_FN(r_receive_9, bits<13>)
DEF_FN(r_receive_9, bits<13> &_ret) {
_ret = READ0(r8);
return true;
}

DECL_FN(r_send_42, unit)
DEF_FN(r_send_42, unit &_ret, bits<13> value) {
WRITE0(r7, value);
_ret = prims::tt;
return true;
}

DECL_FN(r_send_43, unit)
DEF_FN(r_send_43, unit &_ret, bits<13> value) {
WRITE0(r8, value);
_ret = prims::tt;
return true;
}

DECL_FN(r_send_44, unit)
DEF_FN(r_send_44, unit &_ret, bits<13> value) {
WRITE0(r7, value);
_ret = prims::tt;
return true;
}

DECL_FN(r_send_45, unit)
DEF_FN(r_send_45, unit &_ret, bits<13> value) {
WRITE0(r17, value);
_ret = prims::tt;
return true;
}

DECL_FN(r_send_46, unit)
DEF_FN(r_send_46, unit &_ret, bits<13> value) {
WRITE0(r8, value);
_ret = prims::tt;
return true;
}

DECL_FN(r_send_47, unit)
DEF_FN(r_send_47, unit &_ret, bits<13> value) {
WRITE0(r8, value);
_ret = prims::tt;
return true;
}

DECL_FN(r_send_48, unit)
DEF_FN(r_send_48, unit &_ret, bits<13> value) {
WRITE0(r7, value);
_ret = prims::tt;
return true;
}

DECL_FN(r_send_49, unit)
DEF_FN(r_send_49, unit &_ret, bits<13> value) {
WRITE0(r17, value);
_ret = prims::tt;
return true;
}
DEF_RULE(router_8) {
bits<4> r_addr = 4'0111_b;
bits<13> m_input = extfuns.extfn_15(13'0_b);
struct_basic_flit msg = prims::unpack<struct_basic_flit>(m_input);
bits<1> new_data = msg.renamed_cppnew;
bits<4> dest = msg.dest;
bits<4> src_p = msg.src;
if ((new_data & ((src_p == r_addr) & (dest > r_addr)))) {
CALL_FN(r_send_40, m_input);
}
else {
if ((new_data & ((src_p == r_addr) & (dest < r_addr)))) {
CALL_FN(r_send_41, m_input);
}
else {
bits<13> m0 = CALL_FN(r_receive_8);
bits<13> m1 = CALL_FN(r_receive_9);
struct_basic_flit msg = prims::unpack<struct_basic_flit>(m0);
bits<1> new_data = msg.renamed_cppnew;
bits<4> src_p = msg.src;
if (((src_p != r_addr) & new_data)) {
struct_basic_flit _x13 = msg;
_x13.renamed_cppnew = 1'0_b;
CALL_FN(r_send_42, prims::pack(_x13));
bits<4> dest = msg.dest;
if ((dest > r_addr)) {
struct_basic_flit _x16 = msg;
_x16.src = r_addr;
CALL_FN(r_send_43, prims::pack(_x16));
}
else {
if ((dest < r_addr)) {
struct_basic_flit _x18 = msg;
_x18.src = r_addr;
CALL_FN(r_send_44, prims::pack(_x18));
}
else {
bits<13> _value5 = extfuns.extfn_16(m0);
CALL_FN(r_send_45, _value5);
}
}
}
/* bind */ {
struct_basic_flit msg = prims::unpack<struct_basic_flit>(m1);
bits<1> new_data = msg.renamed_cppnew;
bits<4> src_p = msg.src;
if (((src_p != r_addr) & new_data)) {
struct_basic_flit _x24 = msg;
_x24.renamed_cppnew = 1'0_b;
CALL_FN(r_send_46, prims::pack(_x24));
bits<4> dest = msg.dest;
if ((dest > r_addr)) {
struct_basic_flit _x27 = msg;
_x27.src = r_addr;
CALL_FN(r_send_47, prims::pack(_x27));
}
else {
if ((dest < r_addr)) {
struct_basic_flit _x29 = msg;
_x29.src = r_addr;
CALL_FN(r_send_48, prims::pack(_x29));
}
else {
bits<13> _value9 = extfuns.extfn_16(m1);
CALL_FN(r_send_49, _value9);
}
}
}
}
}
}

COMMIT();
}
#undef RULE_NAME

#define RULE_NAME router_5
DEF_RESET(router_5) {
log.state.r4 = Log.state.r4;
log.state.r5 = Log.state.r5;
log.state.r14 = Log.state.r14;
log.rwset.r4 = Log.rwset.r4;
log.rwset.r5 = Log.rwset.r5;
log.rwset.r14 = Log.rwset.r14;
}

DEF_COMMIT(router_5) {
Log.state.r4 = log.state.r4;
Log.state.r5 = log.state.r5;
Log.state.r14 = log.state.r14;
Log.rwset.r4 = log.rwset.r4;
Log.rwset.r5 = log.rwset.r5;
Log.rwset.r14 = log.rwset.r14;
}

DECL_FN(r_send_50, unit)
DEF_FN(r_send_50, unit &_ret, bits<13> value) {
WRITE0(r5, value);
_ret = prims::tt;
return true;
}

DECL_FN(r_send_51, unit)
DEF_FN(r_send_51, unit &_ret, bits<13> value) {
WRITE0(r4, value);
_ret = prims::tt;
return true;
}

DECL_FN(r_receive_10, bits<13>)
DEF_FN(r_receive_10, bits<13> &_ret) {
_ret = READ0(r4);
return true;
}

DECL_FN(r_receive_11, bits<13>)
DEF_FN(r_receive_11, bits<13> &_ret) {
_ret = READ0(r5);
return true;
}

DECL_FN(r_send_52, unit)
DEF_FN(r_send_52, unit &_ret, bits<13> value) {
WRITE0(r4, value);
_ret = prims::tt;
return true;
}

DECL_FN(r_send_53, unit)
DEF_FN(r_send_53, unit &_ret, bits<13> value) {
WRITE0(r5, value);
_ret = prims::tt;
return true;
}

DECL_FN(r_send_54, unit)
DEF_FN(r_send_54, unit &_ret, bits<13> value) {
WRITE0(r4, value);
_ret = prims::tt;
return true;
}

DECL_FN(r_send_55, unit)
DEF_FN(r_send_55, unit &_ret, bits<13> value) {
WRITE0(r14, value);
_ret = prims::tt;
return true;
}

DECL_FN(r_send_56, unit)
DEF_FN(r_send_56, unit &_ret, bits<13> value) {
WRITE0(r5, value);
_ret = prims::tt;
return true;
}

DECL_FN(r_send_57, unit)
DEF_FN(r_send_57, unit &_ret, bits<13> value) {
WRITE0(r5, value);
_ret = prims::tt;
return true;
}

DECL_FN(r_send_58, unit)
DEF_FN(r_send_58, unit &_ret, bits<13> value) {
WRITE0(r4, value);
_ret = prims::tt;
return true;
}

DECL_FN(r_send_59, unit)
DEF_FN(r_send_59, unit &_ret, bits<13> value) {
WRITE0(r14, value);
_ret = prims::tt;
return true;
}
DEF_RULE(router_5) {
bits<4> r_addr = 4'0100_b;
bits<13> m_input = extfuns.extfn_9(13'0_b);
struct_basic_flit msg = prims::unpack<struct_basic_flit>(m_input);
bits<1> new_data = msg.renamed_cppnew;
bits<4> dest = msg.dest;
bits<4> src_p = msg.src;
if ((new_data & ((src_p == r_addr) & (dest > r_addr)))) {
CALL_FN(r_send_50, m_input);
}
else {
if ((new_data & ((src_p == r_addr) & (dest < r_addr)))) {
CALL_FN(r_send_51, m_input);
}
else {
bits<13> m0 = CALL_FN(r_receive_10);
bits<13> m1 = CALL_FN(r_receive_11);
struct_basic_flit msg = prims::unpack<struct_basic_flit>(m0);
bits<1> new_data = msg.renamed_cppnew;
bits<4> src_p = msg.src;
if (((src_p != r_addr) & new_data)) {
struct_basic_flit _x13 = msg;
_x13.renamed_cppnew = 1'0_b;
CALL_FN(r_send_52, prims::pack(_x13));
bits<4> dest = msg.dest;
if ((dest > r_addr)) {
struct_basic_flit _x16 = msg;
_x16.src = r_addr;
CALL_FN(r_send_53, prims::pack(_x16));
}
else {
if ((dest < r_addr)) {
struct_basic_flit _x18 = msg;
_x18.src = r_addr;
CALL_FN(r_send_54, prims::pack(_x18));
}
else {
bits<13> _value5 = extfuns.extfn_10(m0);
CALL_FN(r_send_55, _value5);
}
}
}
/* bind */ {
struct_basic_flit msg = prims::unpack<struct_basic_flit>(m1);
bits<1> new_data = msg.renamed_cppnew;
bits<4> src_p = msg.src;
if (((src_p != r_addr) & new_data)) {
struct_basic_flit _x24 = msg;
_x24.renamed_cppnew = 1'0_b;
CALL_FN(r_send_56, prims::pack(_x24));
bits<4> dest = msg.dest;
if ((dest > r_addr)) {
struct_basic_flit _x27 = msg;
_x27.src = r_addr;
CALL_FN(r_send_57, prims::pack(_x27));
}
else {
if ((dest < r_addr)) {
struct_basic_flit _x29 = msg;
_x29.src = r_addr;
CALL_FN(r_send_58, prims::pack(_x29));
}
else {
bits<13> _value9 = extfuns.extfn_10(m1);
CALL_FN(r_send_59, _value9);
}
}
}
}
}
}

COMMIT();
}
#undef RULE_NAME

#define RULE_NAME router_6
DEF_RESET(router_6) {
log.state.r5 = Log.state.r5;
log.state.r6 = Log.state.r6;
log.state.r15 = Log.state.r15;
log.rwset.r5 = Log.rwset.r5;
log.rwset.r6 = Log.rwset.r6;
log.rwset.r15 = Log.rwset.r15;
}

DEF_COMMIT(router_6) {
Log.state.r5 = log.state.r5;
Log.state.r6 = log.state.r6;
Log.state.r15 = log.state.r15;
Log.rwset.r5 = log.rwset.r5;
Log.rwset.r6 = log.rwset.r6;
Log.rwset.r15 = log.rwset.r15;
}

DECL_FN(r_send_60, unit)
DEF_FN(r_send_60, unit &_ret, bits<13> value) {
WRITE0(r6, value);
_ret = prims::tt;
return true;
}

DECL_FN(r_send_61, unit)
DEF_FN(r_send_61, unit &_ret, bits<13> value) {
WRITE0(r5, value);
_ret = prims::tt;
return true;
}

DECL_FN(r_receive_12, bits<13>)
DEF_FN(r_receive_12, bits<13> &_ret) {
_ret = READ0(r5);
return true;
}

DECL_FN(r_receive_13, bits<13>)
DEF_FN(r_receive_13, bits<13> &_ret) {
_ret = READ0(r6);
return true;
}

DECL_FN(r_send_62, unit)
DEF_FN(r_send_62, unit &_ret, bits<13> value) {
WRITE0(r5, value);
_ret = prims::tt;
return true;
}

DECL_FN(r_send_63, unit)
DEF_FN(r_send_63, unit &_ret, bits<13> value) {
WRITE0(r6, value);
_ret = prims::tt;
return true;
}

DECL_FN(r_send_64, unit)
DEF_FN(r_send_64, unit &_ret, bits<13> value) {
WRITE0(r5, value);
_ret = prims::tt;
return true;
}

DECL_FN(r_send_65, unit)
DEF_FN(r_send_65, unit &_ret, bits<13> value) {
WRITE0(r15, value);
_ret = prims::tt;
return true;
}

DECL_FN(r_send_66, unit)
DEF_FN(r_send_66, unit &_ret, bits<13> value) {
WRITE0(r6, value);
_ret = prims::tt;
return true;
}

DECL_FN(r_send_67, unit)
DEF_FN(r_send_67, unit &_ret, bits<13> value) {
WRITE0(r6, value);
_ret = prims::tt;
return true;
}

DECL_FN(r_send_68, unit)
DEF_FN(r_send_68, unit &_ret, bits<13> value) {
WRITE0(r5, value);
_ret = prims::tt;
return true;
}

DECL_FN(r_send_69, unit)
DEF_FN(r_send_69, unit &_ret, bits<13> value) {
WRITE0(r15, value);
_ret = prims::tt;
return true;
}
DEF_RULE(router_6) {
bits<4> r_addr = 4'0101_b;
bits<13> m_input = extfuns.extfn_11(13'0_b);
struct_basic_flit msg = prims::unpack<struct_basic_flit>(m_input);
bits<1> new_data = msg.renamed_cppnew;
bits<4> dest = msg.dest;
bits<4> src_p = msg.src;
if ((new_data & ((src_p == r_addr) & (dest > r_addr)))) {
CALL_FN(r_send_60, m_input);
}
else {
if ((new_data & ((src_p == r_addr) & (dest < r_addr)))) {
CALL_FN(r_send_61, m_input);
}
else {
bits<13> m0 = CALL_FN(r_receive_12);
bits<13> m1 = CALL_FN(r_receive_13);
struct_basic_flit msg = prims::unpack<struct_basic_flit>(m0);
bits<1> new_data = msg.renamed_cppnew;
bits<4> src_p = msg.src;
if (((src_p != r_addr) & new_data)) {
struct_basic_flit _x13 = msg;
_x13.renamed_cppnew = 1'0_b;
CALL_FN(r_send_62, prims::pack(_x13));
bits<4> dest = msg.dest;
if ((dest > r_addr)) {
struct_basic_flit _x16 = msg;
_x16.src = r_addr;
CALL_FN(r_send_63, prims::pack(_x16));
}
else {
if ((dest < r_addr)) {
struct_basic_flit _x18 = msg;
_x18.src = r_addr;
CALL_FN(r_send_64, prims::pack(_x18));
}
else {
bits<13> _value5 = extfuns.extfn_12(m0);
CALL_FN(r_send_65, _value5);
}
}
}
/* bind */ {
struct_basic_flit msg = prims::unpack<struct_basic_flit>(m1);
bits<1> new_data = msg.renamed_cppnew;
bits<4> src_p = msg.src;
if (((src_p != r_addr) & new_data)) {
struct_basic_flit _x24 = msg;
_x24.renamed_cppnew = 1'0_b;
CALL_FN(r_send_66, prims::pack(_x24));
bits<4> dest = msg.dest;
if ((dest > r_addr)) {
struct_basic_flit _x27 = msg;
_x27.src = r_addr;
CALL_FN(r_send_67, prims::pack(_x27));
}
else {
if ((dest < r_addr)) {
struct_basic_flit _x29 = msg;
_x29.src = r_addr;
CALL_FN(r_send_68, prims::pack(_x29));
}
else {
bits<13> _value9 = extfuns.extfn_12(m1);
CALL_FN(r_send_69, _value9);
}
}
}
}
}
}

COMMIT();
}
#undef RULE_NAME

#define RULE_NAME router_10
DEF_RESET(router_10) {
log.state.r9 = Log.state.r9;
log.state.r19 = Log.state.r19;
log.rwset.r9 = Log.rwset.r9;
}

DEF_COMMIT(router_10) {
Log.state.r9 = log.state.r9;
Log.state.r19 = log.state.r19;
Log.rwset.r9 = log.rwset.r9;
}

DECL_FN(r_send_70, unit)
DEF_FN(r_send_70, unit &_ret, bits<13> value) {
WRITE0(r9, value);
_ret = prims::tt;
return true;
}

DECL_FN(r_receive_14, bits<13>)
DEF_FN(r_receive_14, bits<13> &_ret) {
_ret = READ0(r9);
return true;
}

DECL_FN(r_send_71, unit)
DEF_FN(r_send_71, unit &_ret, bits<13> value) {
WRITE0(r9, value);
_ret = prims::tt;
return true;
}

DECL_FN(r_send_72, unit)
DEF_FN(r_send_72, unit &_ret, bits<13> value) {
WRITE0_FAST(r19, value);
_ret = prims::tt;
return true;
}
DEF_RULE(router_10) {
bits<4> r_addr = 4'1001_b;
bits<13> m_input = extfuns.extfn_19(13'0_b);
struct_basic_flit msg = prims::unpack<struct_basic_flit>(m_input);
bits<1> new_data = msg.renamed_cppnew;
bits<4> src_p = msg.src;
if ((new_data & (src_p == r_addr))) {
CALL_FN(r_send_70, m_input);
}
else {
bits<13> m0 = CALL_FN(r_receive_14);
struct_basic_flit msg = prims::unpack<struct_basic_flit>(m0);
bits<1> new_data = msg.renamed_cppnew;
bits<4> src_p = msg.src;
if (((src_p != r_addr) & new_data)) {
bits<4> dest = msg.dest;
if ((dest > r_addr)) {
FAIL_FAST();
}
else {
if ((dest < r_addr)) {
struct_basic_flit _x12 = msg;
_x12.src = r_addr;
CALL_FN(r_send_71, prims::pack(_x12));
}
else {
bits<13> _value2 = extfuns.extfn_20(m0);
CALL_FN(r_send_72, _value2);
}
}
}
}

COMMIT();
}
#undef RULE_NAME

#define RULE_NAME router_1
DEF_RESET(router_1) {
log.state.r1 = Log.state.r1;
log.state.r10 = Log.state.r10;
log.rwset.r1 = Log.rwset.r1;
}

DEF_COMMIT(router_1) {
Log.state.r1 = log.state.r1;
Log.state.r10 = log.state.r10;
Log.rwset.r1 = log.rwset.r1;
}

DECL_FN(r_send_73, unit)
DEF_FN(r_send_73, unit &_ret, bits<13> value) {
WRITE0(r1, value);
_ret = prims::tt;
return true;
}

DECL_FN(r_receive_15, bits<13>)
DEF_FN(r_receive_15, bits<13> &_ret) {
_ret = READ0(r1);
return true;
}

DECL_FN(r_send_74, unit)
DEF_FN(r_send_74, unit &_ret, bits<13> value) {
WRITE0(r1, value);
_ret = prims::tt;
return true;
}

DECL_FN(r_send_75, unit)
DEF_FN(r_send_75, unit &_ret, bits<13> value) {
WRITE0_FAST(r10, value);
_ret = prims::tt;
return true;
}
DEF_RULE(router_1) {
bits<4> r_addr = 4'0000_b;
bits<13> m_input = extfuns.extfn_1(13'0_b);
struct_basic_flit msg = prims::unpack<struct_basic_flit>(m_input);
bits<1> new_data = msg.renamed_cppnew;
bits<4> src_p = msg.src;
if ((new_data & (src_p == r_addr))) {
CALL_FN(r_send_73, m_input);
}
else {
bits<13> m0 = CALL_FN(r_receive_15);
struct_basic_flit msg = prims::unpack<struct_basic_flit>(m0);
bits<1> new_data = msg.renamed_cppnew;
bits<4> src_p = msg.src;
if (((src_p != r_addr) & new_data)) {
bits<4> dest = msg.dest;
if ((dest > r_addr)) {
struct_basic_flit _x11 = msg;
_x11.src = r_addr;
CALL_FN(r_send_74, prims::pack(_x11));
}
else {
if ((dest < r_addr)) {
FAIL_FAST();
}
else {
bits<13> _value2 = extfuns.extfn_2(m0);
CALL_FN(r_send_75, _value2);
}
}
}
}

COMMIT();
}
#undef RULE_NAME

#define RULE_NAME router_2
DEF_RESET(router_2) {
log.state.r1 = Log.state.r1;
log.state.r2 = Log.state.r2;
log.state.r11 = Log.state.r11;
log.rwset.r1 = Log.rwset.r1;
log.rwset.r2 = Log.rwset.r2;
log.rwset.r11 = Log.rwset.r11;
}

DEF_COMMIT(router_2) {
Log.state.r1 = log.state.r1;
Log.state.r2 = log.state.r2;
Log.state.r11 = log.state.r11;
Log.rwset.r1 = log.rwset.r1;
Log.rwset.r2 = log.rwset.r2;
Log.rwset.r11 = log.rwset.r11;
}

DECL_FN(r_send_76, unit)
DEF_FN(r_send_76, unit &_ret, bits<13> value) {
WRITE0(r2, value);
_ret = prims::tt;
return true;
}

DECL_FN(r_send_77, unit)
DEF_FN(r_send_77, unit &_ret, bits<13> value) {
WRITE0(r1, value);
_ret = prims::tt;
return true;
}

DECL_FN(r_receive_16, bits<13>)
DEF_FN(r_receive_16, bits<13> &_ret) {
_ret = READ0(r1);
return true;
}

DECL_FN(r_receive_17, bits<13>)
DEF_FN(r_receive_17, bits<13> &_ret) {
_ret = READ0(r2);
return true;
}

DECL_FN(r_send_78, unit)
DEF_FN(r_send_78, unit &_ret, bits<13> value) {
WRITE0(r1, value);
_ret = prims::tt;
return true;
}

DECL_FN(r_send_79, unit)
DEF_FN(r_send_79, unit &_ret, bits<13> value) {
WRITE0(r2, value);
_ret = prims::tt;
return true;
}

DECL_FN(r_send_80, unit)
DEF_FN(r_send_80, unit &_ret, bits<13> value) {
WRITE0(r1, value);
_ret = prims::tt;
return true;
}

DECL_FN(r_send_81, unit)
DEF_FN(r_send_81, unit &_ret, bits<13> value) {
WRITE0(r11, value);
_ret = prims::tt;
return true;
}

DECL_FN(r_send_82, unit)
DEF_FN(r_send_82, unit &_ret, bits<13> value) {
WRITE0(r2, value);
_ret = prims::tt;
return true;
}

DECL_FN(r_send_83, unit)
DEF_FN(r_send_83, unit &_ret, bits<13> value) {
WRITE0(r2, value);
_ret = prims::tt;
return true;
}

DECL_FN(r_send_84, unit)
DEF_FN(r_send_84, unit &_ret, bits<13> value) {
WRITE0(r1, value);
_ret = prims::tt;
return true;
}

DECL_FN(r_send_85, unit)
DEF_FN(r_send_85, unit &_ret, bits<13> value) {
WRITE0(r11, value);
_ret = prims::tt;
return true;
}
DEF_RULE(router_2) {
bits<4> r_addr = 4'0001_b;
bits<13> m_input = extfuns.extfn_3(13'0_b);
struct_basic_flit msg = prims::unpack<struct_basic_flit>(m_input);
bits<1> new_data = msg.renamed_cppnew;
bits<4> dest = msg.dest;
bits<4> src_p = msg.src;
if ((new_data & ((src_p == r_addr) & (dest > r_addr)))) {
CALL_FN(r_send_76, m_input);
}
else {
if ((new_data & ((src_p == r_addr) & (dest < r_addr)))) {
CALL_FN(r_send_77, m_input);
}
else {
bits<13> m0 = CALL_FN(r_receive_16);
bits<13> m1 = CALL_FN(r_receive_17);
struct_basic_flit msg = prims::unpack<struct_basic_flit>(m0);
bits<1> new_data = msg.renamed_cppnew;
bits<4> src_p = msg.src;
if (((src_p != r_addr) & new_data)) {
struct_basic_flit _x13 = msg;
_x13.renamed_cppnew = 1'0_b;
CALL_FN(r_send_78, prims::pack(_x13));
bits<4> dest = msg.dest;
if ((dest > r_addr)) {
struct_basic_flit _x16 = msg;
_x16.src = r_addr;
CALL_FN(r_send_79, prims::pack(_x16));
}
else {
if ((dest < r_addr)) {
struct_basic_flit _x18 = msg;
_x18.src = r_addr;
CALL_FN(r_send_80, prims::pack(_x18));
}
else {
bits<13> _value5 = extfuns.extfn_4(m0);
CALL_FN(r_send_81, _value5);
}
}
}
/* bind */ {
struct_basic_flit msg = prims::unpack<struct_basic_flit>(m1);
bits<1> new_data = msg.renamed_cppnew;
bits<4> src_p = msg.src;
if (((src_p != r_addr) & new_data)) {
struct_basic_flit _x24 = msg;
_x24.renamed_cppnew = 1'0_b;
CALL_FN(r_send_82, prims::pack(_x24));
bits<4> dest = msg.dest;
if ((dest > r_addr)) {
struct_basic_flit _x27 = msg;
_x27.src = r_addr;
CALL_FN(r_send_83, prims::pack(_x27));
}
else {
if ((dest < r_addr)) {
struct_basic_flit _x29 = msg;
_x29.src = r_addr;
CALL_FN(r_send_84, prims::pack(_x29));
}
else {
bits<13> _value9 = extfuns.extfn_4(m1);
CALL_FN(r_send_85, _value9);
}
}
}
}
}
}

COMMIT();
}
#undef RULE_NAME

public:
void finish(cuttlesim::exit_info exit_config, int exit_code) {
meta.finished = true;
meta.exit_config = exit_config;
meta.exit_code = exit_code;
}

bool finished() {
return meta.finished;
}

snapshot_t snapshot() const {
return snapshot_t(Log.snapshot(), meta);
}

static constexpr state_t initial_state() {
state_t init {
.r1 = 13'0_b,
.r2 = 13'0_b,
.r3 = 13'0_b,
.r4 = 13'0_b,
.r5 = 13'0_b,
.r6 = 13'0_b,
.r7 = 13'0_b,
.r8 = 13'0_b,
.r9 = 13'0_b,
.r10 = 13'0_b,
.r11 = 13'0_b,
.r12 = 13'0_b,
.r13 = 13'0_b,
.r14 = 13'0_b,
.r15 = 13'0_b,
.r16 = 13'0_b,
.r17 = 13'0_b,
.r18 = 13'0_b,
.r19 = 13'0_b,
};
return init;
}

explicit module_NoC(const state_t init = initial_state()) : log(init), Log(init), extfuns{}, meta{} {
#ifndef SIM_MINIMAL
rng.seed(cuttlesim::random_seed);
#endif
}

_virtual void strobe() const {}

void cycle() {
meta.cycle_id++;
log.rwset = Log.rwset = rwset_t{};
rule_router_10();
rule_router_9();
rule_router_8();
rule_router_7();
rule_router_6();
rule_router_5();
rule_router_4();
rule_router_3();
rule_router_2();
rule_router_1();
strobe();
}

_flatten module_NoC& run(std::uint_fast64_t ncycles) {
for (std::uint_fast64_t cycle_id = 0;
                cycle_id < ncycles && !meta.finished;
                cycle_id++) {
cycle();
}
return *this;
}

#ifndef SIM_MINIMAL
typedef bool (module_NoC::*rule_ptr)();
void cycle_randomized() {
meta.cycle_id++;
log.rwset = Log.rwset = rwset_t{};
static constexpr rule_ptr rules[10] {
&module_NoC::rule_router_3,
&module_NoC::rule_router_7,
&module_NoC::rule_router_9,
&module_NoC::rule_router_4,
&module_NoC::rule_router_8,
&module_NoC::rule_router_5,
&module_NoC::rule_router_6,
&module_NoC::rule_router_10,
&module_NoC::rule_router_1,
&module_NoC::rule_router_2};
(this->*rules[uniform(rng)])();
strobe();
}

_flatten module_NoC& run_randomized(std::uint_fast64_t ncycles) {
for (std::uint_fast64_t cycle_id = 0;
                cycle_id < ncycles && !meta.finished;
                cycle_id++) {
cycle_randomized();
}
return *this;
}

_flatten module_NoC& trace(std::string fname, std::uint_fast64_t ncycles) {
std::ofstream vcd(fname);
state_t::vcd_header(vcd);
state_t latest = Log.snapshot();
latest.vcd_dumpvars(meta.cycle_id, vcd, latest, true);
for (std::uint_fast64_t cycle_id = 0;
                cycle_id < ncycles && !meta.finished;
                cycle_id++) {
cycle();
state_t current = Log.snapshot();
current.vcd_dumpvars(meta.cycle_id, vcd, latest, false);
latest = current;
}
return *this;
}

_flatten module_NoC& trace_randomized(std::string fname, std::uint_fast64_t ncycles) {
std::ofstream vcd(fname);
state_t::vcd_header(vcd);
state_t latest = Log.snapshot();
latest.vcd_dumpvars(meta.cycle_id, vcd, latest, true);
for (std::uint_fast64_t cycle_id = 0;
                cycle_id < ncycles && !meta.finished;
                cycle_id++) {
cycle_randomized();
state_t current = Log.snapshot();
current.vcd_dumpvars(meta.cycle_id, vcd, latest, false);
latest = current;
}
return *this;
}
#endif
};

#endif
