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
bits<3> src;
bits<3> dest;
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
static constexpr prims::bitwidth size = 11;
};

template <> _unused bits<11> pack<>(const struct_basic_flit val) {
bits<11> packed = 11'0_b;
packed |= prims::widen<11>(val.renamed_cppnew);
packed <<= 3;
packed |= prims::widen<11>(val.src);
packed <<= 3;
packed |= prims::widen<11>(val.dest);
packed <<= 4;
packed |= prims::widen<11>(val.data);
return packed;
}

template <> struct _unpack<struct_basic_flit, 11> {
static struct_basic_flit unpack(const bits<11> bs) {
struct_basic_flit unpacked = {};
unpacked.data = prims::truncate<4>(bs >> 0u);
unpacked.dest = prims::truncate<3>(bs >> 4u);
unpacked.src = prims::truncate<3>(bs >> 7u);
unpacked.renamed_cppnew = prims::truncate<1>(bs >> 10u);
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
bits<11> r1;
bits<11> r2;
bits<11> r3;
bits<11> r4;
bits<11> r5;
bits<11> r6;
bits<11> r7;
bits<11> r8;
bits<11> r9;
bits<11> r10;
bits<11> r11;
bits<11> r12;
bits<11> r13;

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
}

static _unused void vcd_header(std::ostream& os) {
#ifndef SIM_VCD_SCOPES
#define SIM_VCD_SCOPES { "TOP", "NoC" }
#endif
cuttlesim::vcd::begin_header(os, SIM_VCD_SCOPES);
cuttlesim::vcd::var(os, "r1", 11);
cuttlesim::vcd::var(os, "r2", 11);
cuttlesim::vcd::var(os, "r3", 11);
cuttlesim::vcd::var(os, "r4", 11);
cuttlesim::vcd::var(os, "r5", 11);
cuttlesim::vcd::var(os, "r6", 11);
cuttlesim::vcd::var(os, "r7", 11);
cuttlesim::vcd::var(os, "r8", 11);
cuttlesim::vcd::var(os, "r9", 11);
cuttlesim::vcd::var(os, "r10", 11);
cuttlesim::vcd::var(os, "r11", 11);
cuttlesim::vcd::var(os, "r12", 11);
cuttlesim::vcd::var(os, "r13", 11);
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
}

std::uint_fast64_t vcd_readvars(_unused std::istream& is) {
std::string var{}, val{};
std::uint_fast64_t cycle_id = std::numeric_limits<std::uint_fast64_t>::max();
cuttlesim::vcd::read_header(is);
while (cuttlesim::vcd::readvar(is, cycle_id, var, val)) {
if (var == "r1") {
r1 = prims::unpack<bits<11>>(bits<11>::of_str(val));
}
else if (var == "r2") {
r2 = prims::unpack<bits<11>>(bits<11>::of_str(val));
}
else if (var == "r3") {
r3 = prims::unpack<bits<11>>(bits<11>::of_str(val));
}
else if (var == "r4") {
r4 = prims::unpack<bits<11>>(bits<11>::of_str(val));
}
else if (var == "r5") {
r5 = prims::unpack<bits<11>>(bits<11>::of_str(val));
}
else if (var == "r6") {
r6 = prims::unpack<bits<11>>(bits<11>::of_str(val));
}
else if (var == "r7") {
r7 = prims::unpack<bits<11>>(bits<11>::of_str(val));
}
else if (var == "r8") {
r8 = prims::unpack<bits<11>>(bits<11>::of_str(val));
}
else if (var == "r9") {
r9 = prims::unpack<bits<11>>(bits<11>::of_str(val));
}
else if (var == "r10") {
r10 = prims::unpack<bits<11>>(bits<11>::of_str(val));
}
else if (var == "r11") {
r11 = prims::unpack<bits<11>>(bits<11>::of_str(val));
}
else if (var == "r12") {
r12 = prims::unpack<bits<11>>(bits<11>::of_str(val));
}
else if (var == "r13") {
r13 = prims::unpack<bits<11>>(bits<11>::of_str(val));
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
cuttlesim::reg_rwset r8;
cuttlesim::reg_rwset r9;
cuttlesim::reg_rwset r10;
cuttlesim::reg_rwset r11;
cuttlesim::reg_rwset r12;
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
std::uniform_int_distribution<int> uniform{0, 6};
#endif

#define RULE_NAME router_3
DEF_RESET(router_3) {
log.state.r2 = Log.state.r2;
log.state.r3 = Log.state.r3;
log.state.r9 = Log.state.r9;
log.rwset.r2 = Log.rwset.r2;
log.rwset.r3 = Log.rwset.r3;
log.rwset.r9 = Log.rwset.r9;
}

DEF_COMMIT(router_3) {
Log.state.r2 = log.state.r2;
Log.state.r3 = log.state.r3;
Log.state.r9 = log.state.r9;
Log.rwset.r2 = log.rwset.r2;
Log.rwset.r3 = log.rwset.r3;
Log.rwset.r9 = log.rwset.r9;
}

DECL_FN(r_send_0, unit)
DEF_FN(r_send_0, unit &_ret, bits<11> value) {
WRITE0(r3, value);
_ret = prims::tt;
return true;
}

DECL_FN(r_send_1, unit)
DEF_FN(r_send_1, unit &_ret, bits<11> value) {
WRITE0(r2, value);
_ret = prims::tt;
return true;
}

DECL_FN(r_receive_0, bits<11>)
DEF_FN(r_receive_0, bits<11> &_ret) {
_ret = READ0(r2);
return true;
}

DECL_FN(r_receive_1, bits<11>)
DEF_FN(r_receive_1, bits<11> &_ret) {
_ret = READ0(r3);
return true;
}

DECL_FN(r_send_2, unit)
DEF_FN(r_send_2, unit &_ret, bits<11> value) {
WRITE0(r2, value);
_ret = prims::tt;
return true;
}

DECL_FN(r_send_3, unit)
DEF_FN(r_send_3, unit &_ret, bits<11> value) {
WRITE0(r3, value);
_ret = prims::tt;
return true;
}

DECL_FN(r_send_4, unit)
DEF_FN(r_send_4, unit &_ret, bits<11> value) {
WRITE0(r2, value);
_ret = prims::tt;
return true;
}

DECL_FN(r_send_5, unit)
DEF_FN(r_send_5, unit &_ret, bits<11> value) {
WRITE0(r9, value);
_ret = prims::tt;
return true;
}

DECL_FN(r_send_6, unit)
DEF_FN(r_send_6, unit &_ret, bits<11> value) {
WRITE0(r3, value);
_ret = prims::tt;
return true;
}

DECL_FN(r_send_7, unit)
DEF_FN(r_send_7, unit &_ret, bits<11> value) {
WRITE0(r3, value);
_ret = prims::tt;
return true;
}

DECL_FN(r_send_8, unit)
DEF_FN(r_send_8, unit &_ret, bits<11> value) {
WRITE0(r2, value);
_ret = prims::tt;
return true;
}

DECL_FN(r_send_9, unit)
DEF_FN(r_send_9, unit &_ret, bits<11> value) {
WRITE0(r9, value);
_ret = prims::tt;
return true;
}
DEF_RULE(router_3) {
bits<3> r_addr = 3'010_b;
bits<11> m_input = extfuns.extfn_5(11'0_b);
struct_basic_flit msg = prims::unpack<struct_basic_flit>(m_input);
bits<1> new_data = msg.renamed_cppnew;
bits<3> dest = msg.dest;
bits<3> src_p = msg.src;
if ((new_data & ((src_p == r_addr) & (dest > r_addr)))) {
CALL_FN(r_send_0, m_input);
}
else {
if ((new_data & ((src_p == r_addr) & (dest < r_addr)))) {
CALL_FN(r_send_1, m_input);
}
else {
bits<11> m0 = CALL_FN(r_receive_0);
bits<11> m1 = CALL_FN(r_receive_1);
struct_basic_flit msg = prims::unpack<struct_basic_flit>(m0);
bits<1> new_data = msg.renamed_cppnew;
bits<3> src_p = msg.src;
if (((src_p != r_addr) & new_data)) {
struct_basic_flit _x13 = msg;
_x13.renamed_cppnew = 1'0_b;
CALL_FN(r_send_2, prims::pack(_x13));
bits<3> dest = msg.dest;
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
bits<11> _value5 = extfuns.extfn_6(m0);
CALL_FN(r_send_5, _value5);
}
}
}
/* bind */ {
struct_basic_flit msg = prims::unpack<struct_basic_flit>(m1);
bits<1> new_data = msg.renamed_cppnew;
bits<3> src_p = msg.src;
if (((src_p != r_addr) & new_data)) {
struct_basic_flit _x24 = msg;
_x24.renamed_cppnew = 1'0_b;
CALL_FN(r_send_6, prims::pack(_x24));
bits<3> dest = msg.dest;
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
bits<11> _value9 = extfuns.extfn_6(m1);
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
log.state.r13 = Log.state.r13;
log.rwset.r6 = Log.rwset.r6;
}

DEF_COMMIT(router_7) {
Log.state.r6 = log.state.r6;
Log.state.r13 = log.state.r13;
Log.rwset.r6 = log.rwset.r6;
}

DECL_FN(r_send_10, unit)
DEF_FN(r_send_10, unit &_ret, bits<11> value) {
WRITE0(r6, value);
_ret = prims::tt;
return true;
}

DECL_FN(r_receive_2, bits<11>)
DEF_FN(r_receive_2, bits<11> &_ret) {
_ret = READ0(r6);
return true;
}

DECL_FN(r_send_11, unit)
DEF_FN(r_send_11, unit &_ret, bits<11> value) {
WRITE0(r6, value);
_ret = prims::tt;
return true;
}

DECL_FN(r_send_12, unit)
DEF_FN(r_send_12, unit &_ret, bits<11> value) {
WRITE0_FAST(r13, value);
_ret = prims::tt;
return true;
}
DEF_RULE(router_7) {
bits<3> r_addr = 3'110_b;
bits<11> m_input = extfuns.extfn_13(11'0_b);
struct_basic_flit msg = prims::unpack<struct_basic_flit>(m_input);
bits<1> new_data = msg.renamed_cppnew;
bits<3> src_p = msg.src;
if ((new_data & (src_p == r_addr))) {
CALL_FN(r_send_10, m_input);
}
else {
bits<11> m0 = CALL_FN(r_receive_2);
struct_basic_flit msg = prims::unpack<struct_basic_flit>(m0);
bits<1> new_data = msg.renamed_cppnew;
bits<3> src_p = msg.src;
if (((src_p != r_addr) & new_data)) {
bits<3> dest = msg.dest;
if ((dest > r_addr)) {
FAIL_FAST();
}
else {
if ((dest < r_addr)) {
struct_basic_flit _x12 = msg;
_x12.src = r_addr;
CALL_FN(r_send_11, prims::pack(_x12));
}
else {
bits<11> _value2 = extfuns.extfn_14(m0);
CALL_FN(r_send_12, _value2);
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
log.state.r10 = Log.state.r10;
log.rwset.r3 = Log.rwset.r3;
log.rwset.r4 = Log.rwset.r4;
log.rwset.r10 = Log.rwset.r10;
}

DEF_COMMIT(router_4) {
Log.state.r3 = log.state.r3;
Log.state.r4 = log.state.r4;
Log.state.r10 = log.state.r10;
Log.rwset.r3 = log.rwset.r3;
Log.rwset.r4 = log.rwset.r4;
Log.rwset.r10 = log.rwset.r10;
}

DECL_FN(r_send_13, unit)
DEF_FN(r_send_13, unit &_ret, bits<11> value) {
WRITE0(r4, value);
_ret = prims::tt;
return true;
}

DECL_FN(r_send_14, unit)
DEF_FN(r_send_14, unit &_ret, bits<11> value) {
WRITE0(r3, value);
_ret = prims::tt;
return true;
}

DECL_FN(r_receive_3, bits<11>)
DEF_FN(r_receive_3, bits<11> &_ret) {
_ret = READ0(r3);
return true;
}

DECL_FN(r_receive_4, bits<11>)
DEF_FN(r_receive_4, bits<11> &_ret) {
_ret = READ0(r4);
return true;
}

DECL_FN(r_send_15, unit)
DEF_FN(r_send_15, unit &_ret, bits<11> value) {
WRITE0(r3, value);
_ret = prims::tt;
return true;
}

DECL_FN(r_send_16, unit)
DEF_FN(r_send_16, unit &_ret, bits<11> value) {
WRITE0(r4, value);
_ret = prims::tt;
return true;
}

DECL_FN(r_send_17, unit)
DEF_FN(r_send_17, unit &_ret, bits<11> value) {
WRITE0(r3, value);
_ret = prims::tt;
return true;
}

DECL_FN(r_send_18, unit)
DEF_FN(r_send_18, unit &_ret, bits<11> value) {
WRITE0(r10, value);
_ret = prims::tt;
return true;
}

DECL_FN(r_send_19, unit)
DEF_FN(r_send_19, unit &_ret, bits<11> value) {
WRITE0(r4, value);
_ret = prims::tt;
return true;
}

DECL_FN(r_send_20, unit)
DEF_FN(r_send_20, unit &_ret, bits<11> value) {
WRITE0(r4, value);
_ret = prims::tt;
return true;
}

DECL_FN(r_send_21, unit)
DEF_FN(r_send_21, unit &_ret, bits<11> value) {
WRITE0(r3, value);
_ret = prims::tt;
return true;
}

DECL_FN(r_send_22, unit)
DEF_FN(r_send_22, unit &_ret, bits<11> value) {
WRITE0(r10, value);
_ret = prims::tt;
return true;
}
DEF_RULE(router_4) {
bits<3> r_addr = 3'011_b;
bits<11> m_input = extfuns.extfn_7(11'0_b);
struct_basic_flit msg = prims::unpack<struct_basic_flit>(m_input);
bits<1> new_data = msg.renamed_cppnew;
bits<3> dest = msg.dest;
bits<3> src_p = msg.src;
if ((new_data & ((src_p == r_addr) & (dest > r_addr)))) {
CALL_FN(r_send_13, m_input);
}
else {
if ((new_data & ((src_p == r_addr) & (dest < r_addr)))) {
CALL_FN(r_send_14, m_input);
}
else {
bits<11> m0 = CALL_FN(r_receive_3);
bits<11> m1 = CALL_FN(r_receive_4);
struct_basic_flit msg = prims::unpack<struct_basic_flit>(m0);
bits<1> new_data = msg.renamed_cppnew;
bits<3> src_p = msg.src;
if (((src_p != r_addr) & new_data)) {
struct_basic_flit _x13 = msg;
_x13.renamed_cppnew = 1'0_b;
CALL_FN(r_send_15, prims::pack(_x13));
bits<3> dest = msg.dest;
if ((dest > r_addr)) {
struct_basic_flit _x16 = msg;
_x16.src = r_addr;
CALL_FN(r_send_16, prims::pack(_x16));
}
else {
if ((dest < r_addr)) {
struct_basic_flit _x18 = msg;
_x18.src = r_addr;
CALL_FN(r_send_17, prims::pack(_x18));
}
else {
bits<11> _value5 = extfuns.extfn_8(m0);
CALL_FN(r_send_18, _value5);
}
}
}
/* bind */ {
struct_basic_flit msg = prims::unpack<struct_basic_flit>(m1);
bits<1> new_data = msg.renamed_cppnew;
bits<3> src_p = msg.src;
if (((src_p != r_addr) & new_data)) {
struct_basic_flit _x24 = msg;
_x24.renamed_cppnew = 1'0_b;
CALL_FN(r_send_19, prims::pack(_x24));
bits<3> dest = msg.dest;
if ((dest > r_addr)) {
struct_basic_flit _x27 = msg;
_x27.src = r_addr;
CALL_FN(r_send_20, prims::pack(_x27));
}
else {
if ((dest < r_addr)) {
struct_basic_flit _x29 = msg;
_x29.src = r_addr;
CALL_FN(r_send_21, prims::pack(_x29));
}
else {
bits<11> _value9 = extfuns.extfn_8(m1);
CALL_FN(r_send_22, _value9);
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
log.state.r11 = Log.state.r11;
log.rwset.r4 = Log.rwset.r4;
log.rwset.r5 = Log.rwset.r5;
log.rwset.r11 = Log.rwset.r11;
}

DEF_COMMIT(router_5) {
Log.state.r4 = log.state.r4;
Log.state.r5 = log.state.r5;
Log.state.r11 = log.state.r11;
Log.rwset.r4 = log.rwset.r4;
Log.rwset.r5 = log.rwset.r5;
Log.rwset.r11 = log.rwset.r11;
}

DECL_FN(r_send_23, unit)
DEF_FN(r_send_23, unit &_ret, bits<11> value) {
WRITE0(r5, value);
_ret = prims::tt;
return true;
}

DECL_FN(r_send_24, unit)
DEF_FN(r_send_24, unit &_ret, bits<11> value) {
WRITE0(r4, value);
_ret = prims::tt;
return true;
}

DECL_FN(r_receive_5, bits<11>)
DEF_FN(r_receive_5, bits<11> &_ret) {
_ret = READ0(r4);
return true;
}

DECL_FN(r_receive_6, bits<11>)
DEF_FN(r_receive_6, bits<11> &_ret) {
_ret = READ0(r5);
return true;
}

DECL_FN(r_send_25, unit)
DEF_FN(r_send_25, unit &_ret, bits<11> value) {
WRITE0(r4, value);
_ret = prims::tt;
return true;
}

DECL_FN(r_send_26, unit)
DEF_FN(r_send_26, unit &_ret, bits<11> value) {
WRITE0(r5, value);
_ret = prims::tt;
return true;
}

DECL_FN(r_send_27, unit)
DEF_FN(r_send_27, unit &_ret, bits<11> value) {
WRITE0(r4, value);
_ret = prims::tt;
return true;
}

DECL_FN(r_send_28, unit)
DEF_FN(r_send_28, unit &_ret, bits<11> value) {
WRITE0(r11, value);
_ret = prims::tt;
return true;
}

DECL_FN(r_send_29, unit)
DEF_FN(r_send_29, unit &_ret, bits<11> value) {
WRITE0(r5, value);
_ret = prims::tt;
return true;
}

DECL_FN(r_send_30, unit)
DEF_FN(r_send_30, unit &_ret, bits<11> value) {
WRITE0(r5, value);
_ret = prims::tt;
return true;
}

DECL_FN(r_send_31, unit)
DEF_FN(r_send_31, unit &_ret, bits<11> value) {
WRITE0(r4, value);
_ret = prims::tt;
return true;
}

DECL_FN(r_send_32, unit)
DEF_FN(r_send_32, unit &_ret, bits<11> value) {
WRITE0(r11, value);
_ret = prims::tt;
return true;
}
DEF_RULE(router_5) {
bits<3> r_addr = 3'100_b;
bits<11> m_input = extfuns.extfn_9(11'0_b);
struct_basic_flit msg = prims::unpack<struct_basic_flit>(m_input);
bits<1> new_data = msg.renamed_cppnew;
bits<3> dest = msg.dest;
bits<3> src_p = msg.src;
if ((new_data & ((src_p == r_addr) & (dest > r_addr)))) {
CALL_FN(r_send_23, m_input);
}
else {
if ((new_data & ((src_p == r_addr) & (dest < r_addr)))) {
CALL_FN(r_send_24, m_input);
}
else {
bits<11> m0 = CALL_FN(r_receive_5);
bits<11> m1 = CALL_FN(r_receive_6);
struct_basic_flit msg = prims::unpack<struct_basic_flit>(m0);
bits<1> new_data = msg.renamed_cppnew;
bits<3> src_p = msg.src;
if (((src_p != r_addr) & new_data)) {
struct_basic_flit _x13 = msg;
_x13.renamed_cppnew = 1'0_b;
CALL_FN(r_send_25, prims::pack(_x13));
bits<3> dest = msg.dest;
if ((dest > r_addr)) {
struct_basic_flit _x16 = msg;
_x16.src = r_addr;
CALL_FN(r_send_26, prims::pack(_x16));
}
else {
if ((dest < r_addr)) {
struct_basic_flit _x18 = msg;
_x18.src = r_addr;
CALL_FN(r_send_27, prims::pack(_x18));
}
else {
bits<11> _value5 = extfuns.extfn_10(m0);
CALL_FN(r_send_28, _value5);
}
}
}
/* bind */ {
struct_basic_flit msg = prims::unpack<struct_basic_flit>(m1);
bits<1> new_data = msg.renamed_cppnew;
bits<3> src_p = msg.src;
if (((src_p != r_addr) & new_data)) {
struct_basic_flit _x24 = msg;
_x24.renamed_cppnew = 1'0_b;
CALL_FN(r_send_29, prims::pack(_x24));
bits<3> dest = msg.dest;
if ((dest > r_addr)) {
struct_basic_flit _x27 = msg;
_x27.src = r_addr;
CALL_FN(r_send_30, prims::pack(_x27));
}
else {
if ((dest < r_addr)) {
struct_basic_flit _x29 = msg;
_x29.src = r_addr;
CALL_FN(r_send_31, prims::pack(_x29));
}
else {
bits<11> _value9 = extfuns.extfn_10(m1);
CALL_FN(r_send_32, _value9);
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
log.state.r12 = Log.state.r12;
log.rwset.r5 = Log.rwset.r5;
log.rwset.r6 = Log.rwset.r6;
log.rwset.r12 = Log.rwset.r12;
}

DEF_COMMIT(router_6) {
Log.state.r5 = log.state.r5;
Log.state.r6 = log.state.r6;
Log.state.r12 = log.state.r12;
Log.rwset.r5 = log.rwset.r5;
Log.rwset.r6 = log.rwset.r6;
Log.rwset.r12 = log.rwset.r12;
}

DECL_FN(r_send_33, unit)
DEF_FN(r_send_33, unit &_ret, bits<11> value) {
WRITE0(r6, value);
_ret = prims::tt;
return true;
}

DECL_FN(r_send_34, unit)
DEF_FN(r_send_34, unit &_ret, bits<11> value) {
WRITE0(r5, value);
_ret = prims::tt;
return true;
}

DECL_FN(r_receive_7, bits<11>)
DEF_FN(r_receive_7, bits<11> &_ret) {
_ret = READ0(r5);
return true;
}

DECL_FN(r_receive_8, bits<11>)
DEF_FN(r_receive_8, bits<11> &_ret) {
_ret = READ0(r6);
return true;
}

DECL_FN(r_send_35, unit)
DEF_FN(r_send_35, unit &_ret, bits<11> value) {
WRITE0(r5, value);
_ret = prims::tt;
return true;
}

DECL_FN(r_send_36, unit)
DEF_FN(r_send_36, unit &_ret, bits<11> value) {
WRITE0(r6, value);
_ret = prims::tt;
return true;
}

DECL_FN(r_send_37, unit)
DEF_FN(r_send_37, unit &_ret, bits<11> value) {
WRITE0(r5, value);
_ret = prims::tt;
return true;
}

DECL_FN(r_send_38, unit)
DEF_FN(r_send_38, unit &_ret, bits<11> value) {
WRITE0(r12, value);
_ret = prims::tt;
return true;
}

DECL_FN(r_send_39, unit)
DEF_FN(r_send_39, unit &_ret, bits<11> value) {
WRITE0(r6, value);
_ret = prims::tt;
return true;
}

DECL_FN(r_send_40, unit)
DEF_FN(r_send_40, unit &_ret, bits<11> value) {
WRITE0(r6, value);
_ret = prims::tt;
return true;
}

DECL_FN(r_send_41, unit)
DEF_FN(r_send_41, unit &_ret, bits<11> value) {
WRITE0(r5, value);
_ret = prims::tt;
return true;
}

DECL_FN(r_send_42, unit)
DEF_FN(r_send_42, unit &_ret, bits<11> value) {
WRITE0(r12, value);
_ret = prims::tt;
return true;
}
DEF_RULE(router_6) {
bits<3> r_addr = 3'101_b;
bits<11> m_input = extfuns.extfn_11(11'0_b);
struct_basic_flit msg = prims::unpack<struct_basic_flit>(m_input);
bits<1> new_data = msg.renamed_cppnew;
bits<3> dest = msg.dest;
bits<3> src_p = msg.src;
if ((new_data & ((src_p == r_addr) & (dest > r_addr)))) {
CALL_FN(r_send_33, m_input);
}
else {
if ((new_data & ((src_p == r_addr) & (dest < r_addr)))) {
CALL_FN(r_send_34, m_input);
}
else {
bits<11> m0 = CALL_FN(r_receive_7);
bits<11> m1 = CALL_FN(r_receive_8);
struct_basic_flit msg = prims::unpack<struct_basic_flit>(m0);
bits<1> new_data = msg.renamed_cppnew;
bits<3> src_p = msg.src;
if (((src_p != r_addr) & new_data)) {
struct_basic_flit _x13 = msg;
_x13.renamed_cppnew = 1'0_b;
CALL_FN(r_send_35, prims::pack(_x13));
bits<3> dest = msg.dest;
if ((dest > r_addr)) {
struct_basic_flit _x16 = msg;
_x16.src = r_addr;
CALL_FN(r_send_36, prims::pack(_x16));
}
else {
if ((dest < r_addr)) {
struct_basic_flit _x18 = msg;
_x18.src = r_addr;
CALL_FN(r_send_37, prims::pack(_x18));
}
else {
bits<11> _value5 = extfuns.extfn_12(m0);
CALL_FN(r_send_38, _value5);
}
}
}
/* bind */ {
struct_basic_flit msg = prims::unpack<struct_basic_flit>(m1);
bits<1> new_data = msg.renamed_cppnew;
bits<3> src_p = msg.src;
if (((src_p != r_addr) & new_data)) {
struct_basic_flit _x24 = msg;
_x24.renamed_cppnew = 1'0_b;
CALL_FN(r_send_39, prims::pack(_x24));
bits<3> dest = msg.dest;
if ((dest > r_addr)) {
struct_basic_flit _x27 = msg;
_x27.src = r_addr;
CALL_FN(r_send_40, prims::pack(_x27));
}
else {
if ((dest < r_addr)) {
struct_basic_flit _x29 = msg;
_x29.src = r_addr;
CALL_FN(r_send_41, prims::pack(_x29));
}
else {
bits<11> _value9 = extfuns.extfn_12(m1);
CALL_FN(r_send_42, _value9);
}
}
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
log.state.r7 = Log.state.r7;
log.rwset.r1 = Log.rwset.r1;
}

DEF_COMMIT(router_1) {
Log.state.r1 = log.state.r1;
Log.state.r7 = log.state.r7;
Log.rwset.r1 = log.rwset.r1;
}

DECL_FN(r_send_43, unit)
DEF_FN(r_send_43, unit &_ret, bits<11> value) {
WRITE0(r1, value);
_ret = prims::tt;
return true;
}

DECL_FN(r_receive_9, bits<11>)
DEF_FN(r_receive_9, bits<11> &_ret) {
_ret = READ0(r1);
return true;
}

DECL_FN(r_send_44, unit)
DEF_FN(r_send_44, unit &_ret, bits<11> value) {
WRITE0(r1, value);
_ret = prims::tt;
return true;
}

DECL_FN(r_send_45, unit)
DEF_FN(r_send_45, unit &_ret, bits<11> value) {
WRITE0_FAST(r7, value);
_ret = prims::tt;
return true;
}
DEF_RULE(router_1) {
bits<3> r_addr = 3'000_b;
bits<11> m_input = extfuns.extfn_1(11'0_b);
struct_basic_flit msg = prims::unpack<struct_basic_flit>(m_input);
bits<1> new_data = msg.renamed_cppnew;
bits<3> src_p = msg.src;
if ((new_data & (src_p == r_addr))) {
CALL_FN(r_send_43, m_input);
}
else {
bits<11> m0 = CALL_FN(r_receive_9);
struct_basic_flit msg = prims::unpack<struct_basic_flit>(m0);
bits<1> new_data = msg.renamed_cppnew;
bits<3> src_p = msg.src;
if (((src_p != r_addr) & new_data)) {
bits<3> dest = msg.dest;
if ((dest > r_addr)) {
struct_basic_flit _x11 = msg;
_x11.src = r_addr;
CALL_FN(r_send_44, prims::pack(_x11));
}
else {
if ((dest < r_addr)) {
FAIL_FAST();
}
else {
bits<11> _value2 = extfuns.extfn_2(m0);
CALL_FN(r_send_45, _value2);
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
log.state.r8 = Log.state.r8;
log.rwset.r1 = Log.rwset.r1;
log.rwset.r2 = Log.rwset.r2;
log.rwset.r8 = Log.rwset.r8;
}

DEF_COMMIT(router_2) {
Log.state.r1 = log.state.r1;
Log.state.r2 = log.state.r2;
Log.state.r8 = log.state.r8;
Log.rwset.r1 = log.rwset.r1;
Log.rwset.r2 = log.rwset.r2;
Log.rwset.r8 = log.rwset.r8;
}

DECL_FN(r_send_46, unit)
DEF_FN(r_send_46, unit &_ret, bits<11> value) {
WRITE0(r2, value);
_ret = prims::tt;
return true;
}

DECL_FN(r_send_47, unit)
DEF_FN(r_send_47, unit &_ret, bits<11> value) {
WRITE0(r1, value);
_ret = prims::tt;
return true;
}

DECL_FN(r_receive_10, bits<11>)
DEF_FN(r_receive_10, bits<11> &_ret) {
_ret = READ0(r1);
return true;
}

DECL_FN(r_receive_11, bits<11>)
DEF_FN(r_receive_11, bits<11> &_ret) {
_ret = READ0(r2);
return true;
}

DECL_FN(r_send_48, unit)
DEF_FN(r_send_48, unit &_ret, bits<11> value) {
WRITE0(r1, value);
_ret = prims::tt;
return true;
}

DECL_FN(r_send_49, unit)
DEF_FN(r_send_49, unit &_ret, bits<11> value) {
WRITE0(r2, value);
_ret = prims::tt;
return true;
}

DECL_FN(r_send_50, unit)
DEF_FN(r_send_50, unit &_ret, bits<11> value) {
WRITE0(r1, value);
_ret = prims::tt;
return true;
}

DECL_FN(r_send_51, unit)
DEF_FN(r_send_51, unit &_ret, bits<11> value) {
WRITE0(r8, value);
_ret = prims::tt;
return true;
}

DECL_FN(r_send_52, unit)
DEF_FN(r_send_52, unit &_ret, bits<11> value) {
WRITE0(r2, value);
_ret = prims::tt;
return true;
}

DECL_FN(r_send_53, unit)
DEF_FN(r_send_53, unit &_ret, bits<11> value) {
WRITE0(r2, value);
_ret = prims::tt;
return true;
}

DECL_FN(r_send_54, unit)
DEF_FN(r_send_54, unit &_ret, bits<11> value) {
WRITE0(r1, value);
_ret = prims::tt;
return true;
}

DECL_FN(r_send_55, unit)
DEF_FN(r_send_55, unit &_ret, bits<11> value) {
WRITE0(r8, value);
_ret = prims::tt;
return true;
}
DEF_RULE(router_2) {
bits<3> r_addr = 3'001_b;
bits<11> m_input = extfuns.extfn_3(11'0_b);
struct_basic_flit msg = prims::unpack<struct_basic_flit>(m_input);
bits<1> new_data = msg.renamed_cppnew;
bits<3> dest = msg.dest;
bits<3> src_p = msg.src;
if ((new_data & ((src_p == r_addr) & (dest > r_addr)))) {
CALL_FN(r_send_46, m_input);
}
else {
if ((new_data & ((src_p == r_addr) & (dest < r_addr)))) {
CALL_FN(r_send_47, m_input);
}
else {
bits<11> m0 = CALL_FN(r_receive_10);
bits<11> m1 = CALL_FN(r_receive_11);
struct_basic_flit msg = prims::unpack<struct_basic_flit>(m0);
bits<1> new_data = msg.renamed_cppnew;
bits<3> src_p = msg.src;
if (((src_p != r_addr) & new_data)) {
struct_basic_flit _x13 = msg;
_x13.renamed_cppnew = 1'0_b;
CALL_FN(r_send_48, prims::pack(_x13));
bits<3> dest = msg.dest;
if ((dest > r_addr)) {
struct_basic_flit _x16 = msg;
_x16.src = r_addr;
CALL_FN(r_send_49, prims::pack(_x16));
}
else {
if ((dest < r_addr)) {
struct_basic_flit _x18 = msg;
_x18.src = r_addr;
CALL_FN(r_send_50, prims::pack(_x18));
}
else {
bits<11> _value5 = extfuns.extfn_4(m0);
CALL_FN(r_send_51, _value5);
}
}
}
/* bind */ {
struct_basic_flit msg = prims::unpack<struct_basic_flit>(m1);
bits<1> new_data = msg.renamed_cppnew;
bits<3> src_p = msg.src;
if (((src_p != r_addr) & new_data)) {
struct_basic_flit _x24 = msg;
_x24.renamed_cppnew = 1'0_b;
CALL_FN(r_send_52, prims::pack(_x24));
bits<3> dest = msg.dest;
if ((dest > r_addr)) {
struct_basic_flit _x27 = msg;
_x27.src = r_addr;
CALL_FN(r_send_53, prims::pack(_x27));
}
else {
if ((dest < r_addr)) {
struct_basic_flit _x29 = msg;
_x29.src = r_addr;
CALL_FN(r_send_54, prims::pack(_x29));
}
else {
bits<11> _value9 = extfuns.extfn_4(m1);
CALL_FN(r_send_55, _value9);
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
.r1 = 11'0_b,
.r2 = 11'0_b,
.r3 = 11'0_b,
.r4 = 11'0_b,
.r5 = 11'0_b,
.r6 = 11'0_b,
.r7 = 11'0_b,
.r8 = 11'0_b,
.r9 = 11'0_b,
.r10 = 11'0_b,
.r11 = 11'0_b,
.r12 = 11'0_b,
.r13 = 11'0_b,
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
static constexpr rule_ptr rules[7] {
&module_NoC::rule_router_3,
&module_NoC::rule_router_7,
&module_NoC::rule_router_4,
&module_NoC::rule_router_5,
&module_NoC::rule_router_6,
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
