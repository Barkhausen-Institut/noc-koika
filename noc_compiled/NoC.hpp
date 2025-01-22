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
bits<2> src;
bits<2> dest;
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
static constexpr prims::bitwidth size = 9;
};

template <> _unused bits<9> pack<>(const struct_basic_flit val) {
bits<9> packed = 9'0_b;
packed |= prims::widen<9>(val.renamed_cppnew);
packed <<= 2;
packed |= prims::widen<9>(val.src);
packed <<= 2;
packed |= prims::widen<9>(val.dest);
packed <<= 4;
packed |= prims::widen<9>(val.data);
return packed;
}

template <> struct _unpack<struct_basic_flit, 9> {
static struct_basic_flit unpack(const bits<9> bs) {
struct_basic_flit unpacked = {};
unpacked.data = prims::truncate<4>(bs >> 0u);
unpacked.dest = prims::truncate<2>(bs >> 4u);
unpacked.src = prims::truncate<2>(bs >> 6u);
unpacked.renamed_cppnew = prims::truncate<1>(bs >> 8u);
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
bits<9> r1;
bits<9> r2;
bits<9> r3;
bits<9> r4;
bits<9> r5;
bits<9> r6;
bits<9> r7;

#ifndef SIM_MINIMAL
void dump(std::ostream& os = std::cout) const {
os << "r1 = " << r1 << std::endl;
os << "r2 = " << r2 << std::endl;
os << "r3 = " << r3 << std::endl;
os << "r4 = " << r4 << std::endl;
os << "r5 = " << r5 << std::endl;
os << "r6 = " << r6 << std::endl;
os << "r7 = " << r7 << std::endl;
}

static _unused void vcd_header(std::ostream& os) {
#ifndef SIM_VCD_SCOPES
#define SIM_VCD_SCOPES { "TOP", "NoC" }
#endif
cuttlesim::vcd::begin_header(os, SIM_VCD_SCOPES);
cuttlesim::vcd::var(os, "r1", 9);
cuttlesim::vcd::var(os, "r2", 9);
cuttlesim::vcd::var(os, "r3", 9);
cuttlesim::vcd::var(os, "r4", 9);
cuttlesim::vcd::var(os, "r5", 9);
cuttlesim::vcd::var(os, "r6", 9);
cuttlesim::vcd::var(os, "r7", 9);
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
}

std::uint_fast64_t vcd_readvars(_unused std::istream& is) {
std::string var{}, val{};
std::uint_fast64_t cycle_id = std::numeric_limits<std::uint_fast64_t>::max();
cuttlesim::vcd::read_header(is);
while (cuttlesim::vcd::readvar(is, cycle_id, var, val)) {
if (var == "r1") {
r1 = prims::unpack<bits<9>>(bits<9>::of_str(val));
}
else if (var == "r2") {
r2 = prims::unpack<bits<9>>(bits<9>::of_str(val));
}
else if (var == "r3") {
r3 = prims::unpack<bits<9>>(bits<9>::of_str(val));
}
else if (var == "r4") {
r4 = prims::unpack<bits<9>>(bits<9>::of_str(val));
}
else if (var == "r5") {
r5 = prims::unpack<bits<9>>(bits<9>::of_str(val));
}
else if (var == "r6") {
r6 = prims::unpack<bits<9>>(bits<9>::of_str(val));
}
else if (var == "r7") {
r7 = prims::unpack<bits<9>>(bits<9>::of_str(val));
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
cuttlesim::reg_rwset r5;
cuttlesim::reg_rwset r6;
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
std::uniform_int_distribution<int> uniform{0, 3};
#endif

#define RULE_NAME router_3
DEF_RESET(router_3) {
log.state.r2 = Log.state.r2;
log.state.r3 = Log.state.r3;
log.state.r6 = Log.state.r6;
log.rwset.r2 = Log.rwset.r2;
log.rwset.r3 = Log.rwset.r3;
log.rwset.r6 = Log.rwset.r6;
}

DEF_COMMIT(router_3) {
Log.state.r2 = log.state.r2;
Log.state.r3 = log.state.r3;
Log.state.r6 = log.state.r6;
Log.rwset.r2 = log.rwset.r2;
Log.rwset.r3 = log.rwset.r3;
Log.rwset.r6 = log.rwset.r6;
}

DECL_FN(r_send_0, unit)
DEF_FN(r_send_0, unit &_ret, bits<9> value) {
WRITE0(r3, value);
_ret = prims::tt;
return true;
}

DECL_FN(r_send_1, unit)
DEF_FN(r_send_1, unit &_ret, bits<9> value) {
WRITE0(r2, value);
_ret = prims::tt;
return true;
}

DECL_FN(r_receive_0, bits<9>)
DEF_FN(r_receive_0, bits<9> &_ret) {
_ret = READ0(r2);
return true;
}

DECL_FN(r_receive_1, bits<9>)
DEF_FN(r_receive_1, bits<9> &_ret) {
_ret = READ0(r3);
return true;
}

DECL_FN(r_send_2, unit)
DEF_FN(r_send_2, unit &_ret, bits<9> value) {
WRITE0(r2, value);
_ret = prims::tt;
return true;
}

DECL_FN(r_send_3, unit)
DEF_FN(r_send_3, unit &_ret, bits<9> value) {
WRITE0(r3, value);
_ret = prims::tt;
return true;
}

DECL_FN(r_send_4, unit)
DEF_FN(r_send_4, unit &_ret, bits<9> value) {
WRITE0(r2, value);
_ret = prims::tt;
return true;
}

DECL_FN(r_send_5, unit)
DEF_FN(r_send_5, unit &_ret, bits<9> value) {
WRITE0(r6, value);
_ret = prims::tt;
return true;
}

DECL_FN(r_send_6, unit)
DEF_FN(r_send_6, unit &_ret, bits<9> value) {
WRITE0(r3, value);
_ret = prims::tt;
return true;
}

DECL_FN(r_send_7, unit)
DEF_FN(r_send_7, unit &_ret, bits<9> value) {
WRITE0(r3, value);
_ret = prims::tt;
return true;
}

DECL_FN(r_send_8, unit)
DEF_FN(r_send_8, unit &_ret, bits<9> value) {
WRITE0(r2, value);
_ret = prims::tt;
return true;
}

DECL_FN(r_send_9, unit)
DEF_FN(r_send_9, unit &_ret, bits<9> value) {
WRITE0(r6, value);
_ret = prims::tt;
return true;
}
DEF_RULE(router_3) {
bits<2> r_addr = 2'10_b;
bits<9> m_input = extfuns.extfn_5(9'0_b);
struct_basic_flit msg = prims::unpack<struct_basic_flit>(m_input);
bits<1> new_data = msg.renamed_cppnew;
bits<2> dest = msg.dest;
bits<2> src_p = msg.src;
if ((new_data & ((src_p == r_addr) & (dest > r_addr)))) {
CALL_FN(r_send_0, m_input);
}
else {
if ((new_data & ((src_p == r_addr) & (dest < r_addr)))) {
CALL_FN(r_send_1, m_input);
}
else {
bits<9> m0 = CALL_FN(r_receive_0);
bits<9> m1 = CALL_FN(r_receive_1);
struct_basic_flit msg = prims::unpack<struct_basic_flit>(m0);
bits<1> new_data = msg.renamed_cppnew;
bits<2> src_p = msg.src;
if (((src_p != r_addr) & new_data)) {
struct_basic_flit _x13 = msg;
_x13.renamed_cppnew = 1'0_b;
CALL_FN(r_send_2, prims::pack(_x13));
bits<2> dest = msg.dest;
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
bits<9> _value5 = extfuns.extfn_6(m0);
CALL_FN(r_send_5, _value5);
}
}
}
/* bind */ {
struct_basic_flit msg = prims::unpack<struct_basic_flit>(m1);
bits<1> new_data = msg.renamed_cppnew;
bits<2> src_p = msg.src;
if (((src_p != r_addr) & new_data)) {
struct_basic_flit _x24 = msg;
_x24.renamed_cppnew = 1'0_b;
CALL_FN(r_send_6, prims::pack(_x24));
bits<2> dest = msg.dest;
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
bits<9> _value9 = extfuns.extfn_6(m1);
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

#define RULE_NAME router_4
DEF_RESET(router_4) {
log.state.r3 = Log.state.r3;
log.state.r7 = Log.state.r7;
log.rwset.r3 = Log.rwset.r3;
}

DEF_COMMIT(router_4) {
Log.state.r3 = log.state.r3;
Log.state.r7 = log.state.r7;
Log.rwset.r3 = log.rwset.r3;
}

DECL_FN(r_send_10, unit)
DEF_FN(r_send_10, unit &_ret, bits<9> value) {
WRITE0(r3, value);
_ret = prims::tt;
return true;
}

DECL_FN(r_receive_2, bits<9>)
DEF_FN(r_receive_2, bits<9> &_ret) {
_ret = READ0(r3);
return true;
}

DECL_FN(r_send_11, unit)
DEF_FN(r_send_11, unit &_ret, bits<9> value) {
WRITE0(r3, value);
_ret = prims::tt;
return true;
}

DECL_FN(r_send_12, unit)
DEF_FN(r_send_12, unit &_ret, bits<9> value) {
WRITE0_FAST(r7, value);
_ret = prims::tt;
return true;
}
DEF_RULE(router_4) {
bits<2> r_addr = 2'11_b;
bits<9> m_input = extfuns.extfn_7(9'0_b);
struct_basic_flit msg = prims::unpack<struct_basic_flit>(m_input);
bits<1> new_data = msg.renamed_cppnew;
bits<2> src_p = msg.src;
if ((new_data & (src_p == r_addr))) {
CALL_FN(r_send_10, m_input);
}
else {
bits<9> m0 = CALL_FN(r_receive_2);
struct_basic_flit msg = prims::unpack<struct_basic_flit>(m0);
bits<1> new_data = msg.renamed_cppnew;
bits<2> src_p = msg.src;
if (((src_p != r_addr) & new_data)) {
bits<2> dest = msg.dest;
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
bits<9> _value2 = extfuns.extfn_8(m0);
CALL_FN(r_send_12, _value2);
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
log.state.r4 = Log.state.r4;
log.rwset.r1 = Log.rwset.r1;
}

DEF_COMMIT(router_1) {
Log.state.r1 = log.state.r1;
Log.state.r4 = log.state.r4;
Log.rwset.r1 = log.rwset.r1;
}

DECL_FN(r_send_13, unit)
DEF_FN(r_send_13, unit &_ret, bits<9> value) {
WRITE0(r1, value);
_ret = prims::tt;
return true;
}

DECL_FN(r_receive_3, bits<9>)
DEF_FN(r_receive_3, bits<9> &_ret) {
_ret = READ0(r1);
return true;
}

DECL_FN(r_send_14, unit)
DEF_FN(r_send_14, unit &_ret, bits<9> value) {
WRITE0(r1, value);
_ret = prims::tt;
return true;
}

DECL_FN(r_send_15, unit)
DEF_FN(r_send_15, unit &_ret, bits<9> value) {
WRITE0_FAST(r4, value);
_ret = prims::tt;
return true;
}
DEF_RULE(router_1) {
bits<2> r_addr = 2'00_b;
bits<9> m_input = extfuns.extfn_1(9'0_b);
struct_basic_flit msg = prims::unpack<struct_basic_flit>(m_input);
bits<1> new_data = msg.renamed_cppnew;
bits<2> src_p = msg.src;
if ((new_data & (src_p == r_addr))) {
CALL_FN(r_send_13, m_input);
}
else {
bits<9> m0 = CALL_FN(r_receive_3);
struct_basic_flit msg = prims::unpack<struct_basic_flit>(m0);
bits<1> new_data = msg.renamed_cppnew;
bits<2> src_p = msg.src;
if (((src_p != r_addr) & new_data)) {
bits<2> dest = msg.dest;
if ((dest > r_addr)) {
struct_basic_flit _x11 = msg;
_x11.src = r_addr;
CALL_FN(r_send_14, prims::pack(_x11));
}
else {
if ((dest < r_addr)) {
FAIL_FAST();
}
else {
bits<9> _value2 = extfuns.extfn_2(m0);
CALL_FN(r_send_15, _value2);
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
log.state.r5 = Log.state.r5;
log.rwset.r1 = Log.rwset.r1;
log.rwset.r2 = Log.rwset.r2;
log.rwset.r5 = Log.rwset.r5;
}

DEF_COMMIT(router_2) {
Log.state.r1 = log.state.r1;
Log.state.r2 = log.state.r2;
Log.state.r5 = log.state.r5;
Log.rwset.r1 = log.rwset.r1;
Log.rwset.r2 = log.rwset.r2;
Log.rwset.r5 = log.rwset.r5;
}

DECL_FN(r_send_16, unit)
DEF_FN(r_send_16, unit &_ret, bits<9> value) {
WRITE0(r2, value);
_ret = prims::tt;
return true;
}

DECL_FN(r_send_17, unit)
DEF_FN(r_send_17, unit &_ret, bits<9> value) {
WRITE0(r1, value);
_ret = prims::tt;
return true;
}

DECL_FN(r_receive_4, bits<9>)
DEF_FN(r_receive_4, bits<9> &_ret) {
_ret = READ0(r1);
return true;
}

DECL_FN(r_receive_5, bits<9>)
DEF_FN(r_receive_5, bits<9> &_ret) {
_ret = READ0(r2);
return true;
}

DECL_FN(r_send_18, unit)
DEF_FN(r_send_18, unit &_ret, bits<9> value) {
WRITE0(r1, value);
_ret = prims::tt;
return true;
}

DECL_FN(r_send_19, unit)
DEF_FN(r_send_19, unit &_ret, bits<9> value) {
WRITE0(r2, value);
_ret = prims::tt;
return true;
}

DECL_FN(r_send_20, unit)
DEF_FN(r_send_20, unit &_ret, bits<9> value) {
WRITE0(r1, value);
_ret = prims::tt;
return true;
}

DECL_FN(r_send_21, unit)
DEF_FN(r_send_21, unit &_ret, bits<9> value) {
WRITE0(r5, value);
_ret = prims::tt;
return true;
}

DECL_FN(r_send_22, unit)
DEF_FN(r_send_22, unit &_ret, bits<9> value) {
WRITE0(r2, value);
_ret = prims::tt;
return true;
}

DECL_FN(r_send_23, unit)
DEF_FN(r_send_23, unit &_ret, bits<9> value) {
WRITE0(r2, value);
_ret = prims::tt;
return true;
}

DECL_FN(r_send_24, unit)
DEF_FN(r_send_24, unit &_ret, bits<9> value) {
WRITE0(r1, value);
_ret = prims::tt;
return true;
}

DECL_FN(r_send_25, unit)
DEF_FN(r_send_25, unit &_ret, bits<9> value) {
WRITE0(r5, value);
_ret = prims::tt;
return true;
}
DEF_RULE(router_2) {
bits<2> r_addr = 2'01_b;
bits<9> m_input = extfuns.extfn_3(9'0_b);
struct_basic_flit msg = prims::unpack<struct_basic_flit>(m_input);
bits<1> new_data = msg.renamed_cppnew;
bits<2> dest = msg.dest;
bits<2> src_p = msg.src;
if ((new_data & ((src_p == r_addr) & (dest > r_addr)))) {
CALL_FN(r_send_16, m_input);
}
else {
if ((new_data & ((src_p == r_addr) & (dest < r_addr)))) {
CALL_FN(r_send_17, m_input);
}
else {
bits<9> m0 = CALL_FN(r_receive_4);
bits<9> m1 = CALL_FN(r_receive_5);
struct_basic_flit msg = prims::unpack<struct_basic_flit>(m0);
bits<1> new_data = msg.renamed_cppnew;
bits<2> src_p = msg.src;
if (((src_p != r_addr) & new_data)) {
struct_basic_flit _x13 = msg;
_x13.renamed_cppnew = 1'0_b;
CALL_FN(r_send_18, prims::pack(_x13));
bits<2> dest = msg.dest;
if ((dest > r_addr)) {
struct_basic_flit _x16 = msg;
_x16.src = r_addr;
CALL_FN(r_send_19, prims::pack(_x16));
}
else {
if ((dest < r_addr)) {
struct_basic_flit _x18 = msg;
_x18.src = r_addr;
CALL_FN(r_send_20, prims::pack(_x18));
}
else {
bits<9> _value5 = extfuns.extfn_4(m0);
CALL_FN(r_send_21, _value5);
}
}
}
/* bind */ {
struct_basic_flit msg = prims::unpack<struct_basic_flit>(m1);
bits<1> new_data = msg.renamed_cppnew;
bits<2> src_p = msg.src;
if (((src_p != r_addr) & new_data)) {
struct_basic_flit _x24 = msg;
_x24.renamed_cppnew = 1'0_b;
CALL_FN(r_send_22, prims::pack(_x24));
bits<2> dest = msg.dest;
if ((dest > r_addr)) {
struct_basic_flit _x27 = msg;
_x27.src = r_addr;
CALL_FN(r_send_23, prims::pack(_x27));
}
else {
if ((dest < r_addr)) {
struct_basic_flit _x29 = msg;
_x29.src = r_addr;
CALL_FN(r_send_24, prims::pack(_x29));
}
else {
bits<9> _value9 = extfuns.extfn_4(m1);
CALL_FN(r_send_25, _value9);
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
.r1 = 9'0_b,
.r2 = 9'0_b,
.r3 = 9'0_b,
.r4 = 9'0_b,
.r5 = 9'0_b,
.r6 = 9'0_b,
.r7 = 9'0_b,
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
static constexpr rule_ptr rules[4] {
&module_NoC::rule_router_3,
&module_NoC::rule_router_4,
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
