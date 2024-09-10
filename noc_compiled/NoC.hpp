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
bits<2> trg_y;
bits<2> trg_x;
bits<5> data;
};

struct struct_router_address {
bits<2> y;
bits<2> x;
};

static _unused bits<1>  operator==(const struct_basic_flit v1, const struct_basic_flit v2) {
return bits<1>::mk(bool(v1.renamed_cppnew == v2.renamed_cppnew) && bool(v1.src == v2.src) && bool(v1.trg_y == v2.trg_y) && bool(v1.trg_x == v2.trg_x) && bool(v1.data == v2.data));
}
static _unused bits<1>  operator!=(const struct_basic_flit v1, const struct_basic_flit v2) {
return !(v1 == v2);}

#ifndef SIM_MINIMAL
static _unused std::ostream& operator<<(std::ostream& os, const struct_basic_flit& val) {
return prims::fmt(os, val);
}
#endif

static _unused bits<1>  operator==(const struct_router_address v1, const struct_router_address v2) {
return bits<1>::mk(bool(v1.y == v2.y) && bool(v1.x == v2.x));
}
static _unused bits<1>  operator!=(const struct_router_address v1, const struct_router_address v2) {
return !(v1 == v2);}

#ifndef SIM_MINIMAL
static _unused std::ostream& operator<<(std::ostream& os, const struct_router_address& val) {
return prims::fmt(os, val);
}
#endif

namespace prims {
#ifndef SIM_MINIMAL
static _unused std::ostream& fmt(std::ostream& os, const struct_basic_flit& val, const fmtopts opts) {
os << "basic_flit { ";
os << ".new = "; fmt(os, val.renamed_cppnew, opts) << "; ";
os << ".src = "; fmt(os, val.src, opts) << "; ";
os << ".trg_y = "; fmt(os, val.trg_y, opts) << "; ";
os << ".trg_x = "; fmt(os, val.trg_x, opts) << "; ";
os << ".data = "; fmt(os, val.data, opts) << "; ";
os << "}";
return os;
}

static _unused std::ostream& fmt(std::ostream& os, const struct_router_address& val, const fmtopts opts) {
os << "router_address { ";
os << ".y = "; fmt(os, val.y, opts) << "; ";
os << ".x = "; fmt(os, val.x, opts) << "; ";
os << "}";
return os;
}
#endif

template <> struct type_info<struct_basic_flit> {
static constexpr prims::bitwidth size = 14;
};

template <> _unused bits<14> pack<>(const struct_basic_flit val) {
bits<14> packed = 14'0_b;
packed |= prims::widen<14>(val.renamed_cppnew);
packed <<= 4;
packed |= prims::widen<14>(val.src);
packed <<= 2;
packed |= prims::widen<14>(val.trg_y);
packed <<= 2;
packed |= prims::widen<14>(val.trg_x);
packed <<= 5;
packed |= prims::widen<14>(val.data);
return packed;
}

template <> struct _unpack<struct_basic_flit, 14> {
static struct_basic_flit unpack(const bits<14> bs) {
struct_basic_flit unpacked = {};
unpacked.data = prims::truncate<5>(bs >> 0u);
unpacked.trg_x = prims::truncate<2>(bs >> 5u);
unpacked.trg_y = prims::truncate<2>(bs >> 7u);
unpacked.src = prims::truncate<4>(bs >> 9u);
unpacked.renamed_cppnew = prims::truncate<1>(bs >> 13u);
return unpacked;
}
};

template <> struct type_info<struct_router_address> {
static constexpr prims::bitwidth size = 4;
};

template <> _unused bits<4> pack<>(const struct_router_address val) {
bits<4> packed = 4'0000_b;
packed |= prims::widen<4>(val.y);
packed <<= 2;
packed |= prims::widen<4>(val.x);
return packed;
}

template <> struct _unpack<struct_router_address, 4> {
static struct_router_address unpack(const bits<4> bs) {
struct_router_address unpacked = {};
unpacked.x = prims::truncate<2>(bs >> 0u);
unpacked.y = prims::truncate<2>(bs >> 2u);
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
bits<14> r1;
bits<14> r2;
bits<14> r3;

#ifndef SIM_MINIMAL
void dump(std::ostream& os = std::cout) const {
os << "r1 = " << r1 << std::endl;
os << "r2 = " << r2 << std::endl;
os << "r3 = " << r3 << std::endl;
}

static _unused void vcd_header(std::ostream& os) {
#ifndef SIM_VCD_SCOPES
#define SIM_VCD_SCOPES { "TOP", "NoC" }
#endif
cuttlesim::vcd::begin_header(os, SIM_VCD_SCOPES);
cuttlesim::vcd::var(os, "r1", 14);
cuttlesim::vcd::var(os, "r2", 14);
cuttlesim::vcd::var(os, "r3", 14);
cuttlesim::vcd::end_header(os, SIM_VCD_SCOPES);
}

void vcd_dumpvars(std::uint_fast64_t cycle_id, _unused std::ostream& os, const state_t& previous, const bool force) const {
os << '#' << cycle_id << std::endl;
cuttlesim::vcd::dumpvar(os, "r1", r1, previous.r1, force);
cuttlesim::vcd::dumpvar(os, "r2", r2, previous.r2, force);
cuttlesim::vcd::dumpvar(os, "r3", r3, previous.r3, force);
}

std::uint_fast64_t vcd_readvars(_unused std::istream& is) {
std::string var{}, val{};
std::uint_fast64_t cycle_id = std::numeric_limits<std::uint_fast64_t>::max();
cuttlesim::vcd::read_header(is);
while (cuttlesim::vcd::readvar(is, cycle_id, var, val)) {
if (var == "r1") {
r1 = prims::unpack<bits<14>>(bits<14>::of_str(val));
}
else if (var == "r2") {
r2 = prims::unpack<bits<14>>(bits<14>::of_str(val));
}
else if (var == "r3") {
r3 = prims::unpack<bits<14>>(bits<14>::of_str(val));
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
log.rwset.r2 = Log.rwset.r2;
log.rwset.r3 = Log.rwset.r3;
}

DEF_COMMIT(router_3) {
Log.state.r2 = log.state.r2;
Log.state.r3 = log.state.r3;
Log.rwset.r2 = log.rwset.r2;
Log.rwset.r3 = log.rwset.r3;
}

DECL_FN(r_receive_0, bits<14>)
DEF_FN(r_receive_0, bits<14> &_ret) {
_ret = READ0(r2);
return true;
}

DECL_FN(r_receive_1, bits<14>)
DEF_FN(r_receive_1, bits<14> &_ret) {
_ret = READ0(r3);
return true;
}

DECL_FN(r_send_0, unit)
DEF_FN(r_send_0, unit &_ret, bits<14> value) {
WRITE0(r2, value);
_ret = prims::tt;
return true;
}

DECL_FN(r_send_1, unit)
DEF_FN(r_send_1, unit &_ret, bits<14> value) {
WRITE0(r3, value);
_ret = prims::tt;
return true;
}

DECL_FN(r_send_2, unit)
DEF_FN(r_send_2, unit &_ret, bits<14> value) {
WRITE0(r2, value);
_ret = prims::tt;
return true;
}

DECL_FN(r_send_3, unit)
DEF_FN(r_send_3, unit &_ret, bits<14> value) {
WRITE0(r3, value);
_ret = prims::tt;
return true;
}

DECL_FN(r_send_4, unit)
DEF_FN(r_send_4, unit &_ret, bits<14> value) {
WRITE0(r3, value);
_ret = prims::tt;
return true;
}

DECL_FN(r_send_5, unit)
DEF_FN(r_send_5, unit &_ret, bits<14> value) {
WRITE0(r2, value);
_ret = prims::tt;
return true;
}
DEF_RULE(router_3) {
bits<4> r_addr = 4'0010_b;
bits<14> m0 = CALL_FN(r_receive_0);
bits<14> _y0 = extfuns.tile_in(14'0_b);
m0 = (m0 ^ _y0);
bits<14> m1 = CALL_FN(r_receive_1);
bits<14> _y1 = extfuns.tile_in(14'0_b);
m1 = (m1 ^ _y1);
struct_basic_flit msg = prims::unpack<struct_basic_flit>(m0);
bits<1> new_data = msg.renamed_cppnew;
bits<4> src_p = msg.src;
if (((src_p != r_addr) & new_data)) {
struct_basic_flit _x6 = msg;
_x6.renamed_cppnew = 1'0_b;
CALL_FN(r_send_0, prims::pack(_x6));
bits<2> trg_x = msg.trg_x;
bits<2> trg_y = msg.trg_y;
bits<2> src_x = prims::unpack<struct_router_address>(r_addr).x;
bits<2> src_y = prims::unpack<struct_router_address>(r_addr).y;
if ((trg_x > src_x)) {
struct_basic_flit _x14 = msg;
_x14.src = r_addr;
CALL_FN(r_send_1, prims::pack(_x14));
}
else {
if ((trg_x < src_x)) {
struct_basic_flit _x16 = msg;
_x16.src = r_addr;
CALL_FN(r_send_2, prims::pack(_x16));
}
else {
bits<14> _value3 = extfuns.tile_out(m0);
CALL_FN(r_send_2, _value3);
}
}
}
/* bind */ {
struct_basic_flit msg1 = prims::unpack<struct_basic_flit>(m1);
bits<1> new_data = msg1.renamed_cppnew;
bits<4> src_p = msg1.src;
if (((src_p != r_addr) & new_data)) {
struct_basic_flit _x22 = msg1;
_x22.renamed_cppnew = 1'0_b;
CALL_FN(r_send_3, prims::pack(_x22));
bits<2> trg_x = msg1.trg_x;
bits<2> trg_y = msg1.trg_y;
bits<2> src_x = prims::unpack<struct_router_address>(r_addr).x;
bits<2> src_y = prims::unpack<struct_router_address>(r_addr).y;
if ((trg_x > src_x)) {
struct_basic_flit _x30 = msg1;
_x30.src = r_addr;
CALL_FN(r_send_4, prims::pack(_x30));
}
else {
if ((trg_x < src_x)) {
struct_basic_flit _x32 = msg1;
_x32.src = r_addr;
CALL_FN(r_send_5, prims::pack(_x32));
}
else {
bits<14> _value7 = extfuns.tile_out(m1);
CALL_FN(r_send_5, _value7);
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
log.rwset.r3 = Log.rwset.r3;
}

DEF_COMMIT(router_4) {
Log.state.r3 = log.state.r3;
Log.rwset.r3 = log.rwset.r3;
}

DECL_FN(r_receive_2, bits<14>)
DEF_FN(r_receive_2, bits<14> &_ret) {
_ret = READ0(r3);
return true;
}

DECL_FN(r_send_6, unit)
DEF_FN(r_send_6, unit &_ret, bits<14> value) {
WRITE0(r3, value);
_ret = prims::tt;
return true;
}
DEF_RULE(router_4) {
bits<4> r_addr = 4'0011_b;
bits<14> m0 = CALL_FN(r_receive_2);
bits<14> _y0 = extfuns.tile_in(14'0_b);
m0 = (m0 ^ _y0);
struct_basic_flit msg = prims::unpack<struct_basic_flit>(m0);
bits<1> new_data = msg.renamed_cppnew;
bits<4> src_p = msg.src;
if (((src_p != r_addr) & new_data)) {
bits<2> trg_x = msg.trg_x;
bits<2> trg_y = msg.trg_y;
bits<2> src_x = prims::unpack<struct_router_address>(r_addr).x;
bits<2> src_y = prims::unpack<struct_router_address>(r_addr).y;
if ((trg_x > src_x)) {
FAIL_FAST();
}
else {
if ((trg_x < src_x)) {
struct_basic_flit _x13 = msg;
_x13.src = r_addr;
CALL_FN(r_send_6, prims::pack(_x13));
}
else {
bits<14> _value1 = extfuns.tile_out(m0);
CALL_FN(r_send_6, _value1);
}
}
}

COMMIT();
}
#undef RULE_NAME

#define RULE_NAME router_1
DEF_RESET(router_1) {
log.state.r1 = Log.state.r1;
log.rwset.r1 = Log.rwset.r1;
}

DEF_COMMIT(router_1) {
Log.state.r1 = log.state.r1;
Log.rwset.r1 = log.rwset.r1;
}

DECL_FN(r_receive_3, bits<14>)
DEF_FN(r_receive_3, bits<14> &_ret) {
_ret = READ0(r1);
return true;
}

DECL_FN(r_send_7, unit)
DEF_FN(r_send_7, unit &_ret, bits<14> value) {
WRITE0(r1, value);
_ret = prims::tt;
return true;
}
DEF_RULE(router_1) {
bits<4> r_addr = 4'0000_b;
bits<14> m0 = CALL_FN(r_receive_3);
bits<14> _y0 = extfuns.tile_in(14'0_b);
m0 = (m0 ^ _y0);
struct_basic_flit msg = prims::unpack<struct_basic_flit>(m0);
bits<1> new_data = msg.renamed_cppnew;
bits<4> src_p = msg.src;
if (((src_p != r_addr) & new_data)) {
bits<2> trg_x = msg.trg_x;
bits<2> trg_y = msg.trg_y;
bits<2> src_x = prims::unpack<struct_router_address>(r_addr).x;
bits<2> src_y = prims::unpack<struct_router_address>(r_addr).y;
if ((trg_x > src_x)) {
struct_basic_flit _x12 = msg;
_x12.src = r_addr;
CALL_FN(r_send_7, prims::pack(_x12));
}
else {
if ((trg_x < src_x)) {
FAIL_FAST();
}
else {
bits<14> _value1 = extfuns.tile_out(m0);
CALL_FN(r_send_7, _value1);
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
log.rwset.r1 = Log.rwset.r1;
log.rwset.r2 = Log.rwset.r2;
}

DEF_COMMIT(router_2) {
Log.state.r1 = log.state.r1;
Log.state.r2 = log.state.r2;
Log.rwset.r1 = log.rwset.r1;
Log.rwset.r2 = log.rwset.r2;
}

DECL_FN(r_receive_4, bits<14>)
DEF_FN(r_receive_4, bits<14> &_ret) {
_ret = READ0(r1);
return true;
}

DECL_FN(r_receive_5, bits<14>)
DEF_FN(r_receive_5, bits<14> &_ret) {
_ret = READ0(r2);
return true;
}

DECL_FN(r_send_8, unit)
DEF_FN(r_send_8, unit &_ret, bits<14> value) {
WRITE0(r1, value);
_ret = prims::tt;
return true;
}

DECL_FN(r_send_9, unit)
DEF_FN(r_send_9, unit &_ret, bits<14> value) {
WRITE0(r2, value);
_ret = prims::tt;
return true;
}

DECL_FN(r_send_10, unit)
DEF_FN(r_send_10, unit &_ret, bits<14> value) {
WRITE0(r1, value);
_ret = prims::tt;
return true;
}

DECL_FN(r_send_11, unit)
DEF_FN(r_send_11, unit &_ret, bits<14> value) {
WRITE0(r2, value);
_ret = prims::tt;
return true;
}

DECL_FN(r_send_12, unit)
DEF_FN(r_send_12, unit &_ret, bits<14> value) {
WRITE0(r2, value);
_ret = prims::tt;
return true;
}

DECL_FN(r_send_13, unit)
DEF_FN(r_send_13, unit &_ret, bits<14> value) {
WRITE0(r1, value);
_ret = prims::tt;
return true;
}
DEF_RULE(router_2) {
bits<4> r_addr = 4'0001_b;
bits<14> m0 = CALL_FN(r_receive_4);
bits<14> _y0 = extfuns.tile_in(14'0_b);
m0 = (m0 ^ _y0);
bits<14> m1 = CALL_FN(r_receive_5);
bits<14> _y1 = extfuns.tile_in(14'0_b);
m1 = (m1 ^ _y1);
struct_basic_flit msg = prims::unpack<struct_basic_flit>(m0);
bits<1> new_data = msg.renamed_cppnew;
bits<4> src_p = msg.src;
if (((src_p != r_addr) & new_data)) {
struct_basic_flit _x6 = msg;
_x6.renamed_cppnew = 1'0_b;
CALL_FN(r_send_8, prims::pack(_x6));
bits<2> trg_x = msg.trg_x;
bits<2> trg_y = msg.trg_y;
bits<2> src_x = prims::unpack<struct_router_address>(r_addr).x;
bits<2> src_y = prims::unpack<struct_router_address>(r_addr).y;
if ((trg_x > src_x)) {
struct_basic_flit _x14 = msg;
_x14.src = r_addr;
CALL_FN(r_send_9, prims::pack(_x14));
}
else {
if ((trg_x < src_x)) {
struct_basic_flit _x16 = msg;
_x16.src = r_addr;
CALL_FN(r_send_10, prims::pack(_x16));
}
else {
bits<14> _value3 = extfuns.tile_out(m0);
CALL_FN(r_send_10, _value3);
}
}
}
/* bind */ {
struct_basic_flit msg1 = prims::unpack<struct_basic_flit>(m1);
bits<1> new_data = msg1.renamed_cppnew;
bits<4> src_p = msg1.src;
if (((src_p != r_addr) & new_data)) {
struct_basic_flit _x22 = msg1;
_x22.renamed_cppnew = 1'0_b;
CALL_FN(r_send_11, prims::pack(_x22));
bits<2> trg_x = msg1.trg_x;
bits<2> trg_y = msg1.trg_y;
bits<2> src_x = prims::unpack<struct_router_address>(r_addr).x;
bits<2> src_y = prims::unpack<struct_router_address>(r_addr).y;
if ((trg_x > src_x)) {
struct_basic_flit _x30 = msg1;
_x30.src = r_addr;
CALL_FN(r_send_12, prims::pack(_x30));
}
else {
if ((trg_x < src_x)) {
struct_basic_flit _x32 = msg1;
_x32.src = r_addr;
CALL_FN(r_send_13, prims::pack(_x32));
}
else {
bits<14> _value7 = extfuns.tile_out(m1);
CALL_FN(r_send_13, _value7);
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
.r1 = 14'0_b,
.r2 = 14'0_b,
.r3 = 14'0_b,
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
