
type __ = Obj.t

val fst : ('a1 * 'a2) -> 'a1

val snd : ('a1 * 'a2) -> 'a2

type comparison =
| Eq
| Lt
| Gt

type 'a sig0 =
| Exist of 'a



val add : int -> int -> int

val mul : int -> int -> int

module Nat :
 sig
  val pred : int -> int

  val sub : int -> int -> int

  val compare : int -> int -> comparison

  val max : int -> int -> int

  val divmod : int -> int -> int -> int -> int * int

  val div : int -> int -> int

  val modulo : int -> int -> int

  val log2_iter : int -> int -> int -> int -> int

  val log2 : int -> int

  val log2_up : int -> int
 end

val map : ('a1 -> 'a2) -> 'a1 list -> 'a2 list

val fold_right : ('a2 -> 'a1 -> 'a1) -> 'a1 -> 'a2 list -> 'a1

module Pos :
 sig
  val succ : int -> int

  val of_succ_nat : int -> int
 end

module N :
 sig
  val zero : int

  val of_nat : int -> int
 end

type t =
| F1 of int
| FS of int * t

val append : char list -> char list -> char list

type index = int

type ('a, 'b) vect_cons_t = { vhd : 'a; vtl : 'b }

type 't vect = __

val vect_hd : int -> 'a1 vect -> 'a1

val vect_tl : int -> 'a1 vect -> 'a1 vect

val vect_cons : int -> 'a1 -> 'a1 vect -> 'a1 vect

val vect_const : int -> 'a1 -> 'a1 vect

val vect_map : int -> ('a1 -> 'a2) -> 'a1 vect -> 'a2 vect

module Bits :
 sig
  val rmul : int -> int -> int

  val of_positive : int -> int -> bool vect

  val of_N : int -> int -> bool vect

  val of_nat : int -> int -> bool vect

  val zero : int -> bool vect
 end

type 't finiteType = { finite_index : ('t -> int);
                       finite_elements : 't list }

type 'a show = { show0 : ('a -> char list) }

module Show_nat :
 sig
  val string_of_base10_digit : int sig0 -> char list

  val string_of_nat_rec : int -> int -> char list

  val string_of_nat : int -> char list
 end

val show_string : char list show

val list_sum' : int -> int list -> int

val list_sum : int list -> int

type 'k member =
| MemberHd of 'k * 'k list
| MemberTl of 'k * 'k * 'k list * 'k member

val list_nth : 'a1 list -> index -> 'a1

type 'a struct_sig' = { struct_name : char list;
                        struct_fields : (char list * 'a) list }

type enum_sig = { enum_name : char list; enum_size : int;
                  enum_bitsize : int;
                  enum_members : char list vect;
                  enum_bitpatterns : bool vect vect }

type 'a array_sig' = { array_type : 'a; array_len : int }

type type0 =
| Bits_t of int
| Enum_t of enum_sig
| Struct_t of type0 struct_sig'
| Array_t of type0 array_sig'

val struct_fields_sz' :
  (type0 -> int) -> (char list * type0) list -> int

val type_sz : type0 -> int

type struct_index = index

val struct_sz : type0 struct_sig' -> int

val field_type : type0 struct_sig' -> index -> type0

type array_index = index

type port =
| P0
| P1

type type_denote = __

type 'argKind _Sig = { argSigs : 'argKind vect;
                       retSig : 'argKind }

val cSig_of_Sig : int -> type0 _Sig -> int _Sig

val sig_of_CSig : int -> int _Sig -> type0 _Sig

type externalSignature = type0 _Sig

type 'var_t tsig = ('var_t * type0) list

type ('fn_name_t, 'action) internalFunction' = { int_name : 
                                                 'fn_name_t;
                                                 int_body : 
                                                 'action }

type ('k, 'v) context =
| CtxEmpty
| CtxCons of 'k list * 'k * 'v * ('k, 'v) context

type bits_comparison =
| CLt
| CGt
| CLe
| CGe

type bits_display_style =
| DBin
| DDec
| DHex
| DFull

type display_options = { display_strings : bool;
                         display_newline : bool;
                         display_style : bits_display_style }

module PrimTyped :
 sig
  type fdisplay =
  | DisplayUtf8 of int
  | DisplayValue of type0 * display_options

  type fconv =
  | Pack
  | Unpack
  | Ignore

  type lowered1 =
  | IgnoreBits of int
  | DisplayBits of fdisplay

  type fbits1 =
  | Not of int
  | Rev of int
  | SExt of int * int
  | ZExtL of int * int
  | ZExtR of int * int
  | Repeat of int * int
  | Slice of int * int * int
  | Lowered of lowered1

  type fbits2 =
  | And of int
  | Or of int
  | Xor of int
  | Lsl of int * int
  | Lsr of int * int
  | Asr of int * int
  | Concat of int * int
  | Sel of int
  | SliceSubst of int * int * int
  | IndexedSlice of int * int
  | Plus of int
  | Minus of int
  | Mul of int * int
  | EqBits of int * bool
  | Compare of bool * bits_comparison * int

  type fn1 =
  | Display of fdisplay
  | Conv of type0 * fconv
  | Bits1 of fbits1
  | Struct1 of type0 struct_sig' * struct_index
  | Array1 of type0 array_sig' * array_index

  type fn2 =
  | Eq of type0 * bool
  | Bits2 of fbits2
  | Struct2 of type0 struct_sig' * struct_index
  | Array2 of type0 array_sig' * array_index
 end

module CircuitSignatures :
 sig
  val coq_DisplaySigma : PrimTyped.fdisplay -> type0 _Sig

  val coq_CSigma1 : PrimTyped.fbits1 -> int _Sig

  val coq_CSigma2 : PrimTyped.fbits2 -> int _Sig
 end

module PrimSignatures :
 sig
  val coq_Sigma1 : PrimTyped.fn1 -> type0 _Sig

  val coq_Sigma2 : PrimTyped.fn2 -> type0 _Sig
 end

type ('pos_t, 'rule_name_t) scheduler =
| Done
| Cons of 'rule_name_t * ('pos_t, 'rule_name_t) scheduler
| Try of 'rule_name_t * ('pos_t, 'rule_name_t) scheduler
   * ('pos_t, 'rule_name_t) scheduler
| SPos of 'pos_t * ('pos_t, 'rule_name_t) scheduler

type ('pos_t, 'var_t, 'fn_name_t, 'reg_t, 'ext_fn_t) action =
| Fail of 'var_t tsig * type0
| Var of ('var_t * type0) list * 'var_t * type0
   * ('var_t * type0) member
| Const of 'var_t tsig * type0 * type_denote
| Assign of ('var_t * type0) list * 'var_t * type0
   * ('var_t * type0) member
   * ('pos_t, 'var_t, 'fn_name_t, 'reg_t, 'ext_fn_t) action
| Seq of 'var_t tsig * type0
   * ('pos_t, 'var_t, 'fn_name_t, 'reg_t, 'ext_fn_t) action
   * ('pos_t, 'var_t, 'fn_name_t, 'reg_t, 'ext_fn_t) action
| Bind of 'var_t tsig * type0 * type0 * 'var_t
   * ('pos_t, 'var_t, 'fn_name_t, 'reg_t, 'ext_fn_t) action
   * ('pos_t, 'var_t, 'fn_name_t, 'reg_t, 'ext_fn_t) action
| If of 'var_t tsig * type0
   * ('pos_t, 'var_t, 'fn_name_t, 'reg_t, 'ext_fn_t) action
   * ('pos_t, 'var_t, 'fn_name_t, 'reg_t, 'ext_fn_t) action
   * ('pos_t, 'var_t, 'fn_name_t, 'reg_t, 'ext_fn_t) action
| Read of 'var_t tsig * port * 'reg_t
| Write of 'var_t tsig * port * 'reg_t
   * ('pos_t, 'var_t, 'fn_name_t, 'reg_t, 'ext_fn_t) action
| Unop of 'var_t tsig * PrimTyped.fn1
   * ('pos_t, 'var_t, 'fn_name_t, 'reg_t, 'ext_fn_t) action
| Binop of 'var_t tsig * PrimTyped.fn2
   * ('pos_t, 'var_t, 'fn_name_t, 'reg_t, 'ext_fn_t) action
   * ('pos_t, 'var_t, 'fn_name_t, 'reg_t, 'ext_fn_t) action
| ExternalCall of 'var_t tsig * 'ext_fn_t
   * ('pos_t, 'var_t, 'fn_name_t, 'reg_t, 'ext_fn_t) action
| InternalCall of 'var_t tsig * type0 * 'var_t tsig
   * ('fn_name_t, ('pos_t, 'var_t, 'fn_name_t, 'reg_t,
     'ext_fn_t) action) internalFunction'
   * ('var_t * type0, ('pos_t, 'var_t, 'fn_name_t, 'reg_t,
     'ext_fn_t) action) context
| APos of 'var_t tsig * type0 * 'pos_t
   * ('pos_t, 'var_t, 'fn_name_t, 'reg_t, 'ext_fn_t) action

type ('pos_t, 'var_t, 'fn_name_t, 'reg_t, 'ext_fn_t) rule =
  ('pos_t, 'var_t, 'fn_name_t, 'reg_t, 'ext_fn_t) action

type ext_fn_rtl_spec = { efr_name : char list;
                         efr_internal : bool }

type ext_fn_sim_spec = { efs_name : char list;
                         efs_method : bool }

type ('pos_t, 'var_t, 'fn_name_t, 'rule_name_t, 'reg_t,
      'ext_fn_t) koika_package_t = { koika_var_names : 
                                     'var_t show;
                                     koika_fn_names : 
                                     'fn_name_t show;
                                     koika_reg_names : 
                                     'reg_t show;
                                     koika_reg_types : 
                                     ('reg_t -> type0);
                                     koika_reg_init : 
                                     ('reg_t -> type_denote);
                                     koika_reg_finite : 
                                     'reg_t finiteType;
                                     koika_ext_fn_types : 
                                     ('ext_fn_t ->
                                     externalSignature);
                                     koika_rules : ('rule_name_t
                                                   -> ('pos_t,
                                                   'var_t,
                                                   'fn_name_t,
                                                   'reg_t,
                                                   'ext_fn_t)
                                                   rule);
                                     koika_rule_external : 
                                     ('rule_name_t -> bool);
                                     koika_rule_names : 
                                     'rule_name_t show;
                                     koika_scheduler : 
                                     ('pos_t, 'rule_name_t)
                                     scheduler;
                                     koika_module_name : 
                                     char list }

type 'ext_fn_t verilog_package_t = { vp_ext_fn_specs : 
                                     ('ext_fn_t ->
                                     ext_fn_rtl_spec) }

type 'ext_fn_t sim_package_t = { sp_ext_fn_specs : ('ext_fn_t
                                                   ->
                                                   ext_fn_sim_spec);
                                 sp_prelude : char list option }

type interop_package_t = { ip_koika : (unit, char list,
                                      char list, __, __, __)
                                      koika_package_t;
                           ip_verilog : __ verilog_package_t;
                           ip_sim : __ sim_package_t }

module Backends :
 sig
  val register : interop_package_t -> unit
 end

type structIdx = struct_index

val struct_idx :
  type0 struct_sig' -> char list -> structIdx -> struct_index

val struct_idx_hd :
  char list -> type0 -> (char list * type0) list -> char list
  -> structIdx

val struct_idx_tl :
  char list -> char list -> type0 -> (char list * type0) list
  -> char list -> structIdx -> structIdx

module type Typesize =
 sig
  val nocsize : int

  val data_sz : int
 end

module Types :
 functor (TS:Typesize) ->
 sig
  val addr_sz : int

  val basic_flit : type0 struct_sig'

  val router_address : type0 struct_sig'

  val sz : int
 end

type pos_t = unit

type var_t = char list

type fn_name_t = char list

type ('reg_t, 'ext_fn_t) action' =
  (pos_t, var_t, fn_name_t, 'reg_t, 'ext_fn_t) action

type ('reg_t, 'ext_fn_t) action0 =
  (pos_t, var_t, fn_name_t, 'reg_t, 'ext_fn_t) action

type ('reg_t, 'ext_fn_t) function0 =
  (fn_name_t, (pos_t, var_t, fn_name_t, 'reg_t, 'ext_fn_t)
  action) internalFunction'

val refine_sig_tau :
  var_t tsig -> type0 -> ('a1 -> type0) -> ('a2 ->
  externalSignature) -> ('a1, 'a2) action' -> ('a1, 'a2)
  action'

type 'a noConfusionPackage =
| Build_NoConfusionPackage

type 'a functionalInduction = { fun_ind_prf : __ }

module Helpers :
 sig
  val absurd_fin : t -> 'a1

  val coq_NoConfusionPackage_nat : int noConfusionPackage

  type le_t =
  | Coq_le_n
  | Coq_le_S of int * le_t

  val absurd_le_t : int -> le_t -> 'a1

  val widen_fin_clause_5 :
    (int -> int -> le_t -> t -> t) -> int -> int -> le_t -> t
    -> t -> t

  val widen_fin : int -> int -> le_t -> t -> t

  val le_t_inj_clause_2 :
    (int -> int -> le_t -> le_t) -> int -> int -> le_t -> le_t
    -> le_t

  val le_t_inj : int -> int -> le_t -> le_t
 end

module Setup :
 sig
  type router_reg_t =
  | Coq_state
  | Coq_downstream

  type reg_t =
  | Coq_router of int * t * router_reg_t

  type ext_com_t =
  | Coq_input
  | Coq_output

  type ext_fn_t =
  | Coq_ext_fun of int * t * ext_com_t

  type rule_name_t =
  | Coq_rule of int * t
 end

module Instances :
 sig
  val lift_router : int -> Setup.reg_t -> Setup.reg_t

  val regt_elems_clause_2 :
    (int -> Setup.reg_t list) -> int -> Setup.reg_t list ->
    Setup.reg_t list

  val regt_elems : int -> Setup.reg_t list

  val regt_idx : int -> Setup.reg_t -> int

  val coq_Fin_regt : int -> Setup.reg_t finiteType
 end

module Router :
 functor (MyTypes:Typesize) ->
 sig
  module NOC_type :
   sig
    val addr_sz : int

    val basic_flit : type0 struct_sig'

    val router_address : type0 struct_sig'

    val sz : int
   end

  val coq_R : int -> Setup.reg_t -> type0

  val coq_Sigma : int -> Setup.ext_fn_t -> type0 _Sig

  val r_send :
    int -> Setup.reg_t -> (Setup.reg_t, Setup.ext_fn_t)
    function0

  val r_receive :
    int -> Setup.reg_t -> (Setup.reg_t, Setup.ext_fn_t)
    function0

  val _routestart_r :
    int -> int -> (Setup.reg_t, Setup.ext_fn_t) function0 ->
    (Setup.reg_t, Setup.ext_fn_t) function0 -> (Setup.reg_t,
    Setup.ext_fn_t) function0 -> Setup.ext_fn_t ->
    Setup.ext_fn_t -> (Setup.reg_t, Setup.ext_fn_t) action0

  val _routeend_r :
    int -> int -> (Setup.reg_t, Setup.ext_fn_t) function0 ->
    (Setup.reg_t, Setup.ext_fn_t) function0 -> (Setup.reg_t,
    Setup.ext_fn_t) function0 -> Setup.ext_fn_t ->
    Setup.ext_fn_t -> (Setup.reg_t, Setup.ext_fn_t) action0

  val _routecenter_r :
    int -> int -> (Setup.reg_t, Setup.ext_fn_t) function0 ->
    (Setup.reg_t, Setup.ext_fn_t) function0 -> (Setup.reg_t,
    Setup.ext_fn_t) function0 -> (Setup.reg_t, Setup.ext_fn_t)
    function0 -> (Setup.reg_t, Setup.ext_fn_t) function0 ->
    Setup.ext_fn_t -> Setup.ext_fn_t -> (Setup.reg_t,
    Setup.ext_fn_t) action0

  val routestartfn :
    int -> int -> Setup.reg_t -> Setup.reg_t -> Setup.ext_fn_t
    -> Setup.ext_fn_t -> (Setup.reg_t, Setup.ext_fn_t) action0

  val routeendfn :
    int -> int -> Setup.reg_t -> Setup.reg_t -> Setup.ext_fn_t
    -> Setup.ext_fn_t -> (Setup.reg_t, Setup.ext_fn_t) action0

  val routecenterfn :
    int -> int -> Setup.reg_t -> Setup.reg_t -> Setup.reg_t ->
    Setup.ext_fn_t -> Setup.ext_fn_t -> (Setup.reg_t,
    Setup.ext_fn_t) action0
 end

module Actions :
 functor (Coq_b:Typesize) ->
 sig
  module Routerfns :
   sig
    module NOC_type :
     sig
      val addr_sz : int

      val basic_flit : type0 struct_sig'

      val router_address : type0 struct_sig'

      val sz : int
     end

    val coq_R : int -> Setup.reg_t -> type0

    val coq_Sigma : int -> Setup.ext_fn_t -> type0 _Sig

    val r_send :
      int -> Setup.reg_t -> (Setup.reg_t, Setup.ext_fn_t)
      function0

    val r_receive :
      int -> Setup.reg_t -> (Setup.reg_t, Setup.ext_fn_t)
      function0

    val _routestart_r :
      int -> int -> (Setup.reg_t, Setup.ext_fn_t) function0 ->
      (Setup.reg_t, Setup.ext_fn_t) function0 -> (Setup.reg_t,
      Setup.ext_fn_t) function0 -> Setup.ext_fn_t ->
      Setup.ext_fn_t -> (Setup.reg_t, Setup.ext_fn_t) action0

    val _routeend_r :
      int -> int -> (Setup.reg_t, Setup.ext_fn_t) function0 ->
      (Setup.reg_t, Setup.ext_fn_t) function0 -> (Setup.reg_t,
      Setup.ext_fn_t) function0 -> Setup.ext_fn_t ->
      Setup.ext_fn_t -> (Setup.reg_t, Setup.ext_fn_t) action0

    val _routecenter_r :
      int -> int -> (Setup.reg_t, Setup.ext_fn_t) function0 ->
      (Setup.reg_t, Setup.ext_fn_t) function0 -> (Setup.reg_t,
      Setup.ext_fn_t) function0 -> (Setup.reg_t,
      Setup.ext_fn_t) function0 -> (Setup.reg_t,
      Setup.ext_fn_t) function0 -> Setup.ext_fn_t ->
      Setup.ext_fn_t -> (Setup.reg_t, Setup.ext_fn_t) action0

    val routestartfn :
      int -> int -> Setup.reg_t -> Setup.reg_t ->
      Setup.ext_fn_t -> Setup.ext_fn_t -> (Setup.reg_t,
      Setup.ext_fn_t) action0

    val routeendfn :
      int -> int -> Setup.reg_t -> Setup.reg_t ->
      Setup.ext_fn_t -> Setup.ext_fn_t -> (Setup.reg_t,
      Setup.ext_fn_t) action0

    val routecenterfn :
      int -> int -> Setup.reg_t -> Setup.reg_t -> Setup.reg_t
      -> Setup.ext_fn_t -> Setup.ext_fn_t -> (Setup.reg_t,
      Setup.ext_fn_t) action0
   end

  val to_action :
    int -> Setup.rule_name_t -> int -> Helpers.le_t ->
    (Setup.reg_t, Setup.ext_fn_t) action0

  type to_action_graph =
  | Coq_to_action_graph_equation_1
  | Coq_to_action_graph_equation_2 of int * Helpers.le_t
  | Coq_to_action_graph_equation_4 of int
  | Coq_to_action_graph_equation_5 of int * int * Helpers.le_t
  | Coq_to_action_graph_equation_6 of int * t * to_action_graph
  | Coq_to_action_graph_equation_7 of int * t * int
     * Helpers.le_t * to_action_graph

  val to_action_graph_rect :
    'a1 -> (int -> Helpers.le_t -> 'a1) -> (int -> 'a1) ->
    (int -> int -> Helpers.le_t -> 'a1) -> (int -> t ->
    to_action_graph -> 'a1 -> 'a1) -> (int -> t -> int ->
    Helpers.le_t -> to_action_graph -> 'a1 -> 'a1) -> int ->
    Setup.rule_name_t -> int -> Helpers.le_t -> (Setup.reg_t,
    Setup.ext_fn_t) action0 -> to_action_graph -> 'a1

  val to_action_graph_correct :
    int -> Setup.rule_name_t -> int -> Helpers.le_t ->
    to_action_graph

  val to_action_elim :
    'a1 -> (int -> Helpers.le_t -> 'a1) -> (int -> 'a1) ->
    (int -> int -> Helpers.le_t -> 'a1) -> (int -> t -> 'a1 ->
    'a1) -> (int -> t -> int -> Helpers.le_t -> 'a1 -> 'a1) ->
    int -> Setup.rule_name_t -> int -> Helpers.le_t -> 'a1

  val coq_FunctionalElimination_to_action :
    __ -> (int -> Helpers.le_t -> __) -> (int -> __) -> (int
    -> int -> Helpers.le_t -> __) -> (int -> t -> __ -> __) ->
    (int -> t -> int -> Helpers.le_t -> __ -> __) -> int ->
    Setup.rule_name_t -> int -> Helpers.le_t -> __

  val coq_FunctionalInduction_to_action :
    (int -> Setup.rule_name_t -> int -> Helpers.le_t ->
    (Setup.reg_t, Setup.ext_fn_t) action0) functionalInduction

  val schedule_clause_4 :
    (int -> int -> Helpers.le_t -> (pos_t, Setup.rule_name_t)
    scheduler) -> int -> (pos_t, Setup.rule_name_t) scheduler
    -> (pos_t, Setup.rule_name_t) scheduler

  val schedule_clause_5 :
    (int -> int -> Helpers.le_t -> (pos_t, Setup.rule_name_t)
    scheduler) -> int -> int -> Helpers.le_t -> (pos_t,
    Setup.rule_name_t) scheduler -> (pos_t, Setup.rule_name_t)
    scheduler

  val schedule :
    int -> int -> Helpers.le_t -> (pos_t, Setup.rule_name_t)
    scheduler

  type schedule_graph =
  | Coq_schedule_graph_equation_1
  | Coq_schedule_graph_equation_3 of int * Helpers.le_t
  | Coq_schedule_graph_equation_4 of int * Helpers.le_t
  | Coq_schedule_graph_refinement_5 of int * schedule_graph
     * schedule_clause_4_graph
  | Coq_schedule_graph_refinement_6 of int * int
     * Helpers.le_t * schedule_graph * schedule_clause_5_graph
  and schedule_clause_4_graph =
  | Coq_schedule_clause_4_graph_equation_1 of int
     * (pos_t, Setup.rule_name_t) scheduler
  and schedule_clause_5_graph =
  | Coq_schedule_clause_5_graph_equation_1 of int * int
     * Helpers.le_t * (pos_t, Setup.rule_name_t) scheduler

  val schedule_clause_5_graph_mut :
    'a1 -> (int -> Helpers.le_t -> 'a1) -> (int ->
    Helpers.le_t -> 'a1) -> (int -> schedule_graph -> 'a1 ->
    schedule_clause_4_graph -> 'a2 -> 'a1) -> (int -> int ->
    Helpers.le_t -> schedule_graph -> 'a1 ->
    schedule_clause_5_graph -> 'a3 -> 'a1) -> (int -> (pos_t,
    Setup.rule_name_t) scheduler -> 'a2) -> (int -> int ->
    Helpers.le_t -> (pos_t, Setup.rule_name_t) scheduler ->
    'a3) -> int -> int -> Helpers.le_t -> (pos_t,
    Setup.rule_name_t) scheduler -> (pos_t, Setup.rule_name_t)
    scheduler -> schedule_clause_5_graph -> 'a3

  val schedule_clause_4_graph_mut :
    'a1 -> (int -> Helpers.le_t -> 'a1) -> (int ->
    Helpers.le_t -> 'a1) -> (int -> schedule_graph -> 'a1 ->
    schedule_clause_4_graph -> 'a2 -> 'a1) -> (int -> int ->
    Helpers.le_t -> schedule_graph -> 'a1 ->
    schedule_clause_5_graph -> 'a3 -> 'a1) -> (int -> (pos_t,
    Setup.rule_name_t) scheduler -> 'a2) -> (int -> int ->
    Helpers.le_t -> (pos_t, Setup.rule_name_t) scheduler ->
    'a3) -> int -> (pos_t, Setup.rule_name_t) scheduler ->
    (pos_t, Setup.rule_name_t) scheduler ->
    schedule_clause_4_graph -> 'a2

  val schedule_graph_mut :
    'a1 -> (int -> Helpers.le_t -> 'a1) -> (int ->
    Helpers.le_t -> 'a1) -> (int -> schedule_graph -> 'a1 ->
    schedule_clause_4_graph -> 'a2 -> 'a1) -> (int -> int ->
    Helpers.le_t -> schedule_graph -> 'a1 ->
    schedule_clause_5_graph -> 'a3 -> 'a1) -> (int -> (pos_t,
    Setup.rule_name_t) scheduler -> 'a2) -> (int -> int ->
    Helpers.le_t -> (pos_t, Setup.rule_name_t) scheduler ->
    'a3) -> int -> int -> Helpers.le_t -> (pos_t,
    Setup.rule_name_t) scheduler -> schedule_graph -> 'a1

  val schedule_graph_rect :
    'a1 -> (int -> Helpers.le_t -> 'a1) -> (int ->
    Helpers.le_t -> 'a1) -> (int -> schedule_graph -> 'a1 ->
    schedule_clause_4_graph -> 'a2 -> 'a1) -> (int -> int ->
    Helpers.le_t -> schedule_graph -> 'a1 ->
    schedule_clause_5_graph -> 'a3 -> 'a1) -> (int -> (pos_t,
    Setup.rule_name_t) scheduler -> 'a2) -> (int -> int ->
    Helpers.le_t -> (pos_t, Setup.rule_name_t) scheduler ->
    'a3) -> int -> int -> Helpers.le_t -> (pos_t,
    Setup.rule_name_t) scheduler -> schedule_graph -> 'a1

  val schedule_graph_correct :
    int -> int -> Helpers.le_t -> schedule_graph

  val schedule_elim :
    'a1 -> (int -> Helpers.le_t -> 'a1) -> (int ->
    Helpers.le_t -> 'a1) -> (int -> (pos_t, Setup.rule_name_t)
    scheduler -> __ -> 'a1 -> 'a1) -> (int -> int ->
    Helpers.le_t -> (pos_t, Setup.rule_name_t) scheduler -> __
    -> 'a1 -> 'a1) -> int -> int -> Helpers.le_t -> 'a1

  val coq_FunctionalElimination_schedule :
    __ -> (int -> Helpers.le_t -> __) -> (int -> Helpers.le_t
    -> __) -> (int -> (pos_t, Setup.rule_name_t) scheduler ->
    __ -> __ -> __) -> (int -> int -> Helpers.le_t -> (pos_t,
    Setup.rule_name_t) scheduler -> __ -> __ -> __) -> int ->
    int -> Helpers.le_t -> __

  val coq_FunctionalInduction_schedule :
    (int -> int -> Helpers.le_t -> (pos_t, Setup.rule_name_t)
    scheduler) functionalInduction
 end

module FNoc :
 functor (Coq_b:Typesize) ->
 sig
  module Coq_d :
   sig
    module Routerfns :
     sig
      module NOC_type :
       sig
        val addr_sz : int

        val basic_flit : type0 struct_sig'

        val router_address : type0 struct_sig'

        val sz : int
       end

      val coq_R : int -> Setup.reg_t -> type0

      val coq_Sigma : int -> Setup.ext_fn_t -> type0 _Sig

      val r_send :
        int -> Setup.reg_t -> (Setup.reg_t, Setup.ext_fn_t)
        function0

      val r_receive :
        int -> Setup.reg_t -> (Setup.reg_t, Setup.ext_fn_t)
        function0

      val _routestart_r :
        int -> int -> (Setup.reg_t, Setup.ext_fn_t) function0
        -> (Setup.reg_t, Setup.ext_fn_t) function0 ->
        (Setup.reg_t, Setup.ext_fn_t) function0 ->
        Setup.ext_fn_t -> Setup.ext_fn_t -> (Setup.reg_t,
        Setup.ext_fn_t) action0

      val _routeend_r :
        int -> int -> (Setup.reg_t, Setup.ext_fn_t) function0
        -> (Setup.reg_t, Setup.ext_fn_t) function0 ->
        (Setup.reg_t, Setup.ext_fn_t) function0 ->
        Setup.ext_fn_t -> Setup.ext_fn_t -> (Setup.reg_t,
        Setup.ext_fn_t) action0

      val _routecenter_r :
        int -> int -> (Setup.reg_t, Setup.ext_fn_t) function0
        -> (Setup.reg_t, Setup.ext_fn_t) function0 ->
        (Setup.reg_t, Setup.ext_fn_t) function0 ->
        (Setup.reg_t, Setup.ext_fn_t) function0 ->
        (Setup.reg_t, Setup.ext_fn_t) function0 ->
        Setup.ext_fn_t -> Setup.ext_fn_t -> (Setup.reg_t,
        Setup.ext_fn_t) action0

      val routestartfn :
        int -> int -> Setup.reg_t -> Setup.reg_t ->
        Setup.ext_fn_t -> Setup.ext_fn_t -> (Setup.reg_t,
        Setup.ext_fn_t) action0

      val routeendfn :
        int -> int -> Setup.reg_t -> Setup.reg_t ->
        Setup.ext_fn_t -> Setup.ext_fn_t -> (Setup.reg_t,
        Setup.ext_fn_t) action0

      val routecenterfn :
        int -> int -> Setup.reg_t -> Setup.reg_t ->
        Setup.reg_t -> Setup.ext_fn_t -> Setup.ext_fn_t ->
        (Setup.reg_t, Setup.ext_fn_t) action0
     end

    val to_action :
      int -> Setup.rule_name_t -> int -> Helpers.le_t ->
      (Setup.reg_t, Setup.ext_fn_t) action0

    type to_action_graph =
    | Coq_to_action_graph_equation_1
    | Coq_to_action_graph_equation_2 of int * Helpers.le_t
    | Coq_to_action_graph_equation_4 of int
    | Coq_to_action_graph_equation_5 of int * int
       * Helpers.le_t
    | Coq_to_action_graph_equation_6 of int * t
       * to_action_graph
    | Coq_to_action_graph_equation_7 of int * t * int
       * Helpers.le_t * to_action_graph

    val to_action_graph_rect :
      'a1 -> (int -> Helpers.le_t -> 'a1) -> (int -> 'a1) ->
      (int -> int -> Helpers.le_t -> 'a1) -> (int -> t ->
      to_action_graph -> 'a1 -> 'a1) -> (int -> t -> int ->
      Helpers.le_t -> to_action_graph -> 'a1 -> 'a1) -> int ->
      Setup.rule_name_t -> int -> Helpers.le_t ->
      (Setup.reg_t, Setup.ext_fn_t) action0 -> to_action_graph
      -> 'a1

    val to_action_graph_correct :
      int -> Setup.rule_name_t -> int -> Helpers.le_t ->
      to_action_graph

    val to_action_elim :
      'a1 -> (int -> Helpers.le_t -> 'a1) -> (int -> 'a1) ->
      (int -> int -> Helpers.le_t -> 'a1) -> (int -> t -> 'a1
      -> 'a1) -> (int -> t -> int -> Helpers.le_t -> 'a1 ->
      'a1) -> int -> Setup.rule_name_t -> int -> Helpers.le_t
      -> 'a1

    val coq_FunctionalElimination_to_action :
      __ -> (int -> Helpers.le_t -> __) -> (int -> __) -> (int
      -> int -> Helpers.le_t -> __) -> (int -> t -> __ -> __)
      -> (int -> t -> int -> Helpers.le_t -> __ -> __) -> int
      -> Setup.rule_name_t -> int -> Helpers.le_t -> __

    val coq_FunctionalInduction_to_action :
      (int -> Setup.rule_name_t -> int -> Helpers.le_t ->
      (Setup.reg_t, Setup.ext_fn_t) action0)
      functionalInduction

    val schedule_clause_4 :
      (int -> int -> Helpers.le_t -> (pos_t,
      Setup.rule_name_t) scheduler) -> int -> (pos_t,
      Setup.rule_name_t) scheduler -> (pos_t,
      Setup.rule_name_t) scheduler

    val schedule_clause_5 :
      (int -> int -> Helpers.le_t -> (pos_t,
      Setup.rule_name_t) scheduler) -> int -> int ->
      Helpers.le_t -> (pos_t, Setup.rule_name_t) scheduler ->
      (pos_t, Setup.rule_name_t) scheduler

    val schedule :
      int -> int -> Helpers.le_t -> (pos_t, Setup.rule_name_t)
      scheduler

    type schedule_graph =
    | Coq_schedule_graph_equation_1
    | Coq_schedule_graph_equation_3 of int * Helpers.le_t
    | Coq_schedule_graph_equation_4 of int * Helpers.le_t
    | Coq_schedule_graph_refinement_5 of int * schedule_graph
       * schedule_clause_4_graph
    | Coq_schedule_graph_refinement_6 of int * int
       * Helpers.le_t * schedule_graph
       * schedule_clause_5_graph
    and schedule_clause_4_graph =
    | Coq_schedule_clause_4_graph_equation_1 of int
       * (pos_t, Setup.rule_name_t) scheduler
    and schedule_clause_5_graph =
    | Coq_schedule_clause_5_graph_equation_1 of int * 
       int * Helpers.le_t
       * (pos_t, Setup.rule_name_t) scheduler

    val schedule_clause_5_graph_mut :
      'a1 -> (int -> Helpers.le_t -> 'a1) -> (int ->
      Helpers.le_t -> 'a1) -> (int -> schedule_graph -> 'a1 ->
      schedule_clause_4_graph -> 'a2 -> 'a1) -> (int -> int ->
      Helpers.le_t -> schedule_graph -> 'a1 ->
      schedule_clause_5_graph -> 'a3 -> 'a1) -> (int ->
      (pos_t, Setup.rule_name_t) scheduler -> 'a2) -> (int ->
      int -> Helpers.le_t -> (pos_t, Setup.rule_name_t)
      scheduler -> 'a3) -> int -> int -> Helpers.le_t ->
      (pos_t, Setup.rule_name_t) scheduler -> (pos_t,
      Setup.rule_name_t) scheduler -> schedule_clause_5_graph
      -> 'a3

    val schedule_clause_4_graph_mut :
      'a1 -> (int -> Helpers.le_t -> 'a1) -> (int ->
      Helpers.le_t -> 'a1) -> (int -> schedule_graph -> 'a1 ->
      schedule_clause_4_graph -> 'a2 -> 'a1) -> (int -> int ->
      Helpers.le_t -> schedule_graph -> 'a1 ->
      schedule_clause_5_graph -> 'a3 -> 'a1) -> (int ->
      (pos_t, Setup.rule_name_t) scheduler -> 'a2) -> (int ->
      int -> Helpers.le_t -> (pos_t, Setup.rule_name_t)
      scheduler -> 'a3) -> int -> (pos_t, Setup.rule_name_t)
      scheduler -> (pos_t, Setup.rule_name_t) scheduler ->
      schedule_clause_4_graph -> 'a2

    val schedule_graph_mut :
      'a1 -> (int -> Helpers.le_t -> 'a1) -> (int ->
      Helpers.le_t -> 'a1) -> (int -> schedule_graph -> 'a1 ->
      schedule_clause_4_graph -> 'a2 -> 'a1) -> (int -> int ->
      Helpers.le_t -> schedule_graph -> 'a1 ->
      schedule_clause_5_graph -> 'a3 -> 'a1) -> (int ->
      (pos_t, Setup.rule_name_t) scheduler -> 'a2) -> (int ->
      int -> Helpers.le_t -> (pos_t, Setup.rule_name_t)
      scheduler -> 'a3) -> int -> int -> Helpers.le_t ->
      (pos_t, Setup.rule_name_t) scheduler -> schedule_graph
      -> 'a1

    val schedule_graph_rect :
      'a1 -> (int -> Helpers.le_t -> 'a1) -> (int ->
      Helpers.le_t -> 'a1) -> (int -> schedule_graph -> 'a1 ->
      schedule_clause_4_graph -> 'a2 -> 'a1) -> (int -> int ->
      Helpers.le_t -> schedule_graph -> 'a1 ->
      schedule_clause_5_graph -> 'a3 -> 'a1) -> (int ->
      (pos_t, Setup.rule_name_t) scheduler -> 'a2) -> (int ->
      int -> Helpers.le_t -> (pos_t, Setup.rule_name_t)
      scheduler -> 'a3) -> int -> int -> Helpers.le_t ->
      (pos_t, Setup.rule_name_t) scheduler -> schedule_graph
      -> 'a1

    val schedule_graph_correct :
      int -> int -> Helpers.le_t -> schedule_graph

    val schedule_elim :
      'a1 -> (int -> Helpers.le_t -> 'a1) -> (int ->
      Helpers.le_t -> 'a1) -> (int -> (pos_t,
      Setup.rule_name_t) scheduler -> __ -> 'a1 -> 'a1) ->
      (int -> int -> Helpers.le_t -> (pos_t,
      Setup.rule_name_t) scheduler -> __ -> 'a1 -> 'a1) -> int
      -> int -> Helpers.le_t -> 'a1

    val coq_FunctionalElimination_schedule :
      __ -> (int -> Helpers.le_t -> __) -> (int ->
      Helpers.le_t -> __) -> (int -> (pos_t,
      Setup.rule_name_t) scheduler -> __ -> __ -> __) -> (int
      -> int -> Helpers.le_t -> (pos_t, Setup.rule_name_t)
      scheduler -> __ -> __ -> __) -> int -> int ->
      Helpers.le_t -> __

    val coq_FunctionalInduction_schedule :
      (int -> int -> Helpers.le_t -> (pos_t,
      Setup.rule_name_t) scheduler) functionalInduction
   end

  val to_action :
    Setup.rule_name_t -> (Setup.reg_t, Setup.ext_fn_t) action0

  type to_action_graph =
  | Coq_to_action_graph_equation_1 of Setup.rule_name_t

  val to_action_graph_rect :
    (Setup.rule_name_t -> 'a1) -> Setup.rule_name_t ->
    (Setup.reg_t, Setup.ext_fn_t) action0 -> to_action_graph
    -> 'a1

  val to_action_graph_correct :
    Setup.rule_name_t -> to_action_graph

  val to_action_elim :
    (Setup.rule_name_t -> 'a1) -> Setup.rule_name_t -> 'a1

  val coq_FunctionalElimination_to_action :
    (Setup.rule_name_t -> __) -> Setup.rule_name_t -> __

  val coq_FunctionalInduction_to_action :
    (Setup.rule_name_t -> (Setup.reg_t, Setup.ext_fn_t)
    action0) functionalInduction

  val schedule : (pos_t, Setup.rule_name_t) scheduler

  type schedule_graph =
  | Coq_schedule_graph_equation_1

  val schedule_graph_rect :
    'a1 -> (pos_t, Setup.rule_name_t) scheduler ->
    schedule_graph -> 'a1

  val schedule_graph_correct : schedule_graph

  val schedule_elim : 'a1 -> 'a1

  val coq_FunctionalElimination_schedule : __ -> __

  val coq_FunctionalInduction_schedule :
    (pos_t, Setup.rule_name_t) scheduler functionalInduction
 end

module Shows :
 sig
  val show_router : Setup.router_reg_t -> char list

  val show_extcon : Setup.ext_com_t -> char list

  val fin_to_nat : int -> t -> int

  val fin_to_string : int -> t -> char list

  val show_reg : int -> Setup.reg_t -> char list

  val show_ext : int -> Setup.ext_fn_t -> char list

  val show_rule : int -> Setup.rule_name_t -> char list

  val coq_Show_reg : int -> Setup.reg_t show

  val coq_Show_rule : int -> Setup.rule_name_t show

  val coq_Show_ext : int -> Setup.ext_fn_t show
 end

module MyTypeSize :
 sig
  val nocsize : int

  val data_sz : int
 end

module NoC4 :
 sig
  module Coq_d :
   sig
    module Routerfns :
     sig
      module NOC_type :
       sig
        val addr_sz : int

        val basic_flit : type0 struct_sig'

        val router_address : type0 struct_sig'

        val sz : int
       end

      val coq_R : int -> Setup.reg_t -> type0

      val coq_Sigma : int -> Setup.ext_fn_t -> type0 _Sig

      val r_send :
        int -> Setup.reg_t -> (Setup.reg_t, Setup.ext_fn_t)
        function0

      val r_receive :
        int -> Setup.reg_t -> (Setup.reg_t, Setup.ext_fn_t)
        function0

      val _routestart_r :
        int -> int -> (Setup.reg_t, Setup.ext_fn_t) function0
        -> (Setup.reg_t, Setup.ext_fn_t) function0 ->
        (Setup.reg_t, Setup.ext_fn_t) function0 ->
        Setup.ext_fn_t -> Setup.ext_fn_t -> (Setup.reg_t,
        Setup.ext_fn_t) action0

      val _routeend_r :
        int -> int -> (Setup.reg_t, Setup.ext_fn_t) function0
        -> (Setup.reg_t, Setup.ext_fn_t) function0 ->
        (Setup.reg_t, Setup.ext_fn_t) function0 ->
        Setup.ext_fn_t -> Setup.ext_fn_t -> (Setup.reg_t,
        Setup.ext_fn_t) action0

      val _routecenter_r :
        int -> int -> (Setup.reg_t, Setup.ext_fn_t) function0
        -> (Setup.reg_t, Setup.ext_fn_t) function0 ->
        (Setup.reg_t, Setup.ext_fn_t) function0 ->
        (Setup.reg_t, Setup.ext_fn_t) function0 ->
        (Setup.reg_t, Setup.ext_fn_t) function0 ->
        Setup.ext_fn_t -> Setup.ext_fn_t -> (Setup.reg_t,
        Setup.ext_fn_t) action0

      val routestartfn :
        int -> int -> Setup.reg_t -> Setup.reg_t ->
        Setup.ext_fn_t -> Setup.ext_fn_t -> (Setup.reg_t,
        Setup.ext_fn_t) action0

      val routeendfn :
        int -> int -> Setup.reg_t -> Setup.reg_t ->
        Setup.ext_fn_t -> Setup.ext_fn_t -> (Setup.reg_t,
        Setup.ext_fn_t) action0

      val routecenterfn :
        int -> int -> Setup.reg_t -> Setup.reg_t ->
        Setup.reg_t -> Setup.ext_fn_t -> Setup.ext_fn_t ->
        (Setup.reg_t, Setup.ext_fn_t) action0
     end

    val to_action :
      int -> Setup.rule_name_t -> int -> Helpers.le_t ->
      (Setup.reg_t, Setup.ext_fn_t) action0

    type to_action_graph =
    | Coq_to_action_graph_equation_1
    | Coq_to_action_graph_equation_2 of int * Helpers.le_t
    | Coq_to_action_graph_equation_4 of int
    | Coq_to_action_graph_equation_5 of int * int
       * Helpers.le_t
    | Coq_to_action_graph_equation_6 of int * t
       * to_action_graph
    | Coq_to_action_graph_equation_7 of int * t * int
       * Helpers.le_t * to_action_graph

    val to_action_graph_rect :
      'a1 -> (int -> Helpers.le_t -> 'a1) -> (int -> 'a1) ->
      (int -> int -> Helpers.le_t -> 'a1) -> (int -> t ->
      to_action_graph -> 'a1 -> 'a1) -> (int -> t -> int ->
      Helpers.le_t -> to_action_graph -> 'a1 -> 'a1) -> int ->
      Setup.rule_name_t -> int -> Helpers.le_t ->
      (Setup.reg_t, Setup.ext_fn_t) action0 -> to_action_graph
      -> 'a1

    val to_action_graph_correct :
      int -> Setup.rule_name_t -> int -> Helpers.le_t ->
      to_action_graph

    val to_action_elim :
      'a1 -> (int -> Helpers.le_t -> 'a1) -> (int -> 'a1) ->
      (int -> int -> Helpers.le_t -> 'a1) -> (int -> t -> 'a1
      -> 'a1) -> (int -> t -> int -> Helpers.le_t -> 'a1 ->
      'a1) -> int -> Setup.rule_name_t -> int -> Helpers.le_t
      -> 'a1

    val coq_FunctionalElimination_to_action :
      __ -> (int -> Helpers.le_t -> __) -> (int -> __) -> (int
      -> int -> Helpers.le_t -> __) -> (int -> t -> __ -> __)
      -> (int -> t -> int -> Helpers.le_t -> __ -> __) -> int
      -> Setup.rule_name_t -> int -> Helpers.le_t -> __

    val coq_FunctionalInduction_to_action :
      (int -> Setup.rule_name_t -> int -> Helpers.le_t ->
      (Setup.reg_t, Setup.ext_fn_t) action0)
      functionalInduction

    val schedule_clause_4 :
      (int -> int -> Helpers.le_t -> (pos_t,
      Setup.rule_name_t) scheduler) -> int -> (pos_t,
      Setup.rule_name_t) scheduler -> (pos_t,
      Setup.rule_name_t) scheduler

    val schedule_clause_5 :
      (int -> int -> Helpers.le_t -> (pos_t,
      Setup.rule_name_t) scheduler) -> int -> int ->
      Helpers.le_t -> (pos_t, Setup.rule_name_t) scheduler ->
      (pos_t, Setup.rule_name_t) scheduler

    val schedule :
      int -> int -> Helpers.le_t -> (pos_t, Setup.rule_name_t)
      scheduler

    type schedule_graph =
    | Coq_schedule_graph_equation_1
    | Coq_schedule_graph_equation_3 of int * Helpers.le_t
    | Coq_schedule_graph_equation_4 of int * Helpers.le_t
    | Coq_schedule_graph_refinement_5 of int * schedule_graph
       * schedule_clause_4_graph
    | Coq_schedule_graph_refinement_6 of int * int
       * Helpers.le_t * schedule_graph
       * schedule_clause_5_graph
    and schedule_clause_4_graph =
    | Coq_schedule_clause_4_graph_equation_1 of int
       * (pos_t, Setup.rule_name_t) scheduler
    and schedule_clause_5_graph =
    | Coq_schedule_clause_5_graph_equation_1 of int * 
       int * Helpers.le_t
       * (pos_t, Setup.rule_name_t) scheduler

    val schedule_clause_5_graph_mut :
      'a1 -> (int -> Helpers.le_t -> 'a1) -> (int ->
      Helpers.le_t -> 'a1) -> (int -> schedule_graph -> 'a1 ->
      schedule_clause_4_graph -> 'a2 -> 'a1) -> (int -> int ->
      Helpers.le_t -> schedule_graph -> 'a1 ->
      schedule_clause_5_graph -> 'a3 -> 'a1) -> (int ->
      (pos_t, Setup.rule_name_t) scheduler -> 'a2) -> (int ->
      int -> Helpers.le_t -> (pos_t, Setup.rule_name_t)
      scheduler -> 'a3) -> int -> int -> Helpers.le_t ->
      (pos_t, Setup.rule_name_t) scheduler -> (pos_t,
      Setup.rule_name_t) scheduler -> schedule_clause_5_graph
      -> 'a3

    val schedule_clause_4_graph_mut :
      'a1 -> (int -> Helpers.le_t -> 'a1) -> (int ->
      Helpers.le_t -> 'a1) -> (int -> schedule_graph -> 'a1 ->
      schedule_clause_4_graph -> 'a2 -> 'a1) -> (int -> int ->
      Helpers.le_t -> schedule_graph -> 'a1 ->
      schedule_clause_5_graph -> 'a3 -> 'a1) -> (int ->
      (pos_t, Setup.rule_name_t) scheduler -> 'a2) -> (int ->
      int -> Helpers.le_t -> (pos_t, Setup.rule_name_t)
      scheduler -> 'a3) -> int -> (pos_t, Setup.rule_name_t)
      scheduler -> (pos_t, Setup.rule_name_t) scheduler ->
      schedule_clause_4_graph -> 'a2

    val schedule_graph_mut :
      'a1 -> (int -> Helpers.le_t -> 'a1) -> (int ->
      Helpers.le_t -> 'a1) -> (int -> schedule_graph -> 'a1 ->
      schedule_clause_4_graph -> 'a2 -> 'a1) -> (int -> int ->
      Helpers.le_t -> schedule_graph -> 'a1 ->
      schedule_clause_5_graph -> 'a3 -> 'a1) -> (int ->
      (pos_t, Setup.rule_name_t) scheduler -> 'a2) -> (int ->
      int -> Helpers.le_t -> (pos_t, Setup.rule_name_t)
      scheduler -> 'a3) -> int -> int -> Helpers.le_t ->
      (pos_t, Setup.rule_name_t) scheduler -> schedule_graph
      -> 'a1

    val schedule_graph_rect :
      'a1 -> (int -> Helpers.le_t -> 'a1) -> (int ->
      Helpers.le_t -> 'a1) -> (int -> schedule_graph -> 'a1 ->
      schedule_clause_4_graph -> 'a2 -> 'a1) -> (int -> int ->
      Helpers.le_t -> schedule_graph -> 'a1 ->
      schedule_clause_5_graph -> 'a3 -> 'a1) -> (int ->
      (pos_t, Setup.rule_name_t) scheduler -> 'a2) -> (int ->
      int -> Helpers.le_t -> (pos_t, Setup.rule_name_t)
      scheduler -> 'a3) -> int -> int -> Helpers.le_t ->
      (pos_t, Setup.rule_name_t) scheduler -> schedule_graph
      -> 'a1

    val schedule_graph_correct :
      int -> int -> Helpers.le_t -> schedule_graph

    val schedule_elim :
      'a1 -> (int -> Helpers.le_t -> 'a1) -> (int ->
      Helpers.le_t -> 'a1) -> (int -> (pos_t,
      Setup.rule_name_t) scheduler -> __ -> 'a1 -> 'a1) ->
      (int -> int -> Helpers.le_t -> (pos_t,
      Setup.rule_name_t) scheduler -> __ -> 'a1 -> 'a1) -> int
      -> int -> Helpers.le_t -> 'a1

    val coq_FunctionalElimination_schedule :
      __ -> (int -> Helpers.le_t -> __) -> (int ->
      Helpers.le_t -> __) -> (int -> (pos_t,
      Setup.rule_name_t) scheduler -> __ -> __ -> __) -> (int
      -> int -> Helpers.le_t -> (pos_t, Setup.rule_name_t)
      scheduler -> __ -> __ -> __) -> int -> int ->
      Helpers.le_t -> __

    val coq_FunctionalInduction_schedule :
      (int -> int -> Helpers.le_t -> (pos_t,
      Setup.rule_name_t) scheduler) functionalInduction
   end

  val to_action :
    Setup.rule_name_t -> (Setup.reg_t, Setup.ext_fn_t) action0

  type to_action_graph =
  | Coq_to_action_graph_equation_1 of Setup.rule_name_t

  val to_action_graph_rect :
    (Setup.rule_name_t -> 'a1) -> Setup.rule_name_t ->
    (Setup.reg_t, Setup.ext_fn_t) action0 -> to_action_graph
    -> 'a1

  val to_action_graph_correct :
    Setup.rule_name_t -> to_action_graph

  val to_action_elim :
    (Setup.rule_name_t -> 'a1) -> Setup.rule_name_t -> 'a1

  val coq_FunctionalElimination_to_action :
    (Setup.rule_name_t -> __) -> Setup.rule_name_t -> __

  val coq_FunctionalInduction_to_action :
    (Setup.rule_name_t -> (Setup.reg_t, Setup.ext_fn_t)
    action0) functionalInduction

  val schedule : (pos_t, Setup.rule_name_t) scheduler

  type schedule_graph =
  | Coq_schedule_graph_equation_1

  val schedule_graph_rect :
    'a1 -> (pos_t, Setup.rule_name_t) scheduler ->
    schedule_graph -> 'a1

  val schedule_graph_correct : schedule_graph

  val schedule_elim : 'a1 -> 'a1

  val coq_FunctionalElimination_schedule : __ -> __

  val coq_FunctionalInduction_schedule :
    (pos_t, Setup.rule_name_t) scheduler functionalInduction
 end

val r : Setup.reg_t -> type_denote

val rule_external : Setup.rule_name_t -> bool

val package : interop_package_t

val prog : unit
