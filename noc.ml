
type __ = Obj.t
let __ = let rec f _ = Obj.repr f in Obj.repr f

(** val fst : ('a1 * 'a2) -> 'a1 **)

let fst = function
| (x, _) -> x

(** val snd : ('a1 * 'a2) -> 'a2 **)

let snd = function
| (_, y) -> y

(** val length : 'a1 list -> int **)

let rec length = function
| [] -> 0
| _ :: l' -> Stdlib.Int.succ (length l')

(** val app : 'a1 list -> 'a1 list -> 'a1 list **)

let rec app l m =
  match l with
  | [] -> m
  | a :: l1 -> a :: (app l1 m)

type comparison =
| Eq
| Lt
| Gt

(** val id : __ -> __ **)

let id x =
  x

type ('a, 'p) sigT =
| ExistT of 'a * 'p

(** val projT1 : ('a1, 'a2) sigT -> 'a1 **)

let projT1 = function
| ExistT (a, _) -> a

(** val projT2 : ('a1, 'a2) sigT -> 'a2 **)

let projT2 = function
| ExistT (_, h) -> h



(** val add : int -> int -> int **)

let rec add = (+)

(** val mul : int -> int -> int **)

let rec mul = ( * )

(** val sub : int -> int -> int **)

let rec sub = fun n m -> Stdlib.max 0 (n-m)

module Nat =
 struct
  (** val pred : int -> int **)

  let pred n0 =
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> n0)
      (fun u -> u)
      n0

  (** val compare : int -> int -> comparison **)

  let rec compare = fun n m -> if n=m then Eq else if n<m then Lt else Gt

  (** val max : int -> int -> int **)

  let rec max n0 m =
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> m)
      (fun n' ->
      (fun fO fS n -> if n=0 then fO () else fS (n-1))
        (fun _ -> n0)
        (fun m' -> Stdlib.Int.succ (max n' m'))
        m)
      n0

  (** val log2_iter : int -> int -> int -> int -> int **)

  let rec log2_iter k p q r0 =
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> p)
      (fun k' ->
      (fun fO fS n -> if n=0 then fO () else fS (n-1))
        (fun _ ->
        log2_iter k' (Stdlib.Int.succ p) (Stdlib.Int.succ q) q)
        (fun r' -> log2_iter k' p (Stdlib.Int.succ q) r')
        r0)
      k

  (** val log2 : int -> int **)

  let log2 n0 =
    log2_iter (pred n0) 0 (Stdlib.Int.succ 0) 0

  (** val log2_up : int -> int **)

  let log2_up a =
    match compare (Stdlib.Int.succ 0) a with
    | Lt -> Stdlib.Int.succ (log2 (pred a))
    | _ -> 0
 end

module Pos =
 struct
  (** val succ : int -> int **)

  let rec succ = Stdlib.Int.succ

  (** val of_succ_nat : int -> int **)

  let rec of_succ_nat n0 =
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> 1)
      (fun x -> succ (of_succ_nat x))
      n0
 end

module N =
 struct
  (** val zero : int **)

  let zero =
    0

  (** val of_nat : int -> int **)

  let of_nat n0 =
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> 0)
      (fun n' -> (Pos.of_succ_nat n'))
      n0
 end

(** val rev : 'a1 list -> 'a1 list **)

let rec rev = function
| [] -> []
| x :: l' -> app (rev l') (x :: [])

(** val map : ('a1 -> 'a2) -> 'a1 list -> 'a2 list **)

let rec map f = function
| [] -> []
| a :: t -> (f a) :: (map f t)

(** val fold_left : ('a1 -> 'a2 -> 'a1) -> 'a2 list -> 'a1 -> 'a1 **)

let rec fold_left f l a0 =
  match l with
  | [] -> a0
  | b :: t -> fold_left f t (f a0 b)

(** val fold_right : ('a2 -> 'a1 -> 'a1) -> 'a1 -> 'a2 list -> 'a1 **)

let rec fold_right f a0 = function
| [] -> a0
| b :: t -> f b (fold_right f a0 t)

(** val combine : 'a1 list -> 'a2 list -> ('a1 * 'a2) list **)

let rec combine l l' =
  match l with
  | [] -> []
  | x :: tl ->
    (match l' with
     | [] -> []
     | y :: tl' -> (x, y) :: (combine tl tl'))

(** val skipn : int -> 'a1 list -> 'a1 list **)

let rec skipn n0 l =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> l)
    (fun n1 -> match l with
               | [] -> []
               | _ :: l0 -> skipn n1 l0)
    n0

(** val length0 : char list -> int **)

let rec length0 = function
| [] -> 0
| _::s' -> Stdlib.Int.succ (length0 s')

type 't eqDec = { eq_dec : ('t -> 't -> bool) }

(** val beq_dec : 'a1 eqDec -> 'a1 -> 'a1 -> bool **)

let beq_dec eQ a1 a2 =
  if eQ.eq_dec a1 a2 then true else false

(** val eqDec_bool : bool eqDec **)

let eqDec_bool =
  { eq_dec = (fun t1 t2 ->
    if t1 then if t2 then true else false else if t2 then false else true) }

(** val eqDec_ascii : char eqDec **)

let eqDec_ascii =
  { eq_dec = (fun t1 t2 ->
    (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
      (fun b b0 b1 b2 b3 b4 b5 b6 ->
      (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
        (fun b7 b8 b9 b10 b11 b12 b13 b14 ->
        if eqDec_bool.eq_dec b b7
        then if eqDec_bool.eq_dec b0 b8
             then if eqDec_bool.eq_dec b1 b9
                  then if eqDec_bool.eq_dec b2 b10
                       then if eqDec_bool.eq_dec b3 b11
                            then if eqDec_bool.eq_dec b4 b12
                                 then if eqDec_bool.eq_dec b5 b13
                                      then eqDec_bool.eq_dec b6 b14
                                      else false
                                 else false
                            else false
                       else false
                  else false
             else false
        else false)
        t2)
      t1) }

(** val eqDec_string : char list eqDec **)

let eqDec_string =
  { eq_dec = (fun t1 t2 ->
    let rec f s x =
      match s with
      | [] -> (match x with
               | [] -> true
               | _::_ -> false)
      | a::s0 ->
        (match x with
         | [] -> false
         | a0::s1 -> if eqDec_ascii.eq_dec a a0 then f s0 s1 else false)
    in f t1 t2) }

(** val eqDec_nat : int eqDec **)

let eqDec_nat =
  { eq_dec = (=) }

type index = int

(** val index_of_nat : int -> int -> index option **)

let rec index_of_nat = fun sz x -> if x < sz then Some x else None

(** val index_to_nat : int -> index -> int **)

let rec index_to_nat = fun _ x -> x

type ('a, 'b) vect_cons_t = { vhd : 'a; vtl : 'b }

type 't vect = __

(** val vect_hd : int -> 'a1 vect -> 'a1 **)

let vect_hd _ v =
  (Obj.magic v).vhd

(** val vect_tl : int -> 'a1 vect -> 'a1 vect **)

let vect_tl _ v =
  (Obj.magic v).vtl

(** val vect_cons : int -> 'a1 -> 'a1 vect -> 'a1 vect **)

let vect_cons _ t v =
  Obj.magic { vhd = t; vtl = v }

(** val vect_const : int -> 'a1 -> 'a1 vect **)

let rec vect_const sz0 t =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> Obj.magic __)
    (fun sz1 -> vect_cons sz1 t (vect_const sz1 t))
    sz0

(** val vect_nth : int -> 'a1 vect -> index -> 'a1 **)

let rec vect_nth n0 v idx =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> assert false (* absurd case *))
    (fun n1 ->
    (fun fthisone fanotherone n -> if n = 0 then fthisone () else fanotherone (n - 1))
      (fun _ -> vect_hd n1 v)
      (fun idx0 -> vect_nth n1 (vect_tl n1 v) idx0)
      (Obj.magic idx))
    n0

(** val vect_map : int -> ('a1 -> 'a2) -> 'a1 vect -> 'a2 vect **)

let rec vect_map n0 f v =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> Obj.magic __ v)
    (fun n1 ->
    vect_cons n1 (f (vect_hd n1 v)) (vect_map n1 f (vect_tl n1 v)))
    n0

(** val vect_find_index : int -> ('a1 -> bool) -> 'a1 vect -> index option **)

let rec vect_find_index sz0 f v =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> Obj.magic None)
    (fun n0 ->
    if f (vect_hd n0 v)
    then Some (Obj.magic 0)
    else (match vect_find_index n0 f (vect_tl n0 v) with
          | Some idx -> Some (Obj.magic (Pervasives.succ idx))
          | None -> None))
    sz0

(** val vect_index : int -> 'a1 eqDec -> 'a1 -> 'a1 vect -> index option **)

let vect_index sz0 eQ k v =
  vect_find_index sz0 (fun t -> beq_dec eQ t k) v

(** val eqDec_vect_nil : 'a1 eqDec -> __ eqDec **)

let eqDec_vect_nil _ =
  { eq_dec = (fun _ _ -> true) }

(** val eqDec_vect_cons :
    'a1 eqDec -> 'a2 eqDec -> ('a1, 'a2) vect_cons_t eqDec **)

let eqDec_vect_cons h h0 =
  { eq_dec = (fun t1 t2 ->
    let vhd0 = t1.vhd in
    let vtl0 = t1.vtl in
    let vhd1 = t2.vhd in
    let vtl1 = t2.vtl in
    if h.eq_dec vhd0 vhd1 then h0.eq_dec vtl0 vtl1 else false) }

(** val eqDec_vect : int -> 'a1 eqDec -> 'a1 vect eqDec **)

let rec eqDec_vect n0 h =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> Obj.magic eqDec_vect_nil h)
    (fun n1 -> Obj.magic eqDec_vect_cons h (eqDec_vect n1 h))
    n0

module Bits =
 struct
  (** val rmul : int -> int -> int **)

  let rec rmul n0 m =
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> 0)
      (fun p -> add (rmul p m) m)
      n0

  (** val of_positive : int -> int -> bool vect **)

  let rec of_positive sz0 p =
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> Obj.magic __)
      (fun sz1 ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun p0 -> vect_cons sz1 true (of_positive sz1 p0))
        (fun p0 -> vect_cons sz1 false (of_positive sz1 p0))
        (fun _ -> vect_cons sz1 true (vect_const sz1 false))
        p)
      sz0

  (** val of_N : int -> int -> bool vect **)

  let of_N sz0 n0 =
    (fun f0 fp n -> if n=0 then f0 () else fp n)
      (fun _ -> vect_const sz0 false)
      (fun p -> of_positive sz0 p)
      n0

  (** val of_nat : int -> int -> bool vect **)

  let of_nat sz0 n0 =
    of_N sz0 (N.of_nat n0)

  (** val zero : int -> bool vect **)

  let zero sz0 =
    of_N sz0 N.zero
 end

type 't finiteType = { finite_index : ('t -> int); finite_elements : 't list }

type 'a show = { show0 : ('a -> char list) }

(** val show_string : char list show **)

let show_string =
  { show0 = (fun x -> x) }

(** val list_sum' : int -> int list -> int **)

let list_sum' n0 l =
  fold_right (fun x acc -> add acc x) n0 l

(** val list_sum : int list -> int **)

let list_sum l =
  list_sum' 0 l

type ('s, 'f) result =
| Success of 's
| Failure of 'f

(** val result_map_failure :
    ('a2 -> 'a3) -> ('a1, 'a2) result -> ('a1, 'a3) result **)

let result_map_failure fn = function
| Success s -> Success s
| Failure f -> Failure (fn f)

(** val opt_result : 'a1 option -> 'a2 -> ('a1, 'a2) result **)

let opt_result o f =
  match o with
  | Some x -> Success x
  | None -> Failure f

(** val result_list_map :
    ('a1 -> ('a2, 'a3) result) -> 'a1 list -> ('a2 list, 'a3) result **)

let rec result_list_map f = function
| [] -> Success []
| a :: la0 ->
  (match f a with
   | Success b ->
     (match result_list_map f la0 with
      | Success la1 -> Success (b :: la1)
      | Failure f0 -> Failure f0)
   | Failure f0 -> Failure f0)

(** val extract_success : ('a1, 'a2) result -> 'a1 **)

let extract_success = function
| Success s -> s
| Failure _ -> assert false (* absurd case *)

type 'k member =
| MemberHd of 'k * 'k list
| MemberTl of 'k * 'k * 'k list * 'k member

(** val assoc :
    'a1 eqDec -> 'a1 -> ('a1 * 'a2) list -> ('a2, ('a1 * 'a2) member) sigT
    option **)

let rec assoc h k1 = function
| [] -> None
| p :: l ->
  let (k, k0) = p in
  let s = h.eq_dec k1 k in
  if s
  then Some (ExistT (k0, (MemberHd ((k, k0), l))))
  else let o = assoc h k1 l in
       (match o with
        | Some s0 ->
          let ExistT (x, m) = s0 in
          Some (ExistT (x, (MemberTl ((k1, x), (k, k0), l, m))))
        | None -> None)

(** val list_assoc : 'a1 eqDec -> 'a1 -> ('a1 * 'a2) list -> index option **)

let rec list_assoc eQ k = function
| [] -> None
| p :: l0 ->
  let s = eQ.eq_dec k (fst p) in
  if s
  then Some (Obj.magic 0)
  else let o = list_assoc eQ k l0 in
       (match o with
        | Some i -> Some (Obj.magic (Pervasives.succ i))
        | None -> None)

(** val list_nth : 'a1 list -> index -> 'a1 **)

let rec list_nth l idx =
  match l with
  | [] -> assert false (* absurd case *)
  | k :: l0 ->
    ((fun fthisone fanotherone n -> if n = 0 then fthisone () else fanotherone (n - 1))
       (fun _ -> k)
       (fun a -> list_nth l0 a)
       (Obj.magic idx))

type 'a struct_sig' = { struct_name : char list;
                        struct_fields : (char list * 'a) list }

type enum_sig = { enum_name : char list; enum_size : int; enum_bitsize : 
                  int; enum_members : char list vect;
                  enum_bitpatterns : bool vect vect }

type 'a array_sig' = { array_type : 'a; array_len : int }

type type0 =
| Bits_t of int
| Enum_t of enum_sig
| Struct_t of type0 struct_sig'
| Array_t of type0 array_sig'

type type_kind =
| Kind_bits
| Kind_enum of enum_sig option
| Kind_struct of type0 struct_sig' option
| Kind_array of type0 array_sig' option

(** val kind_of_type : type0 -> type_kind **)

let kind_of_type = function
| Bits_t _ -> Kind_bits
| Enum_t sig0 -> Kind_enum (Some sig0)
| Struct_t sig0 -> Kind_struct (Some sig0)
| Array_t sig0 -> Kind_array (Some sig0)

(** val struct_fields_sz' :
    (type0 -> int) -> (char list * type0) list -> int **)

let struct_fields_sz' type_sz0 fields =
  list_sum (map (fun nm_tau -> type_sz0 (snd nm_tau)) fields)

(** val type_sz : type0 -> int **)

let rec type_sz = function
| Bits_t sz0 -> sz0
| Enum_t sig0 -> sig0.enum_bitsize
| Struct_t sig0 -> struct_fields_sz' type_sz sig0.struct_fields
| Array_t sig0 -> Bits.rmul sig0.array_len (type_sz sig0.array_type)

type struct_index = index

(** val struct_sz : type0 struct_sig' -> int **)

let struct_sz sig0 =
  type_sz (Struct_t sig0)

(** val field_type : type0 struct_sig' -> index -> type0 **)

let field_type sig0 idx =
  snd (list_nth sig0.struct_fields idx)

(** val field_sz : type0 struct_sig' -> index -> int **)

let field_sz sig0 idx =
  type_sz (field_type sig0 idx)

(** val field_offset_right : type0 struct_sig' -> struct_index -> int **)

let field_offset_right sig0 idx =
  let next_fields =
    skipn (Stdlib.Int.succ (index_to_nat (length sig0.struct_fields) idx))
      sig0.struct_fields
  in
  struct_fields_sz' type_sz next_fields

type array_index = index

(** val array_sz : type0 array_sig' -> int **)

let array_sz sig0 =
  type_sz (Array_t sig0)

(** val element_sz : type0 array_sig' -> int **)

let element_sz sig0 =
  type_sz sig0.array_type

(** val element_offset_right : type0 array_sig' -> array_index -> int **)

let element_offset_right sig0 idx =
  Bits.rmul
    (sub sig0.array_len (Stdlib.Int.succ (index_to_nat sig0.array_len idx)))
    (element_sz sig0)

type port =
| P0
| P1

type type_denote = __

type 'argKind _Sig = { argSigs : 'argKind vect; retSig : 'argKind }

type ('argKind, 'type_of_argKind) _Sig_denote = __

type sig_denote = (type0, type_denote) _Sig_denote

(** val cSig_of_Sig : int -> type0 _Sig -> int _Sig **)

let cSig_of_Sig n0 sig0 =
  { argSigs = (vect_map n0 type_sz sig0.argSigs); retSig =
    (type_sz sig0.retSig) }

(** val sig_of_CSig : int -> int _Sig -> type0 _Sig **)

let sig_of_CSig n0 sig0 =
  { argSigs = (vect_map n0 (fun x -> Bits_t x) sig0.argSigs); retSig =
    (Bits_t sig0.retSig) }

type externalSignature = type0 _Sig

type 'var_t tsig = ('var_t * type0) list

type ('var_t, 'fn_name_t, 'action) internalFunction = { int_name : 'fn_name_t;
                                                        int_argspec : 
                                                        'var_t tsig;
                                                        int_retSig : 
                                                        type0;
                                                        int_body : 'action }

(** val map_intf_body :
    ('a3 -> 'a4) -> ('a1, 'a2, 'a3) internalFunction -> ('a1, 'a2, 'a4)
    internalFunction **)

let map_intf_body f fn =
  { int_name = fn.int_name; int_argspec = fn.int_argspec; int_retSig =
    fn.int_retSig; int_body = (f fn.int_body) }

type 'var_t arg_sig = { arg_name : 'var_t; arg_type : type0 }

(** val prod_of_argsig : 'a1 arg_sig -> 'a1 * type0 **)

let prod_of_argsig a =
  (a.arg_name, a.arg_type)

(** val eqDec_type : type0 eqDec **)

let eqDec_type =
  { eq_dec =
    (let rec iHtau t1 t2 =
       match t1 with
       | Bits_t sz0 ->
         (match t2 with
          | Bits_t sz1 -> eqDec_nat.eq_dec sz0 sz1
          | _ -> false)
       | Enum_t sig0 ->
         (match t2 with
          | Enum_t sig1 ->
            let { enum_name = enum_name0; enum_size = enum_size0;
              enum_bitsize = enum_bitsize0; enum_members = enum_members0;
              enum_bitpatterns = enum_bitpatterns0 } = sig0
            in
            let { enum_name = enum_name1; enum_size = enum_size1;
              enum_bitsize = enum_bitsize1; enum_members = enum_members1;
              enum_bitpatterns = enum_bitpatterns1 } = sig1
            in
            let s = eqDec_string.eq_dec enum_name0 enum_name1 in
            if s
            then let s0 = eqDec_nat.eq_dec enum_size0 enum_size1 in
                 if s0
                 then let s1 = eqDec_nat.eq_dec enum_bitsize0 enum_bitsize1 in
                      if s1
                      then let s2 =
                             (eqDec_vect enum_size1 eqDec_string).eq_dec
                               enum_members0 enum_members1
                           in
                           if s2
                           then (eqDec_vect enum_size1
                                  (eqDec_vect enum_bitsize1 eqDec_bool)).eq_dec
                                  enum_bitpatterns0 enum_bitpatterns1
                           else false
                      else false
                 else false
            else false
          | _ -> false)
       | Struct_t sig0 ->
         (match t2 with
          | Struct_t sig1 ->
            let { struct_name = struct_name0; struct_fields =
              struct_fields0 } = sig0
            in
            let { struct_name = struct_name1; struct_fields =
              struct_fields1 } = sig1
            in
            let s = eqDec_string.eq_dec struct_name0 struct_name1 in
            if s
            then let rec f l x =
                   match l with
                   | [] -> (match x with
                            | [] -> true
                            | _ :: _ -> false)
                   | y :: l0 ->
                     (match x with
                      | [] -> false
                      | p :: l1 ->
                        if let (a, b) = y in
                           let (s0, t) = p in
                           if eqDec_string.eq_dec a s0
                           then iHtau b t
                           else false
                        then f l0 l1
                        else false)
                 in f struct_fields0 struct_fields1
            else false
          | _ -> false)
       | Array_t sig0 ->
         (match t2 with
          | Array_t sig1 ->
            let { array_type = array_type0; array_len = array_len0 } = sig0 in
            let { array_type = array_type1; array_len = array_len1 } = sig1 in
            let s = iHtau array_type0 array_type1 in
            if s then eqDec_nat.eq_dec array_len0 array_len1 else false
          | _ -> false)
     in iHtau) }

type ('k, 'v) context =
| CtxEmpty
| CtxCons of 'k list * 'k * 'v * ('k, 'v) context

type basic_error_message =
| OutOfBounds of int * type0 array_sig'
| UnboundField of char list * type0 struct_sig'
| TypeMismatch of type0 * type0
| KindMismatch of type_kind * type_kind

type ('var_t, 'fn_name_t) error_message =
| ExplicitErrorInAst
| SugaredConstructorInAst
| UnboundVariable of 'var_t
| UnboundEnumMember of char list * enum_sig
| BasicError of basic_error_message
| TooManyArguments of 'fn_name_t * int * int
| TooFewArguments of 'fn_name_t * int * int

type fn_tc_error_loc =
| Arg1
| Arg2

type fn_tc_error = fn_tc_error_loc * basic_error_message

(** val assert_kind :
    type_kind -> fn_tc_error_loc -> type0 -> (__, fn_tc_error) result **)

let assert_kind kind arg tau =
  match kind with
  | Kind_bits ->
    (match tau with
     | Bits_t sz0 -> Success (Obj.magic sz0)
     | _ -> Failure (arg, (KindMismatch ((kind_of_type tau), kind))))
  | Kind_enum _ ->
    (match tau with
     | Enum_t sg -> Success (Obj.magic sg)
     | _ -> Failure (arg, (KindMismatch ((kind_of_type tau), kind))))
  | Kind_struct _ ->
    (match tau with
     | Struct_t sg -> Success (Obj.magic sg)
     | _ -> Failure (arg, (KindMismatch ((kind_of_type tau), kind))))
  | Kind_array _ ->
    (match tau with
     | Array_t sg -> Success (Obj.magic sg)
     | _ -> Failure (arg, (KindMismatch ((kind_of_type tau), kind))))

type ('pos_t, 'var_t, 'fn_name_t) error = { epos : 'pos_t;
                                            emsg : ('var_t, 'fn_name_t)
                                                   error_message }

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

type display_options = { display_strings : bool; display_newline : bool;
                         display_style : bits_display_style }

module PrimUntyped =
 struct
  type udisplay =
  | UDisplayUtf8
  | UDisplayValue of display_options

  type uconv =
  | UPack
  | UUnpack of type0
  | UIgnore

  type ubits1 =
  | UNot
  | USExt of int
  | UZExtL of int
  | UZExtR of int
  | URepeat of int
  | USlice of int * int

  type ubits2 =
  | UAnd
  | UOr
  | UXor
  | ULsl
  | ULsr
  | UAsr
  | UConcat
  | USel
  | USliceSubst of int * int
  | UIndexedSlice of int
  | UPlus
  | UMinus
  | UMul
  | UCompare of bool * bits_comparison

  type ustruct1 =
  | UGetField of char list
  | UGetFieldBits of type0 struct_sig' * char list

  type ustruct2 =
  | USubstField of char list
  | USubstFieldBits of type0 struct_sig' * char list

  type uarray1 =
  | UGetElement of int
  | UGetElementBits of type0 array_sig' * int

  type uarray2 =
  | USubstElement of int
  | USubstElementBits of type0 array_sig' * int

  type ufn1 =
  | UDisplay of udisplay
  | UConv of uconv
  | UBits1 of ubits1
  | UStruct1 of ustruct1
  | UArray1 of uarray1

  type ufn2 =
  | UEq of bool
  | UBits2 of ubits2
  | UStruct2 of ustruct2
  | UArray2 of uarray2
 end

module PrimTyped =
 struct
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

  (** val coq_GetElementBits : type0 array_sig' -> array_index -> fbits1 **)

  let coq_GetElementBits sig0 idx =
    Slice ((array_sz sig0), (element_offset_right sig0 idx),
      (element_sz sig0))

  (** val coq_SubstElementBits : type0 array_sig' -> array_index -> fbits2 **)

  let coq_SubstElementBits sig0 idx =
    SliceSubst ((array_sz sig0), (element_offset_right sig0 idx),
      (element_sz sig0))

  (** val coq_GetFieldBits : type0 struct_sig' -> struct_index -> fbits1 **)

  let coq_GetFieldBits sig0 idx =
    Slice ((struct_sz sig0), (field_offset_right sig0 idx),
      (field_sz sig0 idx))

  (** val coq_SubstFieldBits : type0 struct_sig' -> struct_index -> fbits2 **)

  let coq_SubstFieldBits sig0 idx =
    SliceSubst ((struct_sz sig0), (field_offset_right sig0 idx),
      (field_sz sig0 idx))
 end

module PrimTypeInference =
 struct
  (** val find_field :
      type0 struct_sig' -> char list -> (index, fn_tc_error) result **)

  let find_field sig0 f =
    opt_result (list_assoc eqDec_string f sig0.struct_fields) (Arg1,
      (UnboundField (f, sig0)))

  (** val check_index :
      type0 array_sig' -> int -> (array_index, fn_tc_error) result **)

  let check_index sig0 pos =
    opt_result (index_of_nat sig0.array_len pos) (Arg1, (OutOfBounds (pos,
      sig0)))

  (** val tc1 :
      PrimUntyped.ufn1 -> type0 -> (PrimTyped.fn1, fn_tc_error) result **)

  let tc1 fn tau1 =
    match fn with
    | PrimUntyped.UDisplay fn0 ->
      (match fn0 with
       | PrimUntyped.UDisplayUtf8 ->
         (match assert_kind (Kind_array None) Arg1 tau1 with
          | Success sig0 ->
            Success (PrimTyped.Display (PrimTyped.DisplayUtf8
              (Obj.magic sig0).array_len))
          | Failure f -> Failure f)
       | PrimUntyped.UDisplayValue opts ->
         Success (PrimTyped.Display (PrimTyped.DisplayValue (tau1, opts))))
    | PrimUntyped.UConv fn0 ->
      Success
        (match fn0 with
         | PrimUntyped.UPack -> PrimTyped.Conv (tau1, PrimTyped.Pack)
         | PrimUntyped.UUnpack tau -> PrimTyped.Conv (tau, PrimTyped.Unpack)
         | PrimUntyped.UIgnore -> PrimTyped.Conv (tau1, PrimTyped.Ignore))
    | PrimUntyped.UBits1 fn0 ->
      (match assert_kind Kind_bits Arg1 tau1 with
       | Success sz1 ->
         Success (PrimTyped.Bits1
           (match fn0 with
            | PrimUntyped.UNot -> PrimTyped.Not (Obj.magic sz1)
            | PrimUntyped.USExt width ->
              PrimTyped.SExt ((Obj.magic sz1), width)
            | PrimUntyped.UZExtL width ->
              PrimTyped.ZExtL ((Obj.magic sz1), width)
            | PrimUntyped.UZExtR width ->
              PrimTyped.ZExtR ((Obj.magic sz1), width)
            | PrimUntyped.URepeat times ->
              PrimTyped.Repeat ((Obj.magic sz1), times)
            | PrimUntyped.USlice (offset, width) ->
              PrimTyped.Slice ((Obj.magic sz1), offset, width)))
       | Failure f -> Failure f)
    | PrimUntyped.UStruct1 fn0 ->
      (match fn0 with
       | PrimUntyped.UGetField f ->
         (match assert_kind (Kind_struct None) Arg1 tau1 with
          | Success sig0 ->
            (match find_field (Obj.magic sig0) f with
             | Success idx ->
               Success (PrimTyped.Struct1 ((Obj.magic sig0), idx))
             | Failure f0 -> Failure f0)
          | Failure f0 -> Failure f0)
       | PrimUntyped.UGetFieldBits (sig0, f) ->
         (match find_field sig0 f with
          | Success idx ->
            Success (PrimTyped.Bits1 (PrimTyped.coq_GetFieldBits sig0 idx))
          | Failure f0 -> Failure f0))
    | PrimUntyped.UArray1 fn0 ->
      (match fn0 with
       | PrimUntyped.UGetElement pos ->
         (match assert_kind (Kind_array None) Arg1 tau1 with
          | Success sig0 ->
            (match check_index (Obj.magic sig0) pos with
             | Success idx ->
               Success (PrimTyped.Array1 ((Obj.magic sig0), idx))
             | Failure f -> Failure f)
          | Failure f -> Failure f)
       | PrimUntyped.UGetElementBits (sig0, pos) ->
         (match check_index sig0 pos with
          | Success idx ->
            Success (PrimTyped.Bits1 (PrimTyped.coq_GetElementBits sig0 idx))
          | Failure f -> Failure f))

  (** val tc2 :
      PrimUntyped.ufn2 -> type0 -> type0 -> (PrimTyped.fn2, fn_tc_error)
      result **)

  let tc2 fn tau1 tau2 =
    match fn with
    | PrimUntyped.UEq negate -> Success (PrimTyped.Eq (tau1, negate))
    | PrimUntyped.UBits2 fn0 ->
      (match assert_kind Kind_bits Arg1 tau1 with
       | Success sz1 ->
         (match assert_kind Kind_bits Arg2 tau2 with
          | Success sz2 ->
            Success (PrimTyped.Bits2
              (match fn0 with
               | PrimUntyped.UAnd -> PrimTyped.And (Obj.magic sz1)
               | PrimUntyped.UOr -> PrimTyped.Or (Obj.magic sz1)
               | PrimUntyped.UXor -> PrimTyped.Xor (Obj.magic sz1)
               | PrimUntyped.ULsl ->
                 PrimTyped.Lsl ((Obj.magic sz1), (Obj.magic sz2))
               | PrimUntyped.ULsr ->
                 PrimTyped.Lsr ((Obj.magic sz1), (Obj.magic sz2))
               | PrimUntyped.UAsr ->
                 PrimTyped.Asr ((Obj.magic sz1), (Obj.magic sz2))
               | PrimUntyped.UConcat ->
                 PrimTyped.Concat ((Obj.magic sz1), (Obj.magic sz2))
               | PrimUntyped.USel -> PrimTyped.Sel (Obj.magic sz1)
               | PrimUntyped.USliceSubst (offset, width) ->
                 PrimTyped.SliceSubst ((Obj.magic sz1), offset, width)
               | PrimUntyped.UIndexedSlice width ->
                 PrimTyped.IndexedSlice ((Obj.magic sz1), width)
               | PrimUntyped.UPlus -> PrimTyped.Plus (Obj.magic sz1)
               | PrimUntyped.UMinus -> PrimTyped.Minus (Obj.magic sz1)
               | PrimUntyped.UMul ->
                 PrimTyped.Mul ((Obj.magic sz1), (Obj.magic sz2))
               | PrimUntyped.UCompare (signed, c) ->
                 PrimTyped.Compare (signed, c, (Obj.magic sz1))))
          | Failure f -> Failure f)
       | Failure f -> Failure f)
    | PrimUntyped.UStruct2 fn0 ->
      (match fn0 with
       | PrimUntyped.USubstField f ->
         (match assert_kind (Kind_struct None) Arg1 tau1 with
          | Success sig0 ->
            (match find_field (Obj.magic sig0) f with
             | Success idx ->
               Success (PrimTyped.Struct2 ((Obj.magic sig0), idx))
             | Failure f0 -> Failure f0)
          | Failure f0 -> Failure f0)
       | PrimUntyped.USubstFieldBits (sig0, f) ->
         (match find_field sig0 f with
          | Success idx ->
            Success (PrimTyped.Bits2 (PrimTyped.coq_SubstFieldBits sig0 idx))
          | Failure f0 -> Failure f0))
    | PrimUntyped.UArray2 fn0 ->
      (match fn0 with
       | PrimUntyped.USubstElement pos ->
         (match assert_kind (Kind_array None) Arg1 tau1 with
          | Success sig0 ->
            (match check_index (Obj.magic sig0) pos with
             | Success idx ->
               Success (PrimTyped.Array2 ((Obj.magic sig0), idx))
             | Failure f -> Failure f)
          | Failure f -> Failure f)
       | PrimUntyped.USubstElementBits (sig0, pos) ->
         (match check_index sig0 pos with
          | Success idx ->
            Success (PrimTyped.Bits2
              (PrimTyped.coq_SubstElementBits sig0 idx))
          | Failure f -> Failure f))
 end

module CircuitSignatures =
 struct
  (** val coq_DisplaySigma : PrimTyped.fdisplay -> type0 _Sig **)

  let coq_DisplaySigma fn =
    { argSigs =
      (vect_cons 0
        (match fn with
         | PrimTyped.DisplayUtf8 len ->
           Array_t { array_type = (Bits_t (Stdlib.Int.succ (Stdlib.Int.succ
             (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
             (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0)))))))));
             array_len = len }
         | PrimTyped.DisplayValue (tau, _) -> tau) (Obj.magic __)); retSig =
      (Bits_t 0) }

  (** val coq_CSigma1 : PrimTyped.fbits1 -> int _Sig **)

  let coq_CSigma1 = function
  | PrimTyped.Not sz0 ->
    { argSigs = (vect_cons 0 sz0 (Obj.magic __)); retSig = sz0 }
  | PrimTyped.SExt (sz0, width) ->
    { argSigs = (vect_cons 0 sz0 (Obj.magic __)); retSig =
      (Nat.max sz0 width) }
  | PrimTyped.ZExtL (sz0, width) ->
    { argSigs = (vect_cons 0 sz0 (Obj.magic __)); retSig =
      (Nat.max sz0 width) }
  | PrimTyped.ZExtR (sz0, width) ->
    { argSigs = (vect_cons 0 sz0 (Obj.magic __)); retSig =
      (Nat.max sz0 width) }
  | PrimTyped.Repeat (sz0, times) ->
    { argSigs = (vect_cons 0 sz0 (Obj.magic __)); retSig = (mul times sz0) }
  | PrimTyped.Slice (sz0, _, width) ->
    { argSigs = (vect_cons 0 sz0 (Obj.magic __)); retSig = width }
  | PrimTyped.Lowered fn0 ->
    (match fn0 with
     | PrimTyped.IgnoreBits sz0 ->
       { argSigs = (vect_cons 0 sz0 (Obj.magic __)); retSig = 0 }
     | PrimTyped.DisplayBits fn3 ->
       cSig_of_Sig (Stdlib.Int.succ 0) (coq_DisplaySigma fn3))

  (** val coq_CSigma2 : PrimTyped.fbits2 -> int _Sig **)

  let coq_CSigma2 = function
  | PrimTyped.And sz0 ->
    { argSigs =
      (vect_cons (Stdlib.Int.succ 0) sz0 (vect_cons 0 sz0 (Obj.magic __)));
      retSig = sz0 }
  | PrimTyped.Or sz0 ->
    { argSigs =
      (vect_cons (Stdlib.Int.succ 0) sz0 (vect_cons 0 sz0 (Obj.magic __)));
      retSig = sz0 }
  | PrimTyped.Xor sz0 ->
    { argSigs =
      (vect_cons (Stdlib.Int.succ 0) sz0 (vect_cons 0 sz0 (Obj.magic __)));
      retSig = sz0 }
  | PrimTyped.Lsl (bits_sz, shift_sz) ->
    { argSigs =
      (vect_cons (Stdlib.Int.succ 0) bits_sz
        (vect_cons 0 shift_sz (Obj.magic __))); retSig = bits_sz }
  | PrimTyped.Lsr (bits_sz, shift_sz) ->
    { argSigs =
      (vect_cons (Stdlib.Int.succ 0) bits_sz
        (vect_cons 0 shift_sz (Obj.magic __))); retSig = bits_sz }
  | PrimTyped.Asr (bits_sz, shift_sz) ->
    { argSigs =
      (vect_cons (Stdlib.Int.succ 0) bits_sz
        (vect_cons 0 shift_sz (Obj.magic __))); retSig = bits_sz }
  | PrimTyped.Concat (sz1, sz2) ->
    { argSigs =
      (vect_cons (Stdlib.Int.succ 0) sz1 (vect_cons 0 sz2 (Obj.magic __)));
      retSig = (add sz2 sz1) }
  | PrimTyped.Sel sz0 ->
    { argSigs =
      (vect_cons (Stdlib.Int.succ 0) sz0
        (vect_cons 0 (Nat.log2_up sz0) (Obj.magic __))); retSig =
      (Stdlib.Int.succ 0) }
  | PrimTyped.SliceSubst (sz0, _, width) ->
    { argSigs =
      (vect_cons (Stdlib.Int.succ 0) sz0 (vect_cons 0 width (Obj.magic __)));
      retSig = sz0 }
  | PrimTyped.IndexedSlice (sz0, width) ->
    { argSigs =
      (vect_cons (Stdlib.Int.succ 0) sz0
        (vect_cons 0 (Nat.log2_up sz0) (Obj.magic __))); retSig = width }
  | PrimTyped.Plus sz0 ->
    { argSigs =
      (vect_cons (Stdlib.Int.succ 0) sz0 (vect_cons 0 sz0 (Obj.magic __)));
      retSig = sz0 }
  | PrimTyped.Minus sz0 ->
    { argSigs =
      (vect_cons (Stdlib.Int.succ 0) sz0 (vect_cons 0 sz0 (Obj.magic __)));
      retSig = sz0 }
  | PrimTyped.Mul (sz1, sz2) ->
    { argSigs =
      (vect_cons (Stdlib.Int.succ 0) sz1 (vect_cons 0 sz2 (Obj.magic __)));
      retSig = (add sz1 sz2) }
  | PrimTyped.EqBits (sz0, _) ->
    { argSigs =
      (vect_cons (Stdlib.Int.succ 0) sz0 (vect_cons 0 sz0 (Obj.magic __)));
      retSig = (Stdlib.Int.succ 0) }
  | PrimTyped.Compare (_, _, sz0) ->
    { argSigs =
      (vect_cons (Stdlib.Int.succ 0) sz0 (vect_cons 0 sz0 (Obj.magic __)));
      retSig = (Stdlib.Int.succ 0) }
 end

module PrimSignatures =
 struct
  (** val coq_Sigma1 : PrimTyped.fn1 -> type0 _Sig **)

  let coq_Sigma1 = function
  | PrimTyped.Display fn0 -> CircuitSignatures.coq_DisplaySigma fn0
  | PrimTyped.Conv (tau, fn0) ->
    (match fn0 with
     | PrimTyped.Pack ->
       { argSigs = (vect_cons 0 tau (Obj.magic __)); retSig = (Bits_t
         (type_sz tau)) }
     | PrimTyped.Unpack ->
       { argSigs = (vect_cons 0 (Bits_t (type_sz tau)) (Obj.magic __));
         retSig = tau }
     | PrimTyped.Ignore ->
       { argSigs = (vect_cons 0 tau (Obj.magic __)); retSig = (Bits_t 0) })
  | PrimTyped.Bits1 fn0 ->
    sig_of_CSig (Stdlib.Int.succ 0) (CircuitSignatures.coq_CSigma1 fn0)
  | PrimTyped.Struct1 (sig0, idx) ->
    { argSigs = (vect_cons 0 (Struct_t sig0) (Obj.magic __)); retSig =
      (field_type sig0 idx) }
  | PrimTyped.Array1 (sig0, _) ->
    { argSigs = (vect_cons 0 (Array_t sig0) (Obj.magic __)); retSig =
      sig0.array_type }

  (** val coq_Sigma2 : PrimTyped.fn2 -> type0 _Sig **)

  let coq_Sigma2 = function
  | PrimTyped.Eq (tau, _) ->
    { argSigs =
      (vect_cons (Stdlib.Int.succ 0) tau (vect_cons 0 tau (Obj.magic __)));
      retSig = (Bits_t (Stdlib.Int.succ 0)) }
  | PrimTyped.Bits2 fn0 ->
    sig_of_CSig (Stdlib.Int.succ (Stdlib.Int.succ 0))
      (CircuitSignatures.coq_CSigma2 fn0)
  | PrimTyped.Struct2 (sig0, idx) ->
    { argSigs =
      (vect_cons (Stdlib.Int.succ 0) (Struct_t sig0)
        (vect_cons 0 (field_type sig0 idx) (Obj.magic __))); retSig =
      (Struct_t sig0) }
  | PrimTyped.Array2 (sig0, _) ->
    { argSigs =
      (vect_cons (Stdlib.Int.succ 0) (Array_t sig0)
        (vect_cons 0 sig0.array_type (Obj.magic __))); retSig = (Array_t
      sig0) }
 end

type ('from, 'to0) lift = 'from -> 'to0

type ('pos_t, 'var_t, 'fn_name_t, 'reg_t, 'ext_fn_t) uaction =
| UError of ('pos_t, 'var_t, 'fn_name_t) error
| UFail of type0
| UVar of 'var_t
| UConst of type0 * type_denote
| UAssign of 'var_t * ('pos_t, 'var_t, 'fn_name_t, 'reg_t, 'ext_fn_t) uaction
| USeq of ('pos_t, 'var_t, 'fn_name_t, 'reg_t, 'ext_fn_t) uaction
   * ('pos_t, 'var_t, 'fn_name_t, 'reg_t, 'ext_fn_t) uaction
| UBind of 'var_t * ('pos_t, 'var_t, 'fn_name_t, 'reg_t, 'ext_fn_t) uaction
   * ('pos_t, 'var_t, 'fn_name_t, 'reg_t, 'ext_fn_t) uaction
| UIf of ('pos_t, 'var_t, 'fn_name_t, 'reg_t, 'ext_fn_t) uaction
   * ('pos_t, 'var_t, 'fn_name_t, 'reg_t, 'ext_fn_t) uaction
   * ('pos_t, 'var_t, 'fn_name_t, 'reg_t, 'ext_fn_t) uaction
| URead of port * 'reg_t
| UWrite of port * 'reg_t
   * ('pos_t, 'var_t, 'fn_name_t, 'reg_t, 'ext_fn_t) uaction
| UUnop of PrimUntyped.ufn1
   * ('pos_t, 'var_t, 'fn_name_t, 'reg_t, 'ext_fn_t) uaction
| UBinop of PrimUntyped.ufn2
   * ('pos_t, 'var_t, 'fn_name_t, 'reg_t, 'ext_fn_t) uaction
   * ('pos_t, 'var_t, 'fn_name_t, 'reg_t, 'ext_fn_t) uaction
| UExternalCall of 'ext_fn_t
   * ('pos_t, 'var_t, 'fn_name_t, 'reg_t, 'ext_fn_t) uaction
| UInternalCall of ('var_t, 'fn_name_t, ('pos_t, 'var_t, 'fn_name_t, 'reg_t,
                   'ext_fn_t) uaction) internalFunction
   * ('pos_t, 'var_t, 'fn_name_t, 'reg_t, 'ext_fn_t) uaction list
| UAPos of 'pos_t * ('pos_t, 'var_t, 'fn_name_t, 'reg_t, 'ext_fn_t) uaction
| USugar of ('pos_t, 'var_t, 'fn_name_t, 'reg_t, 'ext_fn_t) usugar
and ('pos_t, 'var_t, 'fn_name_t, 'reg_t, 'ext_fn_t) usugar =
| UErrorInAst
| USkip
| UConstBits of int * bool vect
| UConstString of char list
| UConstEnum of enum_sig * char list
| UProgn of ('pos_t, 'var_t, 'fn_name_t, 'reg_t, 'ext_fn_t) uaction list
| ULet of ('var_t * ('pos_t, 'var_t, 'fn_name_t, 'reg_t, 'ext_fn_t) uaction)
          list * ('pos_t, 'var_t, 'fn_name_t, 'reg_t, 'ext_fn_t) uaction
| UWhen of ('pos_t, 'var_t, 'fn_name_t, 'reg_t, 'ext_fn_t) uaction
   * ('pos_t, 'var_t, 'fn_name_t, 'reg_t, 'ext_fn_t) uaction
| USwitch of ('pos_t, 'var_t, 'fn_name_t, 'reg_t, 'ext_fn_t) uaction
   * ('pos_t, 'var_t, 'fn_name_t, 'reg_t, 'ext_fn_t) uaction
   * (('pos_t, 'var_t, 'fn_name_t, 'reg_t, 'ext_fn_t) uaction * ('pos_t,
     'var_t, 'fn_name_t, 'reg_t, 'ext_fn_t) uaction) list
| UStructInit of type0 struct_sig'
   * (char list * ('pos_t, 'var_t, 'fn_name_t, 'reg_t, 'ext_fn_t) uaction)
     list
| UArrayInit of type0
   * ('pos_t, 'var_t, 'fn_name_t, 'reg_t, 'ext_fn_t) uaction list
| UCallModule of (__ -> 'reg_t) * (__, 'ext_fn_t) lift
   * ('var_t, 'fn_name_t, ('pos_t, 'var_t, 'fn_name_t, __, __) uaction)
     internalFunction
   * ('pos_t, 'var_t, 'fn_name_t, 'reg_t, 'ext_fn_t) uaction list

type ('pos_t, 'rule_name_t) scheduler =
| Done
| Cons of 'rule_name_t * ('pos_t, 'rule_name_t) scheduler
| Try of 'rule_name_t * ('pos_t, 'rule_name_t) scheduler
   * ('pos_t, 'rule_name_t) scheduler
| SPos of 'pos_t * ('pos_t, 'rule_name_t) scheduler

type ('pos_t, 'var_t, 'fn_name_t, 'reg_t, 'ext_fn_t) action =
| Fail of 'var_t tsig * type0
| Var of ('var_t * type0) list * 'var_t * type0 * ('var_t * type0) member
| Const of 'var_t tsig * type0 * type_denote
| Assign of ('var_t * type0) list * 'var_t * type0 * ('var_t * type0) member
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
| InternalCall of 'var_t tsig * type0 * 'fn_name_t * 'var_t tsig
   * ('var_t * type0, ('pos_t, 'var_t, 'fn_name_t, 'reg_t, 'ext_fn_t) action)
     context * ('pos_t, 'var_t, 'fn_name_t, 'reg_t, 'ext_fn_t) action
| APos of 'var_t tsig * type0 * 'pos_t
   * ('pos_t, 'var_t, 'fn_name_t, 'reg_t, 'ext_fn_t) action

type ('pos_t, 'var_t, 'fn_name_t, 'reg_t, 'ext_fn_t) rule =
  ('pos_t, 'var_t, 'fn_name_t, 'reg_t, 'ext_fn_t) action

(** val bits_of_ascii : char -> bool vect **)

let bits_of_ascii c =
  (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
    (fun b0 b1 b2 b3 b4 b5 b6 b7 ->
    vect_cons (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      0))))))) b0
      (vect_cons (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0)))))) b1
        (vect_cons (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
          (Stdlib.Int.succ (Stdlib.Int.succ 0))))) b2
          (vect_cons (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
            (Stdlib.Int.succ 0)))) b3
            (vect_cons (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
              0))) b4
              (vect_cons (Stdlib.Int.succ (Stdlib.Int.succ 0)) b5
                (vect_cons (Stdlib.Int.succ 0) b6
                  (vect_cons 0 b7 (Obj.magic __)))))))))
    c

(** val array_of_bytes : char list -> bool vect vect **)

let rec array_of_bytes = function
| [] -> Obj.magic __
| c::s0 -> vect_cons (length0 s0) (bits_of_ascii c) (array_of_bytes s0)

(** val uprogn :
    ('a1, 'a2, 'a3, 'a4, 'a5) uaction list -> ('a1, 'a2, 'a3, 'a4, 'a5)
    uaction **)

let rec uprogn = function
| [] -> UConst ((Bits_t 0), (Obj.magic __))
| a :: aa0 -> (match aa0 with
               | [] -> a
               | _ :: _ -> USeq (a, (uprogn aa0)))

(** val uskip : ('a1, 'a2, 'a3, 'a4, 'a5) uaction **)

let uskip =
  UConst ((Bits_t 0), (Obj.magic __))

(** val uinit : type0 -> ('a1, 'a2, 'a3, 'a4, 'a5) uaction **)

let uinit tau =
  let zeroes = UConst ((Bits_t (type_sz tau)),
    (vect_const (type_sz tau) false))
  in
  UUnop ((PrimUntyped.UConv (PrimUntyped.UUnpack tau)), zeroes)

(** val ustruct_init :
    type0 struct_sig' -> (char list * ('a1, 'a2, 'a3, 'a4, 'a5) uaction) list
    -> ('a1, 'a2, 'a3, 'a4, 'a5) uaction **)

let ustruct_init sig0 fields =
  let empty = uinit (Struct_t sig0) in
  let usubst = fun f x x0 -> UBinop ((PrimUntyped.UStruct2
    (PrimUntyped.USubstField f)), x, x0)
  in
  fold_left (fun acc pat -> let (f, a) = pat in usubst f acc a) fields empty

(** val uswitch :
    ('a1, 'a2, 'a3, 'a4, 'a5) uaction -> ('a1, 'a2, 'a3, 'a4, 'a5) uaction ->
    (('a1, 'a2, 'a3, 'a4, 'a5) uaction * ('a1, 'a2, 'a3, 'a4, 'a5) uaction)
    list -> ('a1, 'a2, 'a3, 'a4, 'a5) uaction **)

let rec uswitch var default = function
| [] -> default
| p :: branches0 ->
  let (label, action0) = p in
  UIf ((UBinop ((PrimUntyped.UEq false), var, label)), action0,
  (uswitch var default branches0))

(** val desugar_action' :
    'a1 -> ('a6 -> 'a4) -> ('a7 -> 'a5) -> ('a1, 'a2, 'a3, 'a6, 'a7) uaction
    -> ('a1, 'a2, 'a3, 'a4, 'a5) uaction **)

let desugar_action' =
  let rec desugar_action'0 pos fR fSigma a =
    let d = fun a0 -> desugar_action'0 pos fR fSigma a0 in
    (match a with
     | UError err -> UError err
     | UFail tau -> UFail tau
     | UVar var -> UVar var
     | UConst (tau, cst) -> UConst (tau, cst)
     | UAssign (v, ex) -> UAssign (v, (d ex))
     | USeq (a1, a2) -> USeq ((d a1), (d a2))
     | UBind (v, ex, body) -> UBind (v, (d ex), (d body))
     | UIf (cond, tbranch, fbranch) ->
       UIf ((d cond), (d tbranch), (d fbranch))
     | URead (port0, idx) -> URead (port0, (fR idx))
     | UWrite (port0, idx, value) -> UWrite (port0, (fR idx), (d value))
     | UUnop (fn, arg) -> UUnop (fn, (d arg))
     | UBinop (fn, arg1, arg2) -> UBinop (fn, (d arg1), (d arg2))
     | UExternalCall (fn, arg) -> UExternalCall ((fSigma fn), (d arg))
     | UInternalCall (fn, args) ->
       UInternalCall ((map_intf_body d fn), (map d args))
     | UAPos (p, e) -> UAPos (p, (d e))
     | USugar s -> desugar __ __ pos fR fSigma s)
  and desugar _ _ pos fR fSigma s =
    let d = fun a -> desugar_action'0 pos fR fSigma a in
    (match s with
     | UErrorInAst -> UError { epos = pos; emsg = ExplicitErrorInAst }
     | USkip -> uskip
     | UConstBits (sz0, bs) -> UConst ((Bits_t sz0), bs)
     | UConstString s0 ->
       UConst ((Array_t { array_type = (Bits_t (Stdlib.Int.succ
         (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
         (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0)))))))));
         array_len = (length0 s0) }), (array_of_bytes s0))
     | UConstEnum (sig0, name) ->
       (match vect_index sig0.enum_size eqDec_string name sig0.enum_members with
        | Some idx ->
          UConst ((Enum_t sig0),
            (vect_nth sig0.enum_size sig0.enum_bitpatterns idx))
        | None ->
          UError { epos = pos; emsg = (UnboundEnumMember (name, sig0)) })
     | UProgn aa -> uprogn (map d aa)
     | ULet (bindings, body) ->
       fold_right (fun pat acc ->
         let (var, a) = pat in UBind (var, (d a), acc)) (d body) bindings
     | UWhen (cond, body) -> UIf ((d cond), (d body), (UFail (Bits_t 0)))
     | USwitch (var, default, branches) ->
       let branches0 =
         map (fun pat -> let (cond, body) = pat in ((d cond), (d body)))
           branches
       in
       uswitch (d var) (d default) branches0
     | UStructInit (sig0, fields) ->
       let fields0 = map (fun pat -> let (f, a) = pat in (f, (d a))) fields in
       ustruct_init sig0 fields0
     | UArrayInit (tau, elements) ->
       let sig0 = { array_type = tau; array_len = (length elements) } in
       let usubst = fun pos0 x x0 -> UBinop ((PrimUntyped.UArray2
         (PrimUntyped.USubstElement pos0)), x, x0)
       in
       let empty = uinit (Array_t sig0) in
       snd
         (fold_left (fun pat a ->
           let (pos0, acc) = pat in
           ((Stdlib.Int.succ pos0), (usubst pos0 acc (d a)))) elements (0,
           empty))
     | UCallModule (fR', fSigma', fn, args) ->
       let df = fun body ->
         Obj.magic desugar_action'0 pos (fun r0 -> fR (fR' r0)) (fun fn0 ->
           fSigma (fSigma' fn0)) body
       in
       UInternalCall ((map_intf_body df fn), (map d args)))
  in desugar_action'0

(** val desugar_action :
    'a1 -> ('a1, 'a2, 'a3, 'a4, 'a5) uaction -> ('a1, 'a2, 'a3, 'a4, 'a5)
    uaction **)

let desugar_action pos a =
  desugar_action' pos (fun r0 -> r0) (fun fn -> fn) a

(** val lift_basic_error_message :
    ('a4 -> type0) -> ('a5 -> externalSignature) -> 'a1 -> 'a2 tsig -> type0
    -> ('a1, 'a2, 'a3, 'a4, 'a5) action -> basic_error_message -> ('a1, 'a2,
    'a3) error **)

let lift_basic_error_message _ _ pos _ _ _ err =
  { epos = pos; emsg = (BasicError err) }

(** val lift_fn1_tc_result :
    ('a4 -> type0) -> ('a5 -> externalSignature) -> 'a2 tsig -> type0 -> 'a1
    -> ('a1, 'a2, 'a3, 'a4, 'a5) action -> ('a6, fn_tc_error) result -> ('a6,
    ('a1, 'a2, 'a3) error) result **)

let lift_fn1_tc_result r0 sigma sig0 tau pos e r1 =
  result_map_failure (fun pat ->
    let (_, err) = pat in lift_basic_error_message r0 sigma pos sig0 tau e err)
    r1

(** val lift_fn2_tc_result :
    ('a4 -> type0) -> ('a5 -> externalSignature) -> 'a2 tsig -> type0 -> 'a2
    tsig -> type0 -> 'a1 -> ('a1, 'a2, 'a3, 'a4, 'a5) action -> 'a1 -> ('a1,
    'a2, 'a3, 'a4, 'a5) action -> ('a6, fn_tc_error) result -> ('a6, ('a1,
    'a2, 'a3) error) result **)

let lift_fn2_tc_result r0 sigma sig1 tau1 sig2 tau2 pos1 e1 pos2 e2 r1 =
  result_map_failure (fun pat ->
    let (side, err) = pat in
    (match side with
     | Arg1 -> lift_basic_error_message r0 sigma pos1 sig1 tau1 e1 err
     | Arg2 -> lift_basic_error_message r0 sigma pos2 sig2 tau2 e2 err)) r1

(** val mkerror :
    'a1 -> ('a3, 'a2) error_message -> 'a4 -> ('a1, 'a3, 'a2) error **)

let mkerror pos msg _ =
  { epos = pos; emsg = msg }

(** val cast_action' :
    ('a4 -> type0) -> ('a5 -> externalSignature) -> 'a1 -> 'a3 tsig -> type0
    -> type0 -> ('a1, 'a3, 'a2, 'a4, 'a5) action -> ('a3, 'a2) error_message
    -> (('a1, 'a3, 'a2, 'a4, 'a5) action, ('a1, 'a3, 'a2) error) result **)

let cast_action' _ _ pos _ tau1 tau2 e emsg0 =
  let s = eqDec_type.eq_dec tau1 tau2 in
  if s then Success e else Failure (mkerror pos emsg0 e)

(** val cast_action :
    ('a4 -> type0) -> ('a5 -> externalSignature) -> 'a1 -> 'a3 tsig -> type0
    -> type0 -> ('a1, 'a3, 'a2, 'a4, 'a5) action -> (('a1, 'a3, 'a2, 'a4,
    'a5) action, ('a1, 'a3, 'a2) error) result **)

let cast_action r0 sigma pos sig0 tau1 tau2 e =
  cast_action' r0 sigma pos sig0 tau1 tau2 e (BasicError (TypeMismatch (tau1,
    tau2)))

(** val actpos : 'a1 -> ('a1, 'a3, 'a2, 'a4, 'a5) uaction -> 'a1 **)

let actpos pos = function
| UAPos (p, _) -> p
| _ -> pos

(** val assert_argtypes' :
    ('a4 -> type0) -> ('a5 -> externalSignature) -> 'a3 tsig -> 'a6 -> int ->
    'a2 -> 'a1 -> 'a3 tsig -> ('a1 * (type0, ('a1, 'a3, 'a2, 'a4, 'a5)
    action) sigT) list -> (('a3 * type0, ('a1, 'a3, 'a2, 'a4, 'a5) action)
    context, ('a1, 'a3, 'a2) error) result **)

let rec assert_argtypes' r0 sigma sig0 src nexpected fn_name pos args_desc args =
  match args_desc with
  | [] ->
    (match args with
     | [] -> Success CtxEmpty
     | _ :: _ ->
       Failure
         (mkerror pos (TooManyArguments (fn_name, nexpected, (length args)))
           src))
  | p :: fn_sig ->
    let (name1, tau1) = p in
    (match args with
     | [] ->
       Failure
         (mkerror pos (TooFewArguments (fn_name, nexpected,
           (length args_desc))) src)
     | p0 :: args0 ->
       let (pos1, arg1) = p0 in
       (match cast_action r0 sigma pos1 sig0 (projT1 arg1) tau1 (projT2 arg1) with
        | Success arg2 ->
          (match assert_argtypes' r0 sigma sig0 src nexpected fn_name pos
                   fn_sig args0 with
           | Success ctx ->
             Success (CtxCons (fn_sig, (name1, tau1), arg2, ctx))
           | Failure f -> Failure f)
        | Failure f -> Failure f))

(** val assert_argtypes :
    ('a4 -> type0) -> ('a5 -> externalSignature) -> 'a3 tsig -> 'a6 -> 'a2 ->
    'a1 -> 'a3 tsig -> ('a1 * (type0, ('a1, 'a3, 'a2, 'a4, 'a5) action) sigT)
    list -> (('a3 * type0, ('a1, 'a3, 'a2, 'a4, 'a5) action) context, ('a1,
    'a3, 'a2) error) result **)

let assert_argtypes r0 sigma sig0 src fn_name pos args_desc args =
  assert_argtypes' r0 sigma sig0 src (length args_desc) fn_name pos args_desc
    args

(** val type_action :
    'a3 eqDec -> ('a4 -> type0) -> ('a5 -> externalSignature) -> 'a1 -> 'a3
    tsig -> ('a1, 'a3, 'a2, 'a4, 'a5) uaction -> ((type0, ('a1, 'a3, 'a2,
    'a4, 'a5) action) sigT, ('a1, 'a3, 'a2) error) result **)

let rec type_action var_t_eq_dec r0 sigma pos sig0 e = match e with
| UError err -> Failure err
| UFail tau -> Success (ExistT (tau, (Fail (sig0, tau))))
| UVar var ->
  (match opt_result (assoc var_t_eq_dec var sig0)
           (mkerror pos (UnboundVariable var) e) with
   | Success tau_m ->
     Success (ExistT ((projT1 tau_m), (Var (sig0, var, (projT1 tau_m),
       (projT2 tau_m)))))
   | Failure f -> Failure f)
| UConst (tau, cst) -> Success (ExistT (tau, (Const (sig0, tau, cst))))
| UAssign (var, ex) ->
  (match opt_result (assoc var_t_eq_dec var sig0)
           (mkerror pos (UnboundVariable var) e) with
   | Success tau_m ->
     (match type_action var_t_eq_dec r0 sigma pos sig0 ex with
      | Success ex' ->
        (match cast_action r0 sigma (actpos pos ex) sig0 (projT1 ex')
                 (projT1 tau_m) (projT2 ex') with
         | Success ex'0 ->
           Success (ExistT ((Bits_t 0), (Assign (sig0, var, (projT1 tau_m),
             (projT2 tau_m), ex'0))))
         | Failure f -> Failure f)
      | Failure f -> Failure f)
   | Failure f -> Failure f)
| USeq (r1, r2) ->
  (match type_action var_t_eq_dec r0 sigma pos sig0 r1 with
   | Success r1' ->
     (match cast_action r0 sigma (actpos pos r1) sig0 (projT1 r1') (Bits_t 0)
              (projT2 r1') with
      | Success r1'0 ->
        (match type_action var_t_eq_dec r0 sigma pos sig0 r2 with
         | Success r2' ->
           Success (ExistT ((projT1 r2'), (Seq (sig0, (projT1 r2'), r1'0,
             (projT2 r2')))))
         | Failure f -> Failure f)
      | Failure f -> Failure f)
   | Failure f -> Failure f)
| UBind (v, ex, body) ->
  (match type_action var_t_eq_dec r0 sigma pos sig0 ex with
   | Success ex0 ->
     (match type_action var_t_eq_dec r0 sigma pos ((v, (projT1 ex0)) :: sig0)
              body with
      | Success body0 ->
        Success (ExistT ((projT1 body0), (Bind (sig0, (projT1 ex0),
          (projT1 body0), v, (projT2 ex0), (projT2 body0)))))
      | Failure f -> Failure f)
   | Failure f -> Failure f)
| UIf (cond, tbranch, fbranch) ->
  (match type_action var_t_eq_dec r0 sigma pos sig0 cond with
   | Success cond' ->
     (match cast_action r0 sigma (actpos pos cond) sig0 (projT1 cond')
              (Bits_t (Stdlib.Int.succ 0)) (projT2 cond') with
      | Success cond'0 ->
        (match type_action var_t_eq_dec r0 sigma pos sig0 tbranch with
         | Success tbranch' ->
           (match type_action var_t_eq_dec r0 sigma pos sig0 fbranch with
            | Success fbranch' ->
              (match cast_action r0 sigma (actpos pos fbranch) sig0
                       (projT1 fbranch') (projT1 tbranch') (projT2 fbranch') with
               | Success fbranch'0 ->
                 Success (ExistT ((projT1 tbranch'), (If (sig0,
                   (projT1 tbranch'), cond'0, (projT2 tbranch'), fbranch'0))))
               | Failure f -> Failure f)
            | Failure f -> Failure f)
         | Failure f -> Failure f)
      | Failure f -> Failure f)
   | Failure f -> Failure f)
| URead (port0, idx) -> Success (ExistT ((r0 idx), (Read (sig0, port0, idx))))
| UWrite (port0, idx, value) ->
  (match type_action var_t_eq_dec r0 sigma pos sig0 value with
   | Success value' ->
     (match cast_action r0 sigma (actpos pos value) sig0 (projT1 value')
              (r0 idx) (projT2 value') with
      | Success value'0 ->
        Success (ExistT ((Bits_t 0), (Write (sig0, port0, idx, value'0))))
      | Failure f -> Failure f)
   | Failure f -> Failure f)
| UUnop (fn, arg1) ->
  let pos1 = actpos pos arg1 in
  (match type_action var_t_eq_dec r0 sigma pos sig0 arg1 with
   | Success arg1' ->
     (match lift_fn1_tc_result r0 sigma sig0 (projT1 arg1') pos1
              (projT2 arg1') (PrimTypeInference.tc1 fn (projT1 arg1')) with
      | Success fn0 ->
        (match cast_action r0 sigma pos1 sig0 (projT1 arg1')
                 (vect_hd 0 (PrimSignatures.coq_Sigma1 fn0).argSigs)
                 (projT2 arg1') with
         | Success arg1'0 ->
           Success (ExistT ((PrimSignatures.coq_Sigma1 fn0).retSig, (Unop
             (sig0, fn0, arg1'0))))
         | Failure f -> Failure f)
      | Failure f -> Failure f)
   | Failure f -> Failure f)
| UBinop (fn, arg1, arg2) ->
  let pos1 = actpos pos arg1 in
  let pos2 = actpos pos arg2 in
  (match type_action var_t_eq_dec r0 sigma pos sig0 arg1 with
   | Success arg1' ->
     (match type_action var_t_eq_dec r0 sigma pos sig0 arg2 with
      | Success arg2' ->
        (match lift_fn2_tc_result r0 sigma sig0 (projT1 arg1') sig0
                 (projT1 arg2') pos1 (projT2 arg1') pos2 (projT2 arg2')
                 (PrimTypeInference.tc2 fn (projT1 arg1') (projT1 arg2')) with
         | Success fn0 ->
           (match cast_action r0 sigma pos1 sig0 (projT1 arg1')
                    (vect_hd (Stdlib.Int.succ 0)
                      (PrimSignatures.coq_Sigma2 fn0).argSigs) (projT2 arg1') with
            | Success arg1'0 ->
              (match cast_action r0 sigma pos2 sig0 (projT1 arg2')
                       (vect_hd 0
                         (vect_tl (Stdlib.Int.succ 0)
                           (PrimSignatures.coq_Sigma2 fn0).argSigs))
                       (projT2 arg2') with
               | Success arg2'0 ->
                 Success (ExistT ((PrimSignatures.coq_Sigma2 fn0).retSig,
                   (Binop (sig0, fn0, arg1'0, arg2'0))))
               | Failure f -> Failure f)
            | Failure f -> Failure f)
         | Failure f -> Failure f)
      | Failure f -> Failure f)
   | Failure f -> Failure f)
| UExternalCall (fn, arg1) ->
  let pos1 = actpos pos arg1 in
  (match type_action var_t_eq_dec r0 sigma pos1 sig0 arg1 with
   | Success arg1' ->
     (match cast_action r0 sigma pos1 sig0 (projT1 arg1')
              (vect_hd 0 (sigma fn).argSigs) (projT2 arg1') with
      | Success arg1'0 ->
        Success (ExistT ((sigma fn).retSig, (ExternalCall (sig0, fn,
          arg1'0))))
      | Failure f -> Failure f)
   | Failure f -> Failure f)
| UInternalCall (fn, args) ->
  (match result_list_map (type_action var_t_eq_dec r0 sigma pos sig0) args with
   | Success tc_args ->
     let arg_positions = map (actpos pos) args in
     let tc_args_w_pos = combine arg_positions tc_args in
     (match assert_argtypes r0 sigma sig0 e fn.int_name pos
              (rev fn.int_argspec) (rev tc_args_w_pos) with
      | Success args_ctx ->
        (match type_action var_t_eq_dec r0 sigma (actpos pos fn.int_body)
                 (rev fn.int_argspec) fn.int_body with
         | Success fn_body' ->
           (match cast_action r0 sigma (actpos pos fn.int_body)
                    (rev fn.int_argspec) (projT1 fn_body') fn.int_retSig
                    (projT2 fn_body') with
            | Success fn_body'0 ->
              Success (ExistT (fn.int_retSig, (InternalCall (sig0,
                fn.int_retSig, fn.int_name, fn.int_argspec, args_ctx,
                fn_body'0))))
            | Failure f -> Failure f)
         | Failure f -> Failure f)
      | Failure f -> Failure f)
   | Failure f -> Failure f)
| UAPos (pos0, e0) ->
  (match type_action var_t_eq_dec r0 sigma pos0 sig0 e0 with
   | Success e1 ->
     Success (ExistT ((projT1 e1), (APos (sig0, (projT1 e1), pos0,
       (projT2 e1)))))
   | Failure f -> Failure f)
| USugar _ -> Failure (mkerror pos SugaredConstructorInAst e)

(** val tc_action :
    'a3 eqDec -> ('a4 -> type0) -> ('a5 -> externalSignature) -> 'a1 -> 'a3
    tsig -> type0 -> ('a1, 'a3, 'a2, 'a4, 'a5) uaction -> (('a1, 'a3, 'a2,
    'a4, 'a5) action, ('a1, 'a3, 'a2) error) result **)

let tc_action var_t_eq_dec r0 sigma pos sig0 expected_tau e =
  match type_action var_t_eq_dec r0 sigma pos sig0 e with
  | Success a ->
    cast_action r0 sigma pos sig0 (projT1 a) expected_tau (projT2 a)
  | Failure f -> Failure f

type ext_fn_rtl_spec = { efr_name : char list; efr_internal : bool }

type ext_fn_sim_spec = { efs_name : char list; efs_method : bool }

type ('pos_t, 'var_t, 'fn_name_t, 'rule_name_t, 'reg_t, 'ext_fn_t) koika_package_t = { 
koika_var_names : 'var_t show; koika_fn_names : 'fn_name_t show;
koika_reg_names : 'reg_t show; koika_reg_types : ('reg_t -> type0);
koika_reg_init : ('reg_t -> type_denote);
koika_reg_finite : 'reg_t finiteType;
koika_ext_fn_types : ('ext_fn_t -> externalSignature);
koika_rules : ('rule_name_t -> ('pos_t, 'var_t, 'fn_name_t, 'reg_t,
              'ext_fn_t) rule); koika_rule_external : ('rule_name_t -> bool);
koika_rule_names : 'rule_name_t show;
koika_scheduler : ('pos_t, 'rule_name_t) scheduler;
koika_module_name : char list }

type 'ext_fn_t verilog_package_t = { vp_ext_fn_specs : ('ext_fn_t ->
                                                       ext_fn_rtl_spec) }

type 'ext_fn_t sim_package_t = { sp_ext_fn_specs : ('ext_fn_t ->
                                                   ext_fn_sim_spec);
                                 sp_prelude : char list option }

type interop_package_t = { ip_koika : (unit, char list, char list, __, __,
                                      __) koika_package_t;
                           ip_verilog : __ verilog_package_t;
                           ip_sim : __ sim_package_t }

module Backends =
 struct
  (** val register : interop_package_t -> unit **)

  let register = fun ip -> Registry.register (Obj.magic ip)
 end

type 'pos_t dummyPos = { dummy_pos : 'pos_t }

(** val dummyPos_unit : unit dummyPos **)

let dummyPos_unit =
  { dummy_pos = () }

type pos_t = unit

type var_t = char list

type fn_name_t = char list

module Types =
 struct
  (** val sz : int **)

  let sz =
    Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ 0)))))))))))))

  (** val basic_flit : type0 struct_sig' **)

  let basic_flit =
    { struct_name =
      ('b'::('a'::('s'::('i'::('c'::('_'::('f'::('l'::('i'::('t'::[]))))))))));
      struct_fields = ((('n'::('e'::('w'::[]))), (Bits_t (Stdlib.Int.succ
      0))) :: ((('s'::('r'::('c'::[]))), (Bits_t (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      0)))))) :: ((('t'::('r'::('g'::('_'::('y'::[]))))), (Bits_t
      (Stdlib.Int.succ (Stdlib.Int.succ
      0)))) :: ((('t'::('r'::('g'::('_'::('x'::[]))))), (Bits_t
      (Stdlib.Int.succ (Stdlib.Int.succ
      0)))) :: ((('d'::('a'::('t'::('a'::[])))), (Bits_t (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      0))))))) :: []))))) }

  (** val router_address : type0 struct_sig' **)

  let router_address =
    { struct_name =
      ('r'::('o'::('u'::('t'::('e'::('r'::('_'::('a'::('d'::('d'::('r'::('e'::('s'::('s'::[]))))))))))))));
      struct_fields = ((('y'::[]), (Bits_t (Stdlib.Int.succ (Stdlib.Int.succ
      0)))) :: ((('x'::[]), (Bits_t (Stdlib.Int.succ (Stdlib.Int.succ
      0)))) :: [])) }
 end

module type Registers =
 sig
  type reg_t
 end

module Router =
 functor (Regs:Registers) ->
 struct
  (** val ext_fn_t_rect : 'a1 -> 'a1 **)

  let ext_fn_t_rect f =
    f

  (** val ext_fn_t_rec : 'a1 -> 'a1 **)

  let ext_fn_t_rec f =
    f

  (** val coq_Sigma : __ -> externalSignature **)

  let coq_Sigma _ =
    { argSigs = (vect_cons 0 (Bits_t Types.sz) (Obj.magic __)); retSig =
      (Bits_t Types.sz) }

  (** val fnsigma : __ -> sig_denote **)

  let fnsigma _ =
    Obj.magic (fun x -> x)

  (** val to_tile :
      (var_t, fn_name_t, (pos_t, var_t, fn_name_t, Regs.reg_t, __) uaction)
      internalFunction **)

  let to_tile =
    { int_name = ('t'::('o'::('_'::('t'::('i'::('l'::('e'::[])))))));
      int_argspec =
      ((prod_of_argsig { arg_name = ('v'::('a'::('l'::('u'::('e'::[])))));
         arg_type = (Bits_t Types.sz) }) :: []); int_retSig = (Bits_t 0);
      int_body = (UExternalCall (__, (UVar
      ('v'::('a'::('l'::('u'::('e'::[])))))))) }

  (** val r_send :
      Regs.reg_t -> (var_t, fn_name_t, (pos_t, var_t, fn_name_t, Regs.reg_t,
      __) uaction) internalFunction **)

  let r_send reg_name =
    { int_name = ('r'::('_'::('s'::('e'::('n'::('d'::[])))))); int_argspec =
      ((prod_of_argsig { arg_name = ('v'::('a'::('l'::('u'::('e'::[])))));
         arg_type = (Bits_t Types.sz) }) :: []); int_retSig = (Bits_t 0);
      int_body = (UWrite (P0, reg_name, (UBinop ((PrimUntyped.UBits2
      PrimUntyped.UXor), (UVar ('v'::('a'::('l'::('u'::('e'::[])))))),
      (UExternalCall (__, (USugar (UConstBits ((Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ 0)))))))))))))),
      (Bits.of_N (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0)))))))))))))) 0)))))))))) }

  (** val r_receive :
      Regs.reg_t -> (var_t, fn_name_t, (pos_t, var_t, fn_name_t, Regs.reg_t,
      __) uaction) internalFunction **)

  let r_receive reg_name =
    { int_name =
      ('r'::('_'::('r'::('e'::('c'::('e'::('i'::('v'::('e'::[])))))))));
      int_argspec = []; int_retSig = (Bits_t Types.sz); int_body = (URead
      (P0, reg_name)) }

  (** val _routestart_r :
      int -> (var_t, fn_name_t, (pos_t, var_t, fn_name_t, Regs.reg_t, __)
      uaction) internalFunction -> (var_t, fn_name_t, (pos_t, var_t,
      fn_name_t, Regs.reg_t, __) uaction) internalFunction -> (pos_t, var_t,
      fn_name_t, Regs.reg_t, __) uaction **)

  let _routestart_r r_addr2 r0_send r0_receive =
    UBind (('r'::('_'::('a'::('d'::('d'::('r'::[])))))), (USugar (UConstBits
      ((Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      0)))),
      (Bits.of_nat (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ 0)))) r_addr2)))), (UBind (('m'::('0'::[])), (UBinop
      ((PrimUntyped.UBits2 PrimUntyped.UXor), (USugar (UCallModule
      ((Obj.magic id), (Obj.magic __), (Obj.magic r0_receive), []))),
      (UExternalCall (__, (USugar (UConstBits ((Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ 0)))))))))))))),
      (Bits.of_N (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0)))))))))))))) 0)))))))),
      (UBind (('m'::('s'::('g'::[]))), (UUnop ((PrimUntyped.UConv
      (PrimUntyped.UUnpack (Struct_t Types.basic_flit))), (UVar
      ('m'::('0'::[]))))), (UBind
      (('n'::('e'::('w'::('_'::('d'::('a'::('t'::('a'::[])))))))), (UUnop
      ((PrimUntyped.UStruct1 (PrimUntyped.UGetField
      ('n'::('e'::('w'::[]))))), (UVar ('m'::('s'::('g'::[])))))), (UBind
      (('s'::('r'::('c'::('_'::('p'::[]))))), (UUnop ((PrimUntyped.UStruct1
      (PrimUntyped.UGetField ('s'::('r'::('c'::[]))))), (UVar
      ('m'::('s'::('g'::[])))))), (UIf ((UBinop ((PrimUntyped.UBits2
      PrimUntyped.UAnd), (UBinop ((PrimUntyped.UEq true), (UVar
      ('s'::('r'::('c'::('_'::('p'::[])))))), (UVar
      ('r'::('_'::('a'::('d'::('d'::('r'::[]))))))))), (UVar
      ('n'::('e'::('w'::('_'::('d'::('a'::('t'::('a'::[]))))))))))), (UBind
      (('t'::('r'::('g'::('_'::('x'::[]))))), (UUnop ((PrimUntyped.UStruct1
      (PrimUntyped.UGetField ('t'::('r'::('g'::('_'::('x'::[]))))))), (UVar
      ('m'::('s'::('g'::[])))))), (UBind
      (('t'::('r'::('g'::('_'::('y'::[]))))), (UUnop ((PrimUntyped.UStruct1
      (PrimUntyped.UGetField ('t'::('r'::('g'::('_'::('y'::[]))))))), (UVar
      ('m'::('s'::('g'::[])))))), (UBind
      (('s'::('r'::('c'::('_'::('x'::[]))))), (UUnop ((PrimUntyped.UStruct1
      (PrimUntyped.UGetField ('x'::[]))), (UUnop ((PrimUntyped.UConv
      (PrimUntyped.UUnpack (Struct_t Types.router_address))), (UVar
      ('r'::('_'::('a'::('d'::('d'::('r'::[]))))))))))), (UBind
      (('s'::('r'::('c'::('_'::('y'::[]))))), (UUnop ((PrimUntyped.UStruct1
      (PrimUntyped.UGetField ('y'::[]))), (UUnop ((PrimUntyped.UConv
      (PrimUntyped.UUnpack (Struct_t Types.router_address))), (UVar
      ('r'::('_'::('a'::('d'::('d'::('r'::[]))))))))))), (UIf ((UBinop
      ((PrimUntyped.UBits2 (PrimUntyped.UCompare (false, CGt))), (UVar
      ('t'::('r'::('g'::('_'::('x'::[])))))), (UVar
      ('s'::('r'::('c'::('_'::('x'::[])))))))), (USugar (UCallModule
      ((Obj.magic id), (Obj.magic __), (Obj.magic r0_send), ((UUnop
      ((PrimUntyped.UConv PrimUntyped.UPack), (UBinop ((PrimUntyped.UStruct2
      (PrimUntyped.USubstField ('s'::('r'::('c'::[]))))), (UVar
      ('m'::('s'::('g'::[])))), (UVar
      ('r'::('_'::('a'::('d'::('d'::('r'::[]))))))))))) :: [])))), (UIf
      ((UBinop ((PrimUntyped.UBits2 (PrimUntyped.UCompare (false, CLt))),
      (UVar ('t'::('r'::('g'::('_'::('x'::[])))))), (UVar
      ('s'::('r'::('c'::('_'::('x'::[])))))))), (UFail (Bits_t 0)), (USugar
      (UConstBits (0, (Obj.magic __)))))))))))))))), (USugar (UConstBits (0,
      (Obj.magic __)))))))))))))))

  (** val _routecenter_r :
      int -> (var_t, fn_name_t, (pos_t, var_t, fn_name_t, Regs.reg_t, __)
      uaction) internalFunction -> (var_t, fn_name_t, (pos_t, var_t,
      fn_name_t, Regs.reg_t, __) uaction) internalFunction -> (var_t,
      fn_name_t, (pos_t, var_t, fn_name_t, Regs.reg_t, __) uaction)
      internalFunction -> (var_t, fn_name_t, (pos_t, var_t, fn_name_t,
      Regs.reg_t, __) uaction) internalFunction -> (pos_t, var_t, fn_name_t,
      Regs.reg_t, __) uaction **)

  let _routecenter_r r_addr2 r0_send r1_send r0_receive r1_receive =
    UBind (('r'::('_'::('a'::('d'::('d'::('r'::[])))))), (USugar (UConstBits
      ((Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      0)))),
      (Bits.of_nat (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ 0)))) r_addr2)))), (UBind (('m'::('0'::[])), (UBinop
      ((PrimUntyped.UBits2 PrimUntyped.UXor), (USugar (UCallModule
      ((Obj.magic id), (Obj.magic __), (Obj.magic r0_receive), []))),
      (UExternalCall (__, (USugar (UConstBits ((Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ 0)))))))))))))),
      (Bits.of_N (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0)))))))))))))) 0)))))))),
      (UBind (('m'::('1'::[])), (UBinop ((PrimUntyped.UBits2
      PrimUntyped.UXor), (USugar (UCallModule ((Obj.magic id),
      (Obj.magic __), (Obj.magic r1_receive), []))), (UExternalCall (__,
      (USugar (UConstBits ((Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0)))))))))))))),
      (Bits.of_N (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0)))))))))))))) 0)))))))),
      (UBind (('m'::('s'::('g'::[]))), (UUnop ((PrimUntyped.UConv
      (PrimUntyped.UUnpack (Struct_t Types.basic_flit))), (UVar
      ('m'::('0'::[]))))), (UBind
      (('n'::('e'::('w'::('_'::('d'::('a'::('t'::('a'::[])))))))), (UUnop
      ((PrimUntyped.UStruct1 (PrimUntyped.UGetField
      ('n'::('e'::('w'::[]))))), (UVar ('m'::('s'::('g'::[])))))), (UBind
      (('s'::('r'::('c'::('_'::('p'::[]))))), (UUnop ((PrimUntyped.UStruct1
      (PrimUntyped.UGetField ('s'::('r'::('c'::[]))))), (UVar
      ('m'::('s'::('g'::[])))))), (USeq ((UIf ((UBinop ((PrimUntyped.UBits2
      PrimUntyped.UAnd), (UBinop ((PrimUntyped.UEq true), (UVar
      ('s'::('r'::('c'::('_'::('p'::[])))))), (UVar
      ('r'::('_'::('a'::('d'::('d'::('r'::[]))))))))), (UVar
      ('n'::('e'::('w'::('_'::('d'::('a'::('t'::('a'::[]))))))))))), (USeq
      ((USugar (UCallModule ((Obj.magic id), (Obj.magic __),
      (Obj.magic r0_send), ((UUnop ((PrimUntyped.UConv PrimUntyped.UPack),
      (UBinop ((PrimUntyped.UStruct2 (PrimUntyped.USubstField
      ('n'::('e'::('w'::[]))))), (UVar ('m'::('s'::('g'::[])))), (USugar
      (UConstBits ((Stdlib.Int.succ 0),
      (vect_cons 0 false (Obj.magic __))))))))) :: [])))), (UBind
      (('t'::('r'::('g'::('_'::('x'::[]))))), (UUnop ((PrimUntyped.UStruct1
      (PrimUntyped.UGetField ('t'::('r'::('g'::('_'::('x'::[]))))))), (UVar
      ('m'::('s'::('g'::[])))))), (UBind
      (('t'::('r'::('g'::('_'::('y'::[]))))), (UUnop ((PrimUntyped.UStruct1
      (PrimUntyped.UGetField ('t'::('r'::('g'::('_'::('y'::[]))))))), (UVar
      ('m'::('s'::('g'::[])))))), (UBind
      (('s'::('r'::('c'::('_'::('x'::[]))))), (UUnop ((PrimUntyped.UStruct1
      (PrimUntyped.UGetField ('x'::[]))), (UUnop ((PrimUntyped.UConv
      (PrimUntyped.UUnpack (Struct_t Types.router_address))), (UVar
      ('r'::('_'::('a'::('d'::('d'::('r'::[]))))))))))), (UBind
      (('s'::('r'::('c'::('_'::('y'::[]))))), (UUnop ((PrimUntyped.UStruct1
      (PrimUntyped.UGetField ('y'::[]))), (UUnop ((PrimUntyped.UConv
      (PrimUntyped.UUnpack (Struct_t Types.router_address))), (UVar
      ('r'::('_'::('a'::('d'::('d'::('r'::[]))))))))))), (UIf ((UBinop
      ((PrimUntyped.UBits2 (PrimUntyped.UCompare (false, CGt))), (UVar
      ('t'::('r'::('g'::('_'::('x'::[])))))), (UVar
      ('s'::('r'::('c'::('_'::('x'::[])))))))), (USugar (UCallModule
      ((Obj.magic id), (Obj.magic __), (Obj.magic r1_send), ((UUnop
      ((PrimUntyped.UConv PrimUntyped.UPack), (UBinop ((PrimUntyped.UStruct2
      (PrimUntyped.USubstField ('s'::('r'::('c'::[]))))), (UVar
      ('m'::('s'::('g'::[])))), (UVar
      ('r'::('_'::('a'::('d'::('d'::('r'::[]))))))))))) :: [])))), (UIf
      ((UBinop ((PrimUntyped.UBits2 (PrimUntyped.UCompare (false, CLt))),
      (UVar ('t'::('r'::('g'::('_'::('x'::[])))))), (UVar
      ('s'::('r'::('c'::('_'::('x'::[])))))))), (USugar (UCallModule
      ((Obj.magic id), (Obj.magic __), (Obj.magic r0_send), ((UUnop
      ((PrimUntyped.UConv PrimUntyped.UPack), (UBinop ((PrimUntyped.UStruct2
      (PrimUntyped.USubstField ('s'::('r'::('c'::[]))))), (UVar
      ('m'::('s'::('g'::[])))), (UVar
      ('r'::('_'::('a'::('d'::('d'::('r'::[]))))))))))) :: [])))), (USugar
      (UConstBits (0, (Obj.magic __)))))))))))))))))), (USugar (UConstBits
      (0, (Obj.magic __)))))), (UBind (('m'::('s'::('g'::('1'::[])))), (UUnop
      ((PrimUntyped.UConv (PrimUntyped.UUnpack (Struct_t Types.basic_flit))),
      (UVar ('m'::('1'::[]))))), (UBind
      (('n'::('e'::('w'::('_'::('d'::('a'::('t'::('a'::[])))))))), (UUnop
      ((PrimUntyped.UStruct1 (PrimUntyped.UGetField
      ('n'::('e'::('w'::[]))))), (UVar ('m'::('s'::('g'::('1'::[]))))))),
      (UBind (('s'::('r'::('c'::('_'::('p'::[]))))), (UUnop
      ((PrimUntyped.UStruct1 (PrimUntyped.UGetField
      ('s'::('r'::('c'::[]))))), (UVar ('m'::('s'::('g'::('1'::[]))))))),
      (UIf ((UBinop ((PrimUntyped.UBits2 PrimUntyped.UAnd), (UBinop
      ((PrimUntyped.UEq true), (UVar ('s'::('r'::('c'::('_'::('p'::[])))))),
      (UVar ('r'::('_'::('a'::('d'::('d'::('r'::[]))))))))), (UVar
      ('n'::('e'::('w'::('_'::('d'::('a'::('t'::('a'::[]))))))))))), (USeq
      ((USugar (UCallModule ((Obj.magic id), (Obj.magic __),
      (Obj.magic r1_send), ((UUnop ((PrimUntyped.UConv PrimUntyped.UPack),
      (UBinop ((PrimUntyped.UStruct2 (PrimUntyped.USubstField
      ('n'::('e'::('w'::[]))))), (UVar ('m'::('s'::('g'::('1'::[]))))),
      (USugar (UConstBits ((Stdlib.Int.succ 0),
      (vect_cons 0 false (Obj.magic __))))))))) :: [])))), (UBind
      (('t'::('r'::('g'::('_'::('x'::[]))))), (UUnop ((PrimUntyped.UStruct1
      (PrimUntyped.UGetField ('t'::('r'::('g'::('_'::('x'::[]))))))), (UVar
      ('m'::('s'::('g'::('1'::[]))))))), (UBind
      (('t'::('r'::('g'::('_'::('y'::[]))))), (UUnop ((PrimUntyped.UStruct1
      (PrimUntyped.UGetField ('t'::('r'::('g'::('_'::('y'::[]))))))), (UVar
      ('m'::('s'::('g'::('1'::[]))))))), (UBind
      (('s'::('r'::('c'::('_'::('x'::[]))))), (UUnop ((PrimUntyped.UStruct1
      (PrimUntyped.UGetField ('x'::[]))), (UUnop ((PrimUntyped.UConv
      (PrimUntyped.UUnpack (Struct_t Types.router_address))), (UVar
      ('r'::('_'::('a'::('d'::('d'::('r'::[]))))))))))), (UBind
      (('s'::('r'::('c'::('_'::('y'::[]))))), (UUnop ((PrimUntyped.UStruct1
      (PrimUntyped.UGetField ('y'::[]))), (UUnop ((PrimUntyped.UConv
      (PrimUntyped.UUnpack (Struct_t Types.router_address))), (UVar
      ('r'::('_'::('a'::('d'::('d'::('r'::[]))))))))))), (UIf ((UBinop
      ((PrimUntyped.UBits2 (PrimUntyped.UCompare (false, CGt))), (UVar
      ('t'::('r'::('g'::('_'::('x'::[])))))), (UVar
      ('s'::('r'::('c'::('_'::('x'::[])))))))), (USugar (UCallModule
      ((Obj.magic id), (Obj.magic __), (Obj.magic r1_send), ((UUnop
      ((PrimUntyped.UConv PrimUntyped.UPack), (UBinop ((PrimUntyped.UStruct2
      (PrimUntyped.USubstField ('s'::('r'::('c'::[]))))), (UVar
      ('m'::('s'::('g'::('1'::[]))))), (UVar
      ('r'::('_'::('a'::('d'::('d'::('r'::[]))))))))))) :: [])))), (UIf
      ((UBinop ((PrimUntyped.UBits2 (PrimUntyped.UCompare (false, CLt))),
      (UVar ('t'::('r'::('g'::('_'::('x'::[])))))), (UVar
      ('s'::('r'::('c'::('_'::('x'::[])))))))), (USugar (UCallModule
      ((Obj.magic id), (Obj.magic __), (Obj.magic r0_send), ((UUnop
      ((PrimUntyped.UConv PrimUntyped.UPack), (UBinop ((PrimUntyped.UStruct2
      (PrimUntyped.USubstField ('s'::('r'::('c'::[]))))), (UVar
      ('m'::('s'::('g'::('1'::[]))))), (UVar
      ('r'::('_'::('a'::('d'::('d'::('r'::[]))))))))))) :: [])))), (USugar
      (UConstBits (0, (Obj.magic __)))))))))))))))))), (USugar (UConstBits
      (0, (Obj.magic __)))))))))))))))))))))))))

  (** val _routeend_r :
      int -> (var_t, fn_name_t, (pos_t, var_t, fn_name_t, Regs.reg_t, __)
      uaction) internalFunction -> (var_t, fn_name_t, (pos_t, var_t,
      fn_name_t, Regs.reg_t, __) uaction) internalFunction -> (pos_t, var_t,
      fn_name_t, Regs.reg_t, __) uaction **)

  let _routeend_r r_addr2 r0_send r0_receive =
    UBind (('r'::('_'::('a'::('d'::('d'::('r'::[])))))), (USugar (UConstBits
      ((Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      0)))),
      (Bits.of_nat (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ 0)))) r_addr2)))), (UBind (('m'::('0'::[])), (UBinop
      ((PrimUntyped.UBits2 PrimUntyped.UXor), (USugar (UCallModule
      ((Obj.magic id), (Obj.magic __), (Obj.magic r0_receive), []))),
      (UExternalCall (__, (USugar (UConstBits ((Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ 0)))))))))))))),
      (Bits.of_N (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0)))))))))))))) 0)))))))),
      (UBind (('m'::('s'::('g'::[]))), (UUnop ((PrimUntyped.UConv
      (PrimUntyped.UUnpack (Struct_t Types.basic_flit))), (UVar
      ('m'::('0'::[]))))), (UBind
      (('n'::('e'::('w'::('_'::('d'::('a'::('t'::('a'::[])))))))), (UUnop
      ((PrimUntyped.UStruct1 (PrimUntyped.UGetField
      ('n'::('e'::('w'::[]))))), (UVar ('m'::('s'::('g'::[])))))), (UBind
      (('s'::('r'::('c'::('_'::('p'::[]))))), (UUnop ((PrimUntyped.UStruct1
      (PrimUntyped.UGetField ('s'::('r'::('c'::[]))))), (UVar
      ('m'::('s'::('g'::[])))))), (UIf ((UBinop ((PrimUntyped.UBits2
      PrimUntyped.UAnd), (UBinop ((PrimUntyped.UEq true), (UVar
      ('s'::('r'::('c'::('_'::('p'::[])))))), (UVar
      ('r'::('_'::('a'::('d'::('d'::('r'::[]))))))))), (UVar
      ('n'::('e'::('w'::('_'::('d'::('a'::('t'::('a'::[]))))))))))), (UBind
      (('t'::('r'::('g'::('_'::('x'::[]))))), (UUnop ((PrimUntyped.UStruct1
      (PrimUntyped.UGetField ('t'::('r'::('g'::('_'::('x'::[]))))))), (UVar
      ('m'::('s'::('g'::[])))))), (UBind
      (('t'::('r'::('g'::('_'::('y'::[]))))), (UUnop ((PrimUntyped.UStruct1
      (PrimUntyped.UGetField ('t'::('r'::('g'::('_'::('y'::[]))))))), (UVar
      ('m'::('s'::('g'::[])))))), (UBind
      (('s'::('r'::('c'::('_'::('x'::[]))))), (UUnop ((PrimUntyped.UStruct1
      (PrimUntyped.UGetField ('x'::[]))), (UUnop ((PrimUntyped.UConv
      (PrimUntyped.UUnpack (Struct_t Types.router_address))), (UVar
      ('r'::('_'::('a'::('d'::('d'::('r'::[]))))))))))), (UBind
      (('s'::('r'::('c'::('_'::('y'::[]))))), (UUnop ((PrimUntyped.UStruct1
      (PrimUntyped.UGetField ('y'::[]))), (UUnop ((PrimUntyped.UConv
      (PrimUntyped.UUnpack (Struct_t Types.router_address))), (UVar
      ('r'::('_'::('a'::('d'::('d'::('r'::[]))))))))))), (UIf ((UBinop
      ((PrimUntyped.UBits2 (PrimUntyped.UCompare (false, CGt))), (UVar
      ('t'::('r'::('g'::('_'::('x'::[])))))), (UVar
      ('s'::('r'::('c'::('_'::('x'::[])))))))), (UFail (Bits_t 0)), (UIf
      ((UBinop ((PrimUntyped.UBits2 (PrimUntyped.UCompare (false, CLt))),
      (UVar ('t'::('r'::('g'::('_'::('x'::[])))))), (UVar
      ('s'::('r'::('c'::('_'::('x'::[])))))))), (USugar (UCallModule
      ((Obj.magic id), (Obj.magic __), (Obj.magic r0_send), ((UUnop
      ((PrimUntyped.UConv PrimUntyped.UPack), (UBinop ((PrimUntyped.UStruct2
      (PrimUntyped.USubstField ('s'::('r'::('c'::[]))))), (UVar
      ('m'::('s'::('g'::[])))), (UVar
      ('r'::('_'::('a'::('d'::('d'::('r'::[]))))))))))) :: [])))), (USugar
      (UConstBits (0, (Obj.magic __)))))))))))))))), (USugar (UConstBits (0,
      (Obj.magic __)))))))))))))))

  (** val routecenterfn :
      int -> Regs.reg_t -> Regs.reg_t -> (pos_t, var_t, fn_name_t,
      Regs.reg_t, __) uaction **)

  let routecenterfn n0 r1 r2 =
    _routecenter_r n0 (r_send r1) (r_send r2) (r_receive r1) (r_receive r2)

  (** val routestartfn :
      int -> Regs.reg_t -> (pos_t, var_t, fn_name_t, Regs.reg_t, __) uaction **)

  let routestartfn n0 r1 =
    _routestart_r n0 (r_send r1) (r_receive r1)

  (** val routeendfn :
      int -> Regs.reg_t -> (pos_t, var_t, fn_name_t, Regs.reg_t, __) uaction **)

  let routeendfn n0 r1 =
    _routeend_r n0 (r_send r1) (r_receive r1)
 end

module NOCImpl =
 struct
  module Coq__1 = struct
   type reg_t =
   | Coq_r1
   | Coq_r2
   | Coq_r3
  end
  include Coq__1

  type rule_name_t =
  | Coq_router_1
  | Coq_router_2
  | Coq_router_3
  | Coq_router_4

  module MyRegs =
   struct
    type reg_t = Coq__1.reg_t
   end

  module Routerfns = Router(MyRegs)

  (** val coq_R : reg_t -> type0 **)

  let coq_R _ =
    Bits_t (struct_sz Types.basic_flit)

  (** val r : reg_t -> type_denote **)

  let r _ =
    Bits.zero (struct_sz Types.basic_flit)

  (** val schedule : (pos_t, rule_name_t) scheduler **)

  let schedule =
    Cons (Coq_router_4, (Cons (Coq_router_3, (Cons (Coq_router_2, (Cons
      (Coq_router_1, Done)))))))

  (** val rules :
      rule_name_t -> (pos_t, var_t, fn_name_t, reg_t, __) action **)

  let rules = function
  | Coq_router_1 ->
    extract_success
      (let desugared =
         desugar_action dummyPos_unit.dummy_pos (UBind
           (('r'::('_'::('a'::('d'::('d'::('r'::[])))))), (USugar (UConstBits
           ((Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
           (Stdlib.Int.succ 0)))),
           (Bits.of_nat (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
             (Stdlib.Int.succ 0)))) 0)))), (UBind (('m'::('0'::[])), (UBinop
           ((PrimUntyped.UBits2 PrimUntyped.UXor), (USugar (UCallModule (id,
           (Obj.magic __), (Obj.magic Routerfns.r_receive Coq_r1), []))),
           (UExternalCall (__, (USugar (UConstBits ((Stdlib.Int.succ
           (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
           (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
           (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
           (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
           (Stdlib.Int.succ 0)))))))))))))),
           (Bits.of_N (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
             (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
             (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
             (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
             (Stdlib.Int.succ (Stdlib.Int.succ 0)))))))))))))) 0)))))))),
           (UBind (('m'::('s'::('g'::[]))), (UUnop ((PrimUntyped.UConv
           (PrimUntyped.UUnpack (Struct_t Types.basic_flit))), (UVar
           ('m'::('0'::[]))))), (UBind
           (('n'::('e'::('w'::('_'::('d'::('a'::('t'::('a'::[])))))))),
           (UUnop ((PrimUntyped.UStruct1 (PrimUntyped.UGetField
           ('n'::('e'::('w'::[]))))), (UVar ('m'::('s'::('g'::[])))))),
           (UBind (('s'::('r'::('c'::('_'::('p'::[]))))), (UUnop
           ((PrimUntyped.UStruct1 (PrimUntyped.UGetField
           ('s'::('r'::('c'::[]))))), (UVar ('m'::('s'::('g'::[])))))), (UIf
           ((UBinop ((PrimUntyped.UBits2 PrimUntyped.UAnd), (UBinop
           ((PrimUntyped.UEq true), (UVar
           ('s'::('r'::('c'::('_'::('p'::[])))))), (UVar
           ('r'::('_'::('a'::('d'::('d'::('r'::[]))))))))), (UVar
           ('n'::('e'::('w'::('_'::('d'::('a'::('t'::('a'::[]))))))))))),
           (UBind (('t'::('r'::('g'::('_'::('x'::[]))))), (UUnop
           ((PrimUntyped.UStruct1 (PrimUntyped.UGetField
           ('t'::('r'::('g'::('_'::('x'::[]))))))), (UVar
           ('m'::('s'::('g'::[])))))), (UBind
           (('t'::('r'::('g'::('_'::('y'::[]))))), (UUnop
           ((PrimUntyped.UStruct1 (PrimUntyped.UGetField
           ('t'::('r'::('g'::('_'::('y'::[]))))))), (UVar
           ('m'::('s'::('g'::[])))))), (UBind
           (('s'::('r'::('c'::('_'::('x'::[]))))), (UUnop
           ((PrimUntyped.UStruct1 (PrimUntyped.UGetField ('x'::[]))), (UUnop
           ((PrimUntyped.UConv (PrimUntyped.UUnpack (Struct_t
           Types.router_address))), (UVar
           ('r'::('_'::('a'::('d'::('d'::('r'::[]))))))))))), (UBind
           (('s'::('r'::('c'::('_'::('y'::[]))))), (UUnop
           ((PrimUntyped.UStruct1 (PrimUntyped.UGetField ('y'::[]))), (UUnop
           ((PrimUntyped.UConv (PrimUntyped.UUnpack (Struct_t
           Types.router_address))), (UVar
           ('r'::('_'::('a'::('d'::('d'::('r'::[]))))))))))), (UIf ((UBinop
           ((PrimUntyped.UBits2 (PrimUntyped.UCompare (false, CGt))), (UVar
           ('t'::('r'::('g'::('_'::('x'::[])))))), (UVar
           ('s'::('r'::('c'::('_'::('x'::[])))))))), (USugar (UCallModule
           (id, (Obj.magic __), (Obj.magic Routerfns.r_send Coq_r1), ((UUnop
           ((PrimUntyped.UConv PrimUntyped.UPack), (UBinop
           ((PrimUntyped.UStruct2 (PrimUntyped.USubstField
           ('s'::('r'::('c'::[]))))), (UVar ('m'::('s'::('g'::[])))), (UVar
           ('r'::('_'::('a'::('d'::('d'::('r'::[]))))))))))) :: [])))), (UIf
           ((UBinop ((PrimUntyped.UBits2 (PrimUntyped.UCompare (false,
           CLt))), (UVar ('t'::('r'::('g'::('_'::('x'::[])))))), (UVar
           ('s'::('r'::('c'::('_'::('x'::[])))))))), (UFail (Bits_t 0)),
           (USugar (UConstBits (0, (Obj.magic __)))))))))))))))), (USugar
           (UConstBits (0, (Obj.magic __))))))))))))))))
       in
       tc_action eqDec_string coq_R Routerfns.coq_Sigma
         dummyPos_unit.dummy_pos [] (Bits_t 0) (Obj.magic desugared))
  | Coq_router_2 ->
    extract_success
      (let desugared =
         desugar_action dummyPos_unit.dummy_pos (UBind
           (('r'::('_'::('a'::('d'::('d'::('r'::[])))))), (USugar (UConstBits
           ((Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
           (Stdlib.Int.succ 0)))),
           (Bits.of_nat (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
             (Stdlib.Int.succ 0)))) (Stdlib.Int.succ 0))))), (UBind
           (('m'::('0'::[])), (UBinop ((PrimUntyped.UBits2 PrimUntyped.UXor),
           (USugar (UCallModule (id, (Obj.magic __),
           (Obj.magic Routerfns.r_receive Coq_r1), []))), (UExternalCall (__,
           (USugar (UConstBits ((Stdlib.Int.succ (Stdlib.Int.succ
           (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
           (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
           (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
           (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
           0)))))))))))))),
           (Bits.of_N (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
             (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
             (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
             (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
             (Stdlib.Int.succ (Stdlib.Int.succ 0)))))))))))))) 0)))))))),
           (UBind (('m'::('1'::[])), (UBinop ((PrimUntyped.UBits2
           PrimUntyped.UXor), (USugar (UCallModule (id, (Obj.magic __),
           (Obj.magic Routerfns.r_receive Coq_r2), []))), (UExternalCall (__,
           (USugar (UConstBits ((Stdlib.Int.succ (Stdlib.Int.succ
           (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
           (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
           (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
           (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
           0)))))))))))))),
           (Bits.of_N (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
             (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
             (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
             (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
             (Stdlib.Int.succ (Stdlib.Int.succ 0)))))))))))))) 0)))))))),
           (UBind (('m'::('s'::('g'::[]))), (UUnop ((PrimUntyped.UConv
           (PrimUntyped.UUnpack (Struct_t Types.basic_flit))), (UVar
           ('m'::('0'::[]))))), (UBind
           (('n'::('e'::('w'::('_'::('d'::('a'::('t'::('a'::[])))))))),
           (UUnop ((PrimUntyped.UStruct1 (PrimUntyped.UGetField
           ('n'::('e'::('w'::[]))))), (UVar ('m'::('s'::('g'::[])))))),
           (UBind (('s'::('r'::('c'::('_'::('p'::[]))))), (UUnop
           ((PrimUntyped.UStruct1 (PrimUntyped.UGetField
           ('s'::('r'::('c'::[]))))), (UVar ('m'::('s'::('g'::[])))))), (USeq
           ((UIf ((UBinop ((PrimUntyped.UBits2 PrimUntyped.UAnd), (UBinop
           ((PrimUntyped.UEq true), (UVar
           ('s'::('r'::('c'::('_'::('p'::[])))))), (UVar
           ('r'::('_'::('a'::('d'::('d'::('r'::[]))))))))), (UVar
           ('n'::('e'::('w'::('_'::('d'::('a'::('t'::('a'::[]))))))))))),
           (USeq ((USugar (UCallModule (id, (Obj.magic __),
           (Obj.magic Routerfns.r_send Coq_r1), ((UUnop ((PrimUntyped.UConv
           PrimUntyped.UPack), (UBinop ((PrimUntyped.UStruct2
           (PrimUntyped.USubstField ('n'::('e'::('w'::[]))))), (UVar
           ('m'::('s'::('g'::[])))), (USugar (UConstBits ((Stdlib.Int.succ
           0), (vect_cons 0 false (Obj.magic __))))))))) :: [])))), (UBind
           (('t'::('r'::('g'::('_'::('x'::[]))))), (UUnop
           ((PrimUntyped.UStruct1 (PrimUntyped.UGetField
           ('t'::('r'::('g'::('_'::('x'::[]))))))), (UVar
           ('m'::('s'::('g'::[])))))), (UBind
           (('t'::('r'::('g'::('_'::('y'::[]))))), (UUnop
           ((PrimUntyped.UStruct1 (PrimUntyped.UGetField
           ('t'::('r'::('g'::('_'::('y'::[]))))))), (UVar
           ('m'::('s'::('g'::[])))))), (UBind
           (('s'::('r'::('c'::('_'::('x'::[]))))), (UUnop
           ((PrimUntyped.UStruct1 (PrimUntyped.UGetField ('x'::[]))), (UUnop
           ((PrimUntyped.UConv (PrimUntyped.UUnpack (Struct_t
           Types.router_address))), (UVar
           ('r'::('_'::('a'::('d'::('d'::('r'::[]))))))))))), (UBind
           (('s'::('r'::('c'::('_'::('y'::[]))))), (UUnop
           ((PrimUntyped.UStruct1 (PrimUntyped.UGetField ('y'::[]))), (UUnop
           ((PrimUntyped.UConv (PrimUntyped.UUnpack (Struct_t
           Types.router_address))), (UVar
           ('r'::('_'::('a'::('d'::('d'::('r'::[]))))))))))), (UIf ((UBinop
           ((PrimUntyped.UBits2 (PrimUntyped.UCompare (false, CGt))), (UVar
           ('t'::('r'::('g'::('_'::('x'::[])))))), (UVar
           ('s'::('r'::('c'::('_'::('x'::[])))))))), (USugar (UCallModule
           (id, (Obj.magic __), (Obj.magic Routerfns.r_send Coq_r2), ((UUnop
           ((PrimUntyped.UConv PrimUntyped.UPack), (UBinop
           ((PrimUntyped.UStruct2 (PrimUntyped.USubstField
           ('s'::('r'::('c'::[]))))), (UVar ('m'::('s'::('g'::[])))), (UVar
           ('r'::('_'::('a'::('d'::('d'::('r'::[]))))))))))) :: [])))), (UIf
           ((UBinop ((PrimUntyped.UBits2 (PrimUntyped.UCompare (false,
           CLt))), (UVar ('t'::('r'::('g'::('_'::('x'::[])))))), (UVar
           ('s'::('r'::('c'::('_'::('x'::[])))))))), (USugar (UCallModule
           (id, (Obj.magic __), (Obj.magic Routerfns.r_send Coq_r1), ((UUnop
           ((PrimUntyped.UConv PrimUntyped.UPack), (UBinop
           ((PrimUntyped.UStruct2 (PrimUntyped.USubstField
           ('s'::('r'::('c'::[]))))), (UVar ('m'::('s'::('g'::[])))), (UVar
           ('r'::('_'::('a'::('d'::('d'::('r'::[]))))))))))) :: [])))),
           (USugar (UConstBits (0, (Obj.magic __)))))))))))))))))), (USugar
           (UConstBits (0, (Obj.magic __)))))), (UBind
           (('m'::('s'::('g'::('1'::[])))), (UUnop ((PrimUntyped.UConv
           (PrimUntyped.UUnpack (Struct_t Types.basic_flit))), (UVar
           ('m'::('1'::[]))))), (UBind
           (('n'::('e'::('w'::('_'::('d'::('a'::('t'::('a'::[])))))))),
           (UUnop ((PrimUntyped.UStruct1 (PrimUntyped.UGetField
           ('n'::('e'::('w'::[]))))), (UVar
           ('m'::('s'::('g'::('1'::[]))))))), (UBind
           (('s'::('r'::('c'::('_'::('p'::[]))))), (UUnop
           ((PrimUntyped.UStruct1 (PrimUntyped.UGetField
           ('s'::('r'::('c'::[]))))), (UVar
           ('m'::('s'::('g'::('1'::[]))))))), (UIf ((UBinop
           ((PrimUntyped.UBits2 PrimUntyped.UAnd), (UBinop ((PrimUntyped.UEq
           true), (UVar ('s'::('r'::('c'::('_'::('p'::[])))))), (UVar
           ('r'::('_'::('a'::('d'::('d'::('r'::[]))))))))), (UVar
           ('n'::('e'::('w'::('_'::('d'::('a'::('t'::('a'::[]))))))))))),
           (USeq ((USugar (UCallModule (id, (Obj.magic __),
           (Obj.magic Routerfns.r_send Coq_r2), ((UUnop ((PrimUntyped.UConv
           PrimUntyped.UPack), (UBinop ((PrimUntyped.UStruct2
           (PrimUntyped.USubstField ('n'::('e'::('w'::[]))))), (UVar
           ('m'::('s'::('g'::('1'::[]))))), (USugar (UConstBits
           ((Stdlib.Int.succ 0),
           (vect_cons 0 false (Obj.magic __))))))))) :: [])))), (UBind
           (('t'::('r'::('g'::('_'::('x'::[]))))), (UUnop
           ((PrimUntyped.UStruct1 (PrimUntyped.UGetField
           ('t'::('r'::('g'::('_'::('x'::[]))))))), (UVar
           ('m'::('s'::('g'::('1'::[]))))))), (UBind
           (('t'::('r'::('g'::('_'::('y'::[]))))), (UUnop
           ((PrimUntyped.UStruct1 (PrimUntyped.UGetField
           ('t'::('r'::('g'::('_'::('y'::[]))))))), (UVar
           ('m'::('s'::('g'::('1'::[]))))))), (UBind
           (('s'::('r'::('c'::('_'::('x'::[]))))), (UUnop
           ((PrimUntyped.UStruct1 (PrimUntyped.UGetField ('x'::[]))), (UUnop
           ((PrimUntyped.UConv (PrimUntyped.UUnpack (Struct_t
           Types.router_address))), (UVar
           ('r'::('_'::('a'::('d'::('d'::('r'::[]))))))))))), (UBind
           (('s'::('r'::('c'::('_'::('y'::[]))))), (UUnop
           ((PrimUntyped.UStruct1 (PrimUntyped.UGetField ('y'::[]))), (UUnop
           ((PrimUntyped.UConv (PrimUntyped.UUnpack (Struct_t
           Types.router_address))), (UVar
           ('r'::('_'::('a'::('d'::('d'::('r'::[]))))))))))), (UIf ((UBinop
           ((PrimUntyped.UBits2 (PrimUntyped.UCompare (false, CGt))), (UVar
           ('t'::('r'::('g'::('_'::('x'::[])))))), (UVar
           ('s'::('r'::('c'::('_'::('x'::[])))))))), (USugar (UCallModule
           (id, (Obj.magic __), (Obj.magic Routerfns.r_send Coq_r2), ((UUnop
           ((PrimUntyped.UConv PrimUntyped.UPack), (UBinop
           ((PrimUntyped.UStruct2 (PrimUntyped.USubstField
           ('s'::('r'::('c'::[]))))), (UVar ('m'::('s'::('g'::('1'::[]))))),
           (UVar ('r'::('_'::('a'::('d'::('d'::('r'::[]))))))))))) :: [])))),
           (UIf ((UBinop ((PrimUntyped.UBits2 (PrimUntyped.UCompare (false,
           CLt))), (UVar ('t'::('r'::('g'::('_'::('x'::[])))))), (UVar
           ('s'::('r'::('c'::('_'::('x'::[])))))))), (USugar (UCallModule
           (id, (Obj.magic __), (Obj.magic Routerfns.r_send Coq_r1), ((UUnop
           ((PrimUntyped.UConv PrimUntyped.UPack), (UBinop
           ((PrimUntyped.UStruct2 (PrimUntyped.USubstField
           ('s'::('r'::('c'::[]))))), (UVar ('m'::('s'::('g'::('1'::[]))))),
           (UVar ('r'::('_'::('a'::('d'::('d'::('r'::[]))))))))))) :: [])))),
           (USugar (UConstBits (0, (Obj.magic __)))))))))))))))))), (USugar
           (UConstBits (0, (Obj.magic __))))))))))))))))))))))))))
       in
       tc_action eqDec_string coq_R Routerfns.coq_Sigma
         dummyPos_unit.dummy_pos [] (Bits_t 0) (Obj.magic desugared))
  | Coq_router_3 ->
    extract_success
      (let desugared =
         desugar_action dummyPos_unit.dummy_pos (UBind
           (('r'::('_'::('a'::('d'::('d'::('r'::[])))))), (USugar (UConstBits
           ((Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
           (Stdlib.Int.succ 0)))),
           (Bits.of_nat (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
             (Stdlib.Int.succ 0)))) (Stdlib.Int.succ (Stdlib.Int.succ 0)))))),
           (UBind (('m'::('0'::[])), (UBinop ((PrimUntyped.UBits2
           PrimUntyped.UXor), (USugar (UCallModule (id, (Obj.magic __),
           (Obj.magic Routerfns.r_receive Coq_r2), []))), (UExternalCall (__,
           (USugar (UConstBits ((Stdlib.Int.succ (Stdlib.Int.succ
           (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
           (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
           (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
           (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
           0)))))))))))))),
           (Bits.of_N (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
             (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
             (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
             (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
             (Stdlib.Int.succ (Stdlib.Int.succ 0)))))))))))))) 0)))))))),
           (UBind (('m'::('1'::[])), (UBinop ((PrimUntyped.UBits2
           PrimUntyped.UXor), (USugar (UCallModule (id, (Obj.magic __),
           (Obj.magic Routerfns.r_receive Coq_r3), []))), (UExternalCall (__,
           (USugar (UConstBits ((Stdlib.Int.succ (Stdlib.Int.succ
           (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
           (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
           (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
           (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
           0)))))))))))))),
           (Bits.of_N (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
             (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
             (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
             (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
             (Stdlib.Int.succ (Stdlib.Int.succ 0)))))))))))))) 0)))))))),
           (UBind (('m'::('s'::('g'::[]))), (UUnop ((PrimUntyped.UConv
           (PrimUntyped.UUnpack (Struct_t Types.basic_flit))), (UVar
           ('m'::('0'::[]))))), (UBind
           (('n'::('e'::('w'::('_'::('d'::('a'::('t'::('a'::[])))))))),
           (UUnop ((PrimUntyped.UStruct1 (PrimUntyped.UGetField
           ('n'::('e'::('w'::[]))))), (UVar ('m'::('s'::('g'::[])))))),
           (UBind (('s'::('r'::('c'::('_'::('p'::[]))))), (UUnop
           ((PrimUntyped.UStruct1 (PrimUntyped.UGetField
           ('s'::('r'::('c'::[]))))), (UVar ('m'::('s'::('g'::[])))))), (USeq
           ((UIf ((UBinop ((PrimUntyped.UBits2 PrimUntyped.UAnd), (UBinop
           ((PrimUntyped.UEq true), (UVar
           ('s'::('r'::('c'::('_'::('p'::[])))))), (UVar
           ('r'::('_'::('a'::('d'::('d'::('r'::[]))))))))), (UVar
           ('n'::('e'::('w'::('_'::('d'::('a'::('t'::('a'::[]))))))))))),
           (USeq ((USugar (UCallModule (id, (Obj.magic __),
           (Obj.magic Routerfns.r_send Coq_r2), ((UUnop ((PrimUntyped.UConv
           PrimUntyped.UPack), (UBinop ((PrimUntyped.UStruct2
           (PrimUntyped.USubstField ('n'::('e'::('w'::[]))))), (UVar
           ('m'::('s'::('g'::[])))), (USugar (UConstBits ((Stdlib.Int.succ
           0), (vect_cons 0 false (Obj.magic __))))))))) :: [])))), (UBind
           (('t'::('r'::('g'::('_'::('x'::[]))))), (UUnop
           ((PrimUntyped.UStruct1 (PrimUntyped.UGetField
           ('t'::('r'::('g'::('_'::('x'::[]))))))), (UVar
           ('m'::('s'::('g'::[])))))), (UBind
           (('t'::('r'::('g'::('_'::('y'::[]))))), (UUnop
           ((PrimUntyped.UStruct1 (PrimUntyped.UGetField
           ('t'::('r'::('g'::('_'::('y'::[]))))))), (UVar
           ('m'::('s'::('g'::[])))))), (UBind
           (('s'::('r'::('c'::('_'::('x'::[]))))), (UUnop
           ((PrimUntyped.UStruct1 (PrimUntyped.UGetField ('x'::[]))), (UUnop
           ((PrimUntyped.UConv (PrimUntyped.UUnpack (Struct_t
           Types.router_address))), (UVar
           ('r'::('_'::('a'::('d'::('d'::('r'::[]))))))))))), (UBind
           (('s'::('r'::('c'::('_'::('y'::[]))))), (UUnop
           ((PrimUntyped.UStruct1 (PrimUntyped.UGetField ('y'::[]))), (UUnop
           ((PrimUntyped.UConv (PrimUntyped.UUnpack (Struct_t
           Types.router_address))), (UVar
           ('r'::('_'::('a'::('d'::('d'::('r'::[]))))))))))), (UIf ((UBinop
           ((PrimUntyped.UBits2 (PrimUntyped.UCompare (false, CGt))), (UVar
           ('t'::('r'::('g'::('_'::('x'::[])))))), (UVar
           ('s'::('r'::('c'::('_'::('x'::[])))))))), (USugar (UCallModule
           (id, (Obj.magic __), (Obj.magic Routerfns.r_send Coq_r3), ((UUnop
           ((PrimUntyped.UConv PrimUntyped.UPack), (UBinop
           ((PrimUntyped.UStruct2 (PrimUntyped.USubstField
           ('s'::('r'::('c'::[]))))), (UVar ('m'::('s'::('g'::[])))), (UVar
           ('r'::('_'::('a'::('d'::('d'::('r'::[]))))))))))) :: [])))), (UIf
           ((UBinop ((PrimUntyped.UBits2 (PrimUntyped.UCompare (false,
           CLt))), (UVar ('t'::('r'::('g'::('_'::('x'::[])))))), (UVar
           ('s'::('r'::('c'::('_'::('x'::[])))))))), (USugar (UCallModule
           (id, (Obj.magic __), (Obj.magic Routerfns.r_send Coq_r2), ((UUnop
           ((PrimUntyped.UConv PrimUntyped.UPack), (UBinop
           ((PrimUntyped.UStruct2 (PrimUntyped.USubstField
           ('s'::('r'::('c'::[]))))), (UVar ('m'::('s'::('g'::[])))), (UVar
           ('r'::('_'::('a'::('d'::('d'::('r'::[]))))))))))) :: [])))),
           (USugar (UConstBits (0, (Obj.magic __)))))))))))))))))), (USugar
           (UConstBits (0, (Obj.magic __)))))), (UBind
           (('m'::('s'::('g'::('1'::[])))), (UUnop ((PrimUntyped.UConv
           (PrimUntyped.UUnpack (Struct_t Types.basic_flit))), (UVar
           ('m'::('1'::[]))))), (UBind
           (('n'::('e'::('w'::('_'::('d'::('a'::('t'::('a'::[])))))))),
           (UUnop ((PrimUntyped.UStruct1 (PrimUntyped.UGetField
           ('n'::('e'::('w'::[]))))), (UVar
           ('m'::('s'::('g'::('1'::[]))))))), (UBind
           (('s'::('r'::('c'::('_'::('p'::[]))))), (UUnop
           ((PrimUntyped.UStruct1 (PrimUntyped.UGetField
           ('s'::('r'::('c'::[]))))), (UVar
           ('m'::('s'::('g'::('1'::[]))))))), (UIf ((UBinop
           ((PrimUntyped.UBits2 PrimUntyped.UAnd), (UBinop ((PrimUntyped.UEq
           true), (UVar ('s'::('r'::('c'::('_'::('p'::[])))))), (UVar
           ('r'::('_'::('a'::('d'::('d'::('r'::[]))))))))), (UVar
           ('n'::('e'::('w'::('_'::('d'::('a'::('t'::('a'::[]))))))))))),
           (USeq ((USugar (UCallModule (id, (Obj.magic __),
           (Obj.magic Routerfns.r_send Coq_r3), ((UUnop ((PrimUntyped.UConv
           PrimUntyped.UPack), (UBinop ((PrimUntyped.UStruct2
           (PrimUntyped.USubstField ('n'::('e'::('w'::[]))))), (UVar
           ('m'::('s'::('g'::('1'::[]))))), (USugar (UConstBits
           ((Stdlib.Int.succ 0),
           (vect_cons 0 false (Obj.magic __))))))))) :: [])))), (UBind
           (('t'::('r'::('g'::('_'::('x'::[]))))), (UUnop
           ((PrimUntyped.UStruct1 (PrimUntyped.UGetField
           ('t'::('r'::('g'::('_'::('x'::[]))))))), (UVar
           ('m'::('s'::('g'::('1'::[]))))))), (UBind
           (('t'::('r'::('g'::('_'::('y'::[]))))), (UUnop
           ((PrimUntyped.UStruct1 (PrimUntyped.UGetField
           ('t'::('r'::('g'::('_'::('y'::[]))))))), (UVar
           ('m'::('s'::('g'::('1'::[]))))))), (UBind
           (('s'::('r'::('c'::('_'::('x'::[]))))), (UUnop
           ((PrimUntyped.UStruct1 (PrimUntyped.UGetField ('x'::[]))), (UUnop
           ((PrimUntyped.UConv (PrimUntyped.UUnpack (Struct_t
           Types.router_address))), (UVar
           ('r'::('_'::('a'::('d'::('d'::('r'::[]))))))))))), (UBind
           (('s'::('r'::('c'::('_'::('y'::[]))))), (UUnop
           ((PrimUntyped.UStruct1 (PrimUntyped.UGetField ('y'::[]))), (UUnop
           ((PrimUntyped.UConv (PrimUntyped.UUnpack (Struct_t
           Types.router_address))), (UVar
           ('r'::('_'::('a'::('d'::('d'::('r'::[]))))))))))), (UIf ((UBinop
           ((PrimUntyped.UBits2 (PrimUntyped.UCompare (false, CGt))), (UVar
           ('t'::('r'::('g'::('_'::('x'::[])))))), (UVar
           ('s'::('r'::('c'::('_'::('x'::[])))))))), (USugar (UCallModule
           (id, (Obj.magic __), (Obj.magic Routerfns.r_send Coq_r3), ((UUnop
           ((PrimUntyped.UConv PrimUntyped.UPack), (UBinop
           ((PrimUntyped.UStruct2 (PrimUntyped.USubstField
           ('s'::('r'::('c'::[]))))), (UVar ('m'::('s'::('g'::('1'::[]))))),
           (UVar ('r'::('_'::('a'::('d'::('d'::('r'::[]))))))))))) :: [])))),
           (UIf ((UBinop ((PrimUntyped.UBits2 (PrimUntyped.UCompare (false,
           CLt))), (UVar ('t'::('r'::('g'::('_'::('x'::[])))))), (UVar
           ('s'::('r'::('c'::('_'::('x'::[])))))))), (USugar (UCallModule
           (id, (Obj.magic __), (Obj.magic Routerfns.r_send Coq_r2), ((UUnop
           ((PrimUntyped.UConv PrimUntyped.UPack), (UBinop
           ((PrimUntyped.UStruct2 (PrimUntyped.USubstField
           ('s'::('r'::('c'::[]))))), (UVar ('m'::('s'::('g'::('1'::[]))))),
           (UVar ('r'::('_'::('a'::('d'::('d'::('r'::[]))))))))))) :: [])))),
           (USugar (UConstBits (0, (Obj.magic __)))))))))))))))))), (USugar
           (UConstBits (0, (Obj.magic __))))))))))))))))))))))))))
       in
       tc_action eqDec_string coq_R Routerfns.coq_Sigma
         dummyPos_unit.dummy_pos [] (Bits_t 0) (Obj.magic desugared))
  | Coq_router_4 ->
    extract_success
      (let desugared =
         desugar_action dummyPos_unit.dummy_pos (UBind
           (('r'::('_'::('a'::('d'::('d'::('r'::[])))))), (USugar (UConstBits
           ((Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
           (Stdlib.Int.succ 0)))),
           (Bits.of_nat (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
             (Stdlib.Int.succ 0)))) (Stdlib.Int.succ (Stdlib.Int.succ
             (Stdlib.Int.succ 0))))))), (UBind (('m'::('0'::[])), (UBinop
           ((PrimUntyped.UBits2 PrimUntyped.UXor), (USugar (UCallModule (id,
           (Obj.magic __), (Obj.magic Routerfns.r_receive Coq_r3), []))),
           (UExternalCall (__, (USugar (UConstBits ((Stdlib.Int.succ
           (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
           (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
           (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
           (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
           (Stdlib.Int.succ 0)))))))))))))),
           (Bits.of_N (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
             (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
             (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
             (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
             (Stdlib.Int.succ (Stdlib.Int.succ 0)))))))))))))) 0)))))))),
           (UBind (('m'::('s'::('g'::[]))), (UUnop ((PrimUntyped.UConv
           (PrimUntyped.UUnpack (Struct_t Types.basic_flit))), (UVar
           ('m'::('0'::[]))))), (UBind
           (('n'::('e'::('w'::('_'::('d'::('a'::('t'::('a'::[])))))))),
           (UUnop ((PrimUntyped.UStruct1 (PrimUntyped.UGetField
           ('n'::('e'::('w'::[]))))), (UVar ('m'::('s'::('g'::[])))))),
           (UBind (('s'::('r'::('c'::('_'::('p'::[]))))), (UUnop
           ((PrimUntyped.UStruct1 (PrimUntyped.UGetField
           ('s'::('r'::('c'::[]))))), (UVar ('m'::('s'::('g'::[])))))), (UIf
           ((UBinop ((PrimUntyped.UBits2 PrimUntyped.UAnd), (UBinop
           ((PrimUntyped.UEq true), (UVar
           ('s'::('r'::('c'::('_'::('p'::[])))))), (UVar
           ('r'::('_'::('a'::('d'::('d'::('r'::[]))))))))), (UVar
           ('n'::('e'::('w'::('_'::('d'::('a'::('t'::('a'::[]))))))))))),
           (UBind (('t'::('r'::('g'::('_'::('x'::[]))))), (UUnop
           ((PrimUntyped.UStruct1 (PrimUntyped.UGetField
           ('t'::('r'::('g'::('_'::('x'::[]))))))), (UVar
           ('m'::('s'::('g'::[])))))), (UBind
           (('t'::('r'::('g'::('_'::('y'::[]))))), (UUnop
           ((PrimUntyped.UStruct1 (PrimUntyped.UGetField
           ('t'::('r'::('g'::('_'::('y'::[]))))))), (UVar
           ('m'::('s'::('g'::[])))))), (UBind
           (('s'::('r'::('c'::('_'::('x'::[]))))), (UUnop
           ((PrimUntyped.UStruct1 (PrimUntyped.UGetField ('x'::[]))), (UUnop
           ((PrimUntyped.UConv (PrimUntyped.UUnpack (Struct_t
           Types.router_address))), (UVar
           ('r'::('_'::('a'::('d'::('d'::('r'::[]))))))))))), (UBind
           (('s'::('r'::('c'::('_'::('y'::[]))))), (UUnop
           ((PrimUntyped.UStruct1 (PrimUntyped.UGetField ('y'::[]))), (UUnop
           ((PrimUntyped.UConv (PrimUntyped.UUnpack (Struct_t
           Types.router_address))), (UVar
           ('r'::('_'::('a'::('d'::('d'::('r'::[]))))))))))), (UIf ((UBinop
           ((PrimUntyped.UBits2 (PrimUntyped.UCompare (false, CGt))), (UVar
           ('t'::('r'::('g'::('_'::('x'::[])))))), (UVar
           ('s'::('r'::('c'::('_'::('x'::[])))))))), (UFail (Bits_t 0)), (UIf
           ((UBinop ((PrimUntyped.UBits2 (PrimUntyped.UCompare (false,
           CLt))), (UVar ('t'::('r'::('g'::('_'::('x'::[])))))), (UVar
           ('s'::('r'::('c'::('_'::('x'::[])))))))), (USugar (UCallModule
           (id, (Obj.magic __), (Obj.magic Routerfns.r_send Coq_r3), ((UUnop
           ((PrimUntyped.UConv PrimUntyped.UPack), (UBinop
           ((PrimUntyped.UStruct2 (PrimUntyped.USubstField
           ('s'::('r'::('c'::[]))))), (UVar ('m'::('s'::('g'::[])))), (UVar
           ('r'::('_'::('a'::('d'::('d'::('r'::[]))))))))))) :: [])))),
           (USugar (UConstBits (0, (Obj.magic __)))))))))))))))), (USugar
           (UConstBits (0, (Obj.magic __))))))))))))))))
       in
       tc_action eqDec_string coq_R Routerfns.coq_Sigma
         dummyPos_unit.dummy_pos [] (Bits_t 0) (Obj.magic desugared))

  (** val cpp_extfuns : char list **)

  let cpp_extfuns =
    'c'::('l'::('a'::('s'::('s'::(' '::('e'::('x'::('t'::('f'::('u'::('n'::('s'::(' '::('{'::('\n'::('p'::('u'::('b'::('l'::('i'::('c'::(':'::('\n'::(' '::(' '::('s'::('t'::('a'::('t'::('i'::('c'::(' '::('b'::('i'::('t'::('s'::('<'::('3'::('2'::('>'::(' '::('t'::('i'::('l'::('e'::('_'::('i'::('n'::('t'::('f'::('('::('b'::('i'::('t'::('s'::('<'::('3'::('2'::('>'::(' '::('s'::('t'::(')'::(' '::('{'::('\n'::(' '::(' '::(' '::(' '::('r'::('e'::('t'::('u'::('r'::('n'::(' '::('s'::('t'::(';'::('\n'::(' '::(' '::('}'::('\n'::('}'::(';'::[])))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

  (** val ext_fn_names : __ -> char list **)

  let ext_fn_names _ =
    't'::('i'::('l'::('e'::('_'::('i'::('n'::('t'::('f'::[]))))))))

  (** val package : interop_package_t **)

  let package =
    { ip_koika = { koika_var_names = show_string; koika_fn_names =
      show_string; koika_reg_names = { show0 = (fun h ->
      match Obj.magic h with
      | Coq_r1 -> 'r'::('1'::[])
      | Coq_r2 -> 'r'::('2'::[])
      | Coq_r3 -> 'r'::('3'::[])) }; koika_reg_types = (Obj.magic coq_R);
      koika_reg_init = (Obj.magic r); koika_reg_finite = { finite_index =
      (fun h ->
      match Obj.magic h with
      | Coq_r1 -> 0
      | Coq_r2 -> Stdlib.Int.succ 0
      | Coq_r3 -> Stdlib.Int.succ (Stdlib.Int.succ 0)); finite_elements =
      ((Obj.magic Coq_r1) :: ((Obj.magic Coq_r2) :: ((Obj.magic Coq_r3) :: []))) };
      koika_ext_fn_types = (Obj.magic Routerfns.coq_Sigma); koika_rules =
      (Obj.magic rules); koika_rule_external = (fun _ -> false);
      koika_rule_names = { show0 = (fun h ->
      match Obj.magic h with
      | Coq_router_1 ->
        'r'::('o'::('u'::('t'::('e'::('r'::('_'::('1'::[])))))))
      | Coq_router_2 ->
        'r'::('o'::('u'::('t'::('e'::('r'::('_'::('2'::[])))))))
      | Coq_router_3 ->
        'r'::('o'::('u'::('t'::('e'::('r'::('_'::('3'::[])))))))
      | Coq_router_4 ->
        'r'::('o'::('u'::('t'::('e'::('r'::('_'::('4'::[])))))))) };
      koika_scheduler = (Obj.magic schedule); koika_module_name =
      ('N'::('o'::('C'::[]))) }; ip_verilog = { vp_ext_fn_specs =
      (Obj.magic (fun _ -> { efr_name = (ext_fn_names __); efr_internal =
        false })) }; ip_sim = { sp_ext_fn_specs =
      (Obj.magic (fun _ -> { efs_name = (ext_fn_names __); efs_method =
        false })); sp_prelude = (Some cpp_extfuns) } }

  (** val prog : unit **)

  let prog =
    Backends.register package
 end
