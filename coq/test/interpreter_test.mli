
val negb : bool -> bool

val fst : ('a1 * 'a2) -> 'a1

val snd : ('a1 * 'a2) -> 'a2

val length : 'a1 list -> int

val app : 'a1 list -> 'a1 list -> 'a1 list

type comparison =
| Eq
| Lt
| Gt

val add : int -> int -> int

module Nat :
 sig
 end

module Pos :
 sig
  type mask =
  | IsNul
  | IsPos of int
  | IsNeg
 end

module Coq_Pos :
 sig
  val succ : int -> int

  val add : int -> int -> int

  val add_carry : int -> int -> int

  val pred_double : int -> int

  val pred_N : int -> int

  type mask = Pos.mask =
  | IsNul
  | IsPos of int
  | IsNeg

  val succ_double_mask : mask -> mask

  val double_mask : mask -> mask

  val double_pred_mask : int -> mask

  val sub_mask : int -> int -> mask

  val sub_mask_carry : int -> int -> mask

  val mul : int -> int -> int

  val iter : ('a1 -> 'a1) -> 'a1 -> int -> 'a1

  val div2 : int -> int

  val div2_up : int -> int

  val size : int -> int

  val compare_cont : comparison -> int -> int -> comparison

  val compare : int -> int -> comparison

  val eqb : int -> int -> bool

  val coq_Nsucc_double : int -> int

  val coq_Ndouble : int -> int

  val coq_lor : int -> int -> int

  val coq_land : int -> int -> int

  val ldiff : int -> int -> int

  val coq_lxor : int -> int -> int

  val testbit : int -> int -> bool

  val iter_op : ('a1 -> 'a1 -> 'a1) -> int -> 'a1 -> 'a1

  val to_nat : int -> int

  val of_succ_nat : int -> int

  val eq_dec : int -> int -> bool
 end

module N :
 sig
  val succ_double : int -> int

  val double : int -> int

  val succ_pos : int -> int

  val sub : int -> int -> int

  val compare : int -> int -> comparison

  val leb : int -> int -> bool

  val pos_div_eucl : int -> int -> int * int

  val coq_lor : int -> int -> int

  val coq_land : int -> int -> int

  val ldiff : int -> int -> int

  val coq_lxor : int -> int -> int

  val testbit : int -> int -> bool
 end

val nth : int -> 'a1 list -> 'a1 -> 'a1

val nth_error : 'a1 list -> int -> 'a1 option

val removelast : 'a1 list -> 'a1 list

val rev : 'a1 list -> 'a1 list

val map : ('a1 -> 'a2) -> 'a1 list -> 'a2 list

val firstn : int -> 'a1 list -> 'a1 list

val skipn : int -> 'a1 list -> 'a1 list

val repeat : 'a1 -> int -> 'a1 list

module Z :
 sig
  val double : int64 -> int64

  val succ_double : int64 -> int64

  val pred_double : int64 -> int64

  val pos_sub : int -> int -> int64

  val add : int64 -> int64 -> int64

  val opp : int64 -> int64

  val pred : int64 -> int64

  val sub : int64 -> int64 -> int64

  val mul : int64 -> int64 -> int64

  val pow_pos : int64 -> int -> int64

  val pow : int64 -> int64 -> int64

  val compare : int64 -> int64 -> comparison

  val leb : int64 -> int64 -> bool

  val ltb : int64 -> int64 -> bool

  val eqb : int64 -> int64 -> bool

  val to_nat : int64 -> int

  val of_nat : int -> int64

  val of_N : int -> int64

  val iter : int64 -> ('a1 -> 'a1) -> 'a1 -> 'a1

  val pos_div_eucl : int -> int64 -> int64 * int64

  val div_eucl : int64 -> int64 -> int64 * int64

  val div : int64 -> int64 -> int64

  val modulo : int64 -> int64 -> int64

  val quotrem : int64 -> int64 -> int64 * int64

  val quot : int64 -> int64 -> int64

  val rem : int64 -> int64 -> int64

  val odd : int64 -> bool

  val div2 : int64 -> int64

  val log2 : int64 -> int64

  val testbit : int64 -> int64 -> bool

  val shiftl : int64 -> int64 -> int64

  val shiftr : int64 -> int64 -> int64

  val coq_lor : int64 -> int64 -> int64

  val coq_land : int64 -> int64 -> int64

  val coq_lxor : int64 -> int64 -> int64

  val eq_dec : int64 -> int64 -> bool
 end

val z_lt_dec : int64 -> int64 -> bool

val z_le_dec : int64 -> int64 -> bool

val z_le_gt_dec : int64 -> int64 -> bool

val zeq_bool : int64 -> int64 -> bool

val zdivide_dec : int64 -> int64 -> bool

val shift_nat : int -> int -> int

val shift_pos : int -> int -> int

val two_power_nat : int -> int64

val two_power_pos : int -> int64

val two_p : int64 -> int64

val peq : int -> int -> bool

val zeq : int64 -> int64 -> bool

val zlt : int64 -> int64 -> bool

val zle : int64 -> int64 -> bool

val proj_sumbool : bool -> bool

val p_mod_two_p : int -> int -> int64

val zshiftin : bool -> int64 -> int64

val zzero_ext : int64 -> int64 -> int64

val zsign_ext : int64 -> int64 -> int64

val z_one_bits : int -> int64 -> int64 -> int64 list

val p_is_power2 : int -> bool

val z_is_power2 : int64 -> int64 option

val zsize : int64 -> int64

val emin : int64 -> int64 -> int64

type full_float =
| F754_zero of bool
| F754_infinity of bool
| F754_nan of bool * int
| F754_finite of bool * int * int64

type binary_float =
| B754_zero of bool
| B754_infinity of bool
| B754_nan of bool * int
| B754_finite of bool * int * int64

val fF2B : int64 -> int64 -> full_float -> binary_float

val join_bits : int64 -> int64 -> bool -> int64 -> int64 -> int64

val split_bits : int64 -> int64 -> int64 -> (bool * int64) * int64

val bits_of_binary_float : int64 -> int64 -> binary_float -> int64

val binary_float_of_bits_aux : int64 -> int64 -> int64 -> full_float

val binary_float_of_bits : int64 -> int64 -> int64 -> binary_float

type binary32 = binary_float

val b32_of_bits : int64 -> binary32

val bits_of_b32 : binary32 -> int64

type binary64 = binary_float

val b64_of_bits : int64 -> binary64

val bits_of_b64 : binary64 -> int64

val ptr64 : bool

val big_endian : bool

type comparison0 =
| Ceq
| Cne
| Clt
| Cle
| Cgt
| Cge

module type WORDSIZE =
 sig
  val wordsize : int
 end

module Make :
 functor (WS:WORDSIZE) ->
 sig
  val wordsize : int

  val zwordsize : int64

  val modulus : int64

  val half_modulus : int64

  val max_unsigned : int64

  val max_signed : int64

  val min_signed : int64

  type int = int64
    (* singleton inductive, whose constructor was mkint *)

  val intval : int -> int64

  val coq_Z_mod_modulus : int64 -> int64

  val unsigned : int -> int64

  val signed : int -> int64

  val repr : int64 -> int

  val zero : int

  val one : int

  val mone : int

  val iwordsize : int

  val eq_dec : int -> int -> bool

  val eq : int -> int -> bool

  val lt : int -> int -> bool

  val ltu : int -> int -> bool

  val neg : int -> int

  val add : int -> int -> int

  val sub : int -> int -> int

  val mul : int -> int -> int

  val divs : int -> int -> int

  val mods : int -> int -> int

  val divu : int -> int -> int

  val modu : int -> int -> int

  val coq_and : int -> int -> int

  val coq_or : int -> int -> int

  val xor : int -> int -> int

  val not : int -> int

  val shl : int -> int -> int

  val shru : int -> int -> int

  val shr : int -> int -> int

  val rol : int -> int -> int

  val ror : int -> int -> int

  val rolm : int -> int -> int -> int

  val shrx : int -> int -> int

  val mulhu : int -> int -> int

  val mulhs : int -> int -> int

  val negative : int -> int

  val add_carry : int -> int -> int -> int

  val add_overflow : int -> int -> int -> int

  val sub_borrow : int -> int -> int -> int

  val sub_overflow : int -> int -> int -> int

  val shr_carry : int -> int -> int

  val zero_ext : int64 -> int -> int

  val sign_ext : int64 -> int -> int

  val one_bits : int -> int list

  val is_power2 : int -> int option

  val cmp : comparison0 -> int -> int -> bool

  val cmpu : comparison0 -> int -> int -> bool

  val notbool : int -> int

  val divmodu2 : int -> int -> int -> (int * int) option

  val divmods2 : int -> int -> int -> (int * int) option

  val testbit : int -> int64 -> bool

  val int_of_one_bits : int list -> int

  val no_overlap : int -> int64 -> int -> int64 -> bool

  val size : int -> int64

  val unsigned_bitfield_extract : int64 -> int64 -> int -> int

  val signed_bitfield_extract : int64 -> int64 -> int -> int

  val bitfield_insert : int64 -> int64 -> int -> int -> int
 end

module Wordsize_32 :
 sig
  val wordsize : int
 end

module Int :
 sig
  val wordsize : int

  val zwordsize : int64

  val modulus : int64

  val half_modulus : int64

  val max_unsigned : int64

  val max_signed : int64

  val min_signed : int64

  type int = int64
    (* singleton inductive, whose constructor was mkint *)

  val intval : int -> int64

  val coq_Z_mod_modulus : int64 -> int64

  val unsigned : int -> int64

  val signed : int -> int64

  val repr : int64 -> int

  val zero : int

  val one : int

  val mone : int

  val iwordsize : int

  val eq_dec : int -> int -> bool

  val eq : int -> int -> bool

  val lt : int -> int -> bool

  val ltu : int -> int -> bool

  val neg : int -> int

  val add : int -> int -> int

  val sub : int -> int -> int

  val mul : int -> int -> int

  val divs : int -> int -> int

  val mods : int -> int -> int

  val divu : int -> int -> int

  val modu : int -> int -> int

  val coq_and : int -> int -> int

  val coq_or : int -> int -> int

  val xor : int -> int -> int

  val not : int -> int

  val shl : int -> int -> int

  val shru : int -> int -> int

  val shr : int -> int -> int

  val rol : int -> int -> int

  val ror : int -> int -> int

  val rolm : int -> int -> int -> int

  val shrx : int -> int -> int

  val mulhu : int -> int -> int

  val mulhs : int -> int -> int

  val negative : int -> int

  val add_carry : int -> int -> int -> int

  val add_overflow : int -> int -> int -> int

  val sub_borrow : int -> int -> int -> int

  val sub_overflow : int -> int -> int -> int

  val shr_carry : int -> int -> int

  val zero_ext : int64 -> int -> int

  val sign_ext : int64 -> int -> int

  val one_bits : int -> int list

  val is_power2 : int -> int option

  val cmp : comparison0 -> int -> int -> bool

  val cmpu : comparison0 -> int -> int -> bool

  val notbool : int -> int

  val divmodu2 : int -> int -> int -> (int * int) option

  val divmods2 : int -> int -> int -> (int * int) option

  val testbit : int -> int64 -> bool

  val int_of_one_bits : int list -> int

  val no_overlap : int -> int64 -> int -> int64 -> bool

  val size : int -> int64

  val unsigned_bitfield_extract : int64 -> int64 -> int -> int

  val signed_bitfield_extract : int64 -> int64 -> int -> int

  val bitfield_insert : int64 -> int64 -> int -> int -> int
 end

module Wordsize_8 :
 sig
  val wordsize : int
 end

module Byte :
 sig
  val wordsize : int

  val zwordsize : int64

  val modulus : int64

  val half_modulus : int64

  val max_unsigned : int64

  val max_signed : int64

  val min_signed : int64

  type int = int64
    (* singleton inductive, whose constructor was mkint *)

  val intval : int -> int64

  val coq_Z_mod_modulus : int64 -> int64

  val unsigned : int -> int64

  val signed : int -> int64

  val repr : int64 -> int

  val zero : int

  val one : int

  val mone : int

  val iwordsize : int

  val eq_dec : int -> int -> bool

  val eq : int -> int -> bool

  val lt : int -> int -> bool

  val ltu : int -> int -> bool

  val neg : int -> int

  val add : int -> int -> int

  val sub : int -> int -> int

  val mul : int -> int -> int

  val divs : int -> int -> int

  val mods : int -> int -> int

  val divu : int -> int -> int

  val modu : int -> int -> int

  val coq_and : int -> int -> int

  val coq_or : int -> int -> int

  val xor : int -> int -> int

  val not : int -> int

  val shl : int -> int -> int

  val shru : int -> int -> int

  val shr : int -> int -> int

  val rol : int -> int -> int

  val ror : int -> int -> int

  val rolm : int -> int -> int -> int

  val shrx : int -> int -> int

  val mulhu : int -> int -> int

  val mulhs : int -> int -> int

  val negative : int -> int

  val add_carry : int -> int -> int -> int

  val add_overflow : int -> int -> int -> int

  val sub_borrow : int -> int -> int -> int

  val sub_overflow : int -> int -> int -> int

  val shr_carry : int -> int -> int

  val zero_ext : int64 -> int -> int

  val sign_ext : int64 -> int -> int

  val one_bits : int -> int list

  val is_power2 : int -> int option

  val cmp : comparison0 -> int -> int -> bool

  val cmpu : comparison0 -> int -> int -> bool

  val notbool : int -> int

  val divmodu2 : int -> int -> int -> (int * int) option

  val divmods2 : int -> int -> int -> (int * int) option

  val testbit : int -> int64 -> bool

  val int_of_one_bits : int list -> int

  val no_overlap : int -> int64 -> int -> int64 -> bool

  val size : int -> int64

  val unsigned_bitfield_extract : int64 -> int64 -> int -> int

  val signed_bitfield_extract : int64 -> int64 -> int -> int

  val bitfield_insert : int64 -> int64 -> int -> int -> int
 end

module Wordsize_64 :
 sig
  val wordsize : int
 end

module Int64 :
 sig
  val wordsize : int

  val modulus : int64

  val half_modulus : int64

  type int = int64
    (* singleton inductive, whose constructor was mkint *)

  val intval : int -> int64

  val coq_Z_mod_modulus : int64 -> int64

  val unsigned : int -> int64

  val signed : int -> int64

  val repr : int64 -> int

  val zero : int

  val one : int

  val eq_dec : int -> int -> bool

  val eq : int -> int -> bool

  val lt : int -> int -> bool

  val ltu : int -> int -> bool

  val neg : int -> int

  val add : int -> int -> int

  val sub : int -> int -> int

  val mul : int -> int -> int

  val mods : int -> int -> int

  val divu : int -> int -> int

  val modu : int -> int -> int

  val coq_and : int -> int -> int

  val coq_or : int -> int -> int

  val xor : int -> int -> int

  val shl : int -> int -> int

  val shru : int -> int -> int

  val zero_ext : int64 -> int -> int

  val cmp : comparison0 -> int -> int -> bool

  val cmpu : comparison0 -> int -> int -> bool

  val unsigned_bitfield_extract : int64 -> int64 -> int -> int
 end

module Wordsize_Ptrofs :
 sig
  val wordsize : int
 end

module Ptrofs :
 sig
  val wordsize : int

  val modulus : int64

  type int = int64
    (* singleton inductive, whose constructor was mkint *)

  val intval : int -> int64

  val coq_Z_mod_modulus : int64 -> int64

  val unsigned : int -> int64

  val repr : int64 -> int

  val eq_dec : int -> int -> bool

  val of_int64 : Int64.int -> int

  val of_int64u : Int64.int -> int
 end

module Wordsize_16 :
 sig
  val wordsize : int
 end

module Int16 :
 sig
  val wordsize : int

  val zwordsize : int64

  val modulus : int64

  val half_modulus : int64

  val max_unsigned : int64

  val max_signed : int64

  val min_signed : int64

  type int = int64
    (* singleton inductive, whose constructor was mkint *)

  val intval : int -> int64

  val coq_Z_mod_modulus : int64 -> int64

  val unsigned : int -> int64

  val signed : int -> int64

  val repr : int64 -> int

  val zero : int

  val one : int

  val mone : int

  val iwordsize : int

  val eq_dec : int -> int -> bool

  val eq : int -> int -> bool

  val lt : int -> int -> bool

  val ltu : int -> int -> bool

  val neg : int -> int

  val add : int -> int -> int

  val sub : int -> int -> int

  val mul : int -> int -> int

  val divs : int -> int -> int

  val mods : int -> int -> int

  val divu : int -> int -> int

  val modu : int -> int -> int

  val coq_and : int -> int -> int

  val coq_or : int -> int -> int

  val xor : int -> int -> int

  val not : int -> int

  val shl : int -> int -> int

  val shru : int -> int -> int

  val shr : int -> int -> int

  val rol : int -> int -> int

  val ror : int -> int -> int

  val rolm : int -> int -> int -> int

  val shrx : int -> int -> int

  val mulhu : int -> int -> int

  val mulhs : int -> int -> int

  val negative : int -> int

  val add_carry : int -> int -> int -> int

  val add_overflow : int -> int -> int -> int

  val sub_borrow : int -> int -> int -> int

  val sub_overflow : int -> int -> int -> int

  val shr_carry : int -> int -> int

  val zero_ext : int64 -> int -> int

  val sign_ext : int64 -> int -> int

  val one_bits : int -> int list

  val is_power2 : int -> int option

  val cmp : comparison0 -> int -> int -> bool

  val cmpu : comparison0 -> int -> int -> bool

  val notbool : int -> int

  val divmodu2 : int -> int -> int -> (int * int) option

  val divmods2 : int -> int -> int -> (int * int) option

  val testbit : int -> int64 -> bool

  val int_of_one_bits : int list -> int

  val no_overlap : int -> int64 -> int -> int64 -> bool

  val size : int -> int64

  val unsigned_bitfield_extract : int64 -> int64 -> int -> int

  val signed_bitfield_extract : int64 -> int64 -> int -> int

  val bitfield_insert : int64 -> int64 -> int -> int -> int
 end

module Wordsize_128 :
 sig
  val wordsize : int
 end

module Int128 :
 sig
  val wordsize : int

  val zwordsize : int64

  val modulus : int64

  val half_modulus : int64

  val max_unsigned : int64

  val max_signed : int64

  val min_signed : int64

  type int = int64
    (* singleton inductive, whose constructor was mkint *)

  val intval : int -> int64

  val coq_Z_mod_modulus : int64 -> int64

  val unsigned : int -> int64

  val signed : int -> int64

  val repr : int64 -> int

  val zero : int

  val one : int

  val mone : int

  val iwordsize : int

  val eq_dec : int -> int -> bool

  val eq : int -> int -> bool

  val lt : int -> int -> bool

  val ltu : int -> int -> bool

  val neg : int -> int

  val add : int -> int -> int

  val sub : int -> int -> int

  val mul : int -> int -> int

  val divs : int -> int -> int

  val mods : int -> int -> int

  val divu : int -> int -> int

  val modu : int -> int -> int

  val coq_and : int -> int -> int

  val coq_or : int -> int -> int

  val xor : int -> int -> int

  val not : int -> int

  val shl : int -> int -> int

  val shru : int -> int -> int

  val shr : int -> int -> int

  val rol : int -> int -> int

  val ror : int -> int -> int

  val rolm : int -> int -> int -> int

  val shrx : int -> int -> int

  val mulhu : int -> int -> int

  val mulhs : int -> int -> int

  val negative : int -> int

  val add_carry : int -> int -> int -> int

  val add_overflow : int -> int -> int -> int

  val sub_borrow : int -> int -> int -> int

  val sub_overflow : int -> int -> int -> int

  val shr_carry : int -> int -> int

  val zero_ext : int64 -> int -> int

  val sign_ext : int64 -> int -> int

  val one_bits : int -> int list

  val is_power2 : int -> int option

  val cmp : comparison0 -> int -> int -> bool

  val cmpu : comparison0 -> int -> int -> bool

  val notbool : int -> int

  val divmodu2 : int -> int -> int -> (int * int) option

  val divmods2 : int -> int -> int -> (int * int) option

  val testbit : int -> int64 -> bool

  val int_of_one_bits : int list -> int

  val no_overlap : int -> int64 -> int -> int64 -> bool

  val size : int -> int64

  val unsigned_bitfield_extract : int64 -> int64 -> int -> int

  val signed_bitfield_extract : int64 -> int64 -> int -> int

  val bitfield_insert : int64 -> int64 -> int -> int -> int
 end

type usize = Int64.int

val bit_left_shift_word : Int16.int -> int -> Int16.int

val bit_right_shift_word : Int16.int -> int -> Int16.int

val bit_left_shift_int : Int.int -> int -> Int.int

val bit_right_shift_int : Int.int -> int -> Int.int

val bit_left_shift_int64 : Int64.int -> int -> Int64.int

val bit_right_shift_int64 : Int64.int -> int -> Int64.int

val byte_list_of_word : Int16.int -> Byte.int list

val byte_list_of_int : Int.int -> Byte.int list

val byte_list_of_int64 : Int64.int -> Byte.int list

val int64_of_byte_list : Byte.int list -> Int64.int option

val int_of_byte_list : Byte.int list -> Int.int option

val word_of_byte_list : Byte.int list -> Int16.int option

module PTree :
 sig
  type 'a tree' =
  | Node001 of 'a tree'
  | Node010 of 'a
  | Node011 of 'a * 'a tree'
  | Node100 of 'a tree'
  | Node101 of 'a tree' * 'a tree'
  | Node110 of 'a tree' * 'a
  | Node111 of 'a tree' * 'a * 'a tree'

  type 'a tree =
  | Empty
  | Nodes of 'a tree'

  type 'a t = 'a tree

  val empty : 'a1 t

  val get' : int -> 'a1 tree' -> 'a1 option

  val get : int -> 'a1 tree -> 'a1 option

  val set0 : int -> 'a1 -> 'a1 tree'

  val set' : int -> 'a1 -> 'a1 tree' -> 'a1 tree'

  val set : int -> 'a1 -> 'a1 tree -> 'a1 tree

  val map1' : ('a1 -> 'a2) -> 'a1 tree' -> 'a2 tree'

  val map1 : ('a1 -> 'a2) -> 'a1 t -> 'a2 t
 end

module PMap :
 sig
  type 'a t = 'a * 'a PTree.t

  val init : 'a1 -> 'a1 * 'a1 PTree.t

  val get : int -> 'a1 t -> 'a1

  val set : int -> 'a1 -> 'a1 t -> 'a1 * 'a1 PTree.tree

  val map : ('a1 -> 'a2) -> 'a1 t -> 'a2 t
 end

module type INDEXED_TYPE =
 sig
  type t

  val index : t -> int

  val eq : t -> t -> bool
 end

module IMap :
 functor (X:INDEXED_TYPE) ->
 sig
  type elt = X.t

  val elt_eq : X.t -> X.t -> bool

  type 'x t = 'x PMap.t

  val init : 'a1 -> 'a1 * 'a1 PTree.t

  val get : X.t -> 'a1 t -> 'a1

  val set : X.t -> 'a1 -> 'a1 t -> 'a1 * 'a1 PTree.tree

  val map : ('a1 -> 'a2) -> 'a1 t -> 'a2 t
 end

module ZIndexed :
 sig
  type t = int64

  val index : int64 -> int

  val eq : int64 -> int64 -> bool
 end

module ZMap :
 sig
  type elt = ZIndexed.t

  val elt_eq : ZIndexed.t -> ZIndexed.t -> bool

  type 'x t = 'x PMap.t

  val init : 'a1 -> 'a1 * 'a1 PTree.t

  val get : ZIndexed.t -> 'a1 t -> 'a1

  val set : ZIndexed.t -> 'a1 -> 'a1 t -> 'a1 * 'a1 PTree.tree

  val map : ('a1 -> 'a2) -> 'a1 t -> 'a2 t
 end

module type EQUALITY_TYPE =
 sig
  type t

  val eq : t -> t -> bool
 end

module EMap :
 functor (X:EQUALITY_TYPE) ->
 sig
  type elt = X.t

  val elt_eq : X.t -> X.t -> bool

  type 'a t = X.t -> 'a

  val init : 'a1 -> X.t -> 'a1

  val get : X.t -> 'a1 t -> 'a1

  val set : X.t -> 'a1 -> 'a1 t -> X.t -> 'a1

  val map : ('a1 -> 'a2) -> 'a1 t -> X.t -> 'a2
 end

val beq_dec : int64 -> int64 -> binary_float -> binary_float -> bool

type float = binary64

type float32 = binary32

module Float :
 sig
  val eq_dec : float -> float -> bool

  val to_bits : float -> Int64.int

  val of_bits : Int64.int -> float
 end

module Float32 :
 sig
  val eq_dec : float32 -> float32 -> bool

  val to_bits : float32 -> Int.int

  val of_bits : Int.int -> float32
 end

type memory_chunk =
| Mint8signed
| Mint8unsigned
| Mint16signed
| Mint16unsigned
| Mint32
| Mint64
| Mfloat32
| Mfloat64
| Many32
| Many64

type bpf_ireg =
| BR0
| BR1
| BR2
| BR3
| BR4
| BR5
| BR6
| BR7
| BR8
| BR9
| BR10

type off_ty = Int16.int

type snd_op =
| SOImm of Int.int
| SOReg of bpf_ireg

type condition =
| Eq0
| Gt0
| Ge
| Lt0
| Le
| SEt
| Ne
| SGt
| SGe
| SLt
| SLe

type binop =
| BPF_ADD
| BPF_SUB
| BPF_MUL
| BPF_DIV
| BPF_OR
| BPF_AND
| BPF_LSH
| BPF_RSH
| BPF_MOD
| BPF_XOR
| BPF_MOV
| BPF_ARSH

type pqrop =
| BPF_LMUL
| BPF_UDIV
| BPF_UREM
| BPF_SDIV
| BPF_SREM

type pqrop2 =
| BPF_UHMUL
| BPF_SHMUL

type sBPFV =
| V1
| V2

type bpf_instruction =
| BPF_LD_IMM of bpf_ireg * Int.int * Int.int
| BPF_LDX of memory_chunk * bpf_ireg * bpf_ireg * Int16.int
| BPF_ST of memory_chunk * bpf_ireg * snd_op * Int16.int
| BPF_ADD_STK of Int.int
| BPF_ALU of binop * bpf_ireg * snd_op
| BPF_NEG32_REG of bpf_ireg
| BPF_LE of bpf_ireg * Int.int
| BPF_BE of bpf_ireg * Int.int
| BPF_ALU64 of binop * bpf_ireg * snd_op
| BPF_NEG64_REG of bpf_ireg
| BPF_HOR64_IMM of bpf_ireg * Int.int
| BPF_PQR of pqrop * bpf_ireg * snd_op
| BPF_PQR64 of pqrop * bpf_ireg * snd_op
| BPF_PQR2 of pqrop2 * bpf_ireg * snd_op
| BPF_JA of off_ty
| BPF_JUMP of condition * bpf_ireg * snd_op * off_ty
| BPF_CALL_REG of bpf_ireg * Int.int
| BPF_CALL_IMM of bpf_ireg * Int.int
| BPF_EXIT

type bpf_bin = Int64.int list

val nat_to_bpf_ireg : int -> bpf_ireg option

val iNSN_SIZE : int

val mM_STACK_START : Int64.int

type func_key = Int.int

type func_val = Int64.int

module Coq_func_Eq :
 sig
  type t = func_key

  val eq : Int.int -> Int.int -> bool
 end

module Coq_func_Map :
 sig
  type elt = Coq_func_Eq.t

  val elt_eq : Coq_func_Eq.t -> Coq_func_Eq.t -> bool

  type 'a t = Coq_func_Eq.t -> 'a

  val init : 'a1 -> Coq_func_Eq.t -> 'a1

  val get : Coq_func_Eq.t -> 'a1 t -> 'a1

  val set : Coq_func_Eq.t -> 'a1 -> 'a1 t -> Coq_func_Eq.t -> 'a1

  val map : ('a1 -> 'a2) -> 'a1 t -> Coq_func_Eq.t -> 'a2
 end

type func_map = func_val option Coq_func_Map.t

val init_func_map : func_map

val get_function_registry : func_key -> func_map -> func_val option

val max_call_depth : usize

val stack_frame_size : usize

type callFrame = { caller_saved_registers : Int64.int list;
                   frame_pointer : Int64.int; target_pc : Int64.int }

val reg_eq : bpf_ireg -> bpf_ireg -> bool

module Coq_reg_Eq :
 sig
  type t = bpf_ireg

  val eq : bpf_ireg -> bpf_ireg -> bool
 end

module Coq_reg_Map :
 sig
  type elt = Coq_reg_Eq.t

  val elt_eq : Coq_reg_Eq.t -> Coq_reg_Eq.t -> bool

  type 'a t = Coq_reg_Eq.t -> 'a

  val init : 'a1 -> Coq_reg_Eq.t -> 'a1

  val get : Coq_reg_Eq.t -> 'a1 t -> 'a1

  val set : Coq_reg_Eq.t -> 'a1 -> 'a1 t -> Coq_reg_Eq.t -> 'a1

  val map : ('a1 -> 'a2) -> 'a1 t -> Coq_reg_Eq.t -> 'a2
 end

type reg_map = Int64.int Coq_reg_Map.t

type block = int

val eq_block : int -> int -> bool

type val0 =
| Vundef
| Vint of Int.int
| Vlong of Int64.int
| Vfloat of float
| Vsingle of float32
| Vptr of block * Ptrofs.int

module Val :
 sig
  val eq : val0 -> val0 -> bool

  val load_result : memory_chunk -> val0 -> val0
 end

val size_chunk : memory_chunk -> int64

val size_chunk_nat : memory_chunk -> int

val align_chunk : memory_chunk -> int64

type quantity =
| Q32
| Q64

val quantity_eq : quantity -> quantity -> bool

val size_quantity_nat : quantity -> int

type memval =
| Undef
| Byte of Byte.int
| Fragment of val0 * quantity * int

val bytes_of_int : int -> int64 -> Byte.int list

val int_of_bytes : Byte.int list -> int64

val rev_if_be : Byte.int list -> Byte.int list

val encode_int : int -> int64 -> Byte.int list

val decode_int : Byte.int list -> int64

val inj_bytes : Byte.int list -> memval list

val proj_bytes : memval list -> Byte.int list option

val inj_value_rec : int -> val0 -> quantity -> memval list

val inj_value : quantity -> val0 -> memval list

val check_value : int -> val0 -> quantity -> memval list -> bool

val proj_value : quantity -> memval list -> val0

val encode_val : memory_chunk -> val0 -> memval list

val decode_val : memory_chunk -> memval list -> val0

type permission =
| Freeable
| Writable
| Readable
| Nonempty

type perm_kind =
| Max
| Cur

module Mem :
 sig
  type mem' = { mem_contents : memval ZMap.t PMap.t;
                mem_access : (int64 -> perm_kind -> permission option) PMap.t;
                nextblock : block }

  val mem_contents : mem' -> memval ZMap.t PMap.t

  val mem_access : mem' -> (int64 -> perm_kind -> permission option) PMap.t

  val nextblock : mem' -> block

  type mem = mem'

  val perm_order_dec : permission -> permission -> bool

  val perm_order'_dec : permission option -> permission -> bool

  val perm_dec : mem -> block -> int64 -> perm_kind -> permission -> bool

  val range_perm_dec :
    mem -> block -> int64 -> int64 -> perm_kind -> permission -> bool

  val valid_access_dec :
    mem -> memory_chunk -> block -> int64 -> permission -> bool

  val empty : mem

  val getN : int -> int64 -> memval ZMap.t -> memval list

  val load : memory_chunk -> mem -> block -> int64 -> val0 option

  val loadv : memory_chunk -> mem -> val0 -> val0 option

  val setN : memval list -> int64 -> memval ZMap.t -> memval ZMap.t

  val store : memory_chunk -> mem -> block -> int64 -> val0 -> mem option

  val storev : memory_chunk -> mem -> val0 -> val0 -> mem option

  val storebytes : mem -> block -> int64 -> memval list -> mem option
 end

val decode_bpf : Int64.int -> int -> int -> Int64.int

val rbpf_decoder_one :
  Byte.int -> int -> int -> Int16.int -> Int.int -> bpf_instruction option

val rbpf_decoder : int -> Int64.int list -> bpf_instruction option

type stack_state = { call_depth : Int64.int; stack_pointer : Int64.int;
                     call_frames : callFrame list }

val eval_reg : bpf_ireg -> reg_map -> Int64.int

val create_list : int -> 'a1 -> 'a1 list

val mM_INPUT_START : Int64.int

val init_stack_state : stack_state

type bpf_state =
| BPF_OK of Int64.int * reg_map * Mem.mem * stack_state * sBPFV * func_map
   * Int64.int * Int64.int
| BPF_Success of Int64.int
| BPF_EFlag
| BPF_Err

val init_reg_map : reg_map

val init_bpf_state : reg_map -> Mem.mem -> Int64.int -> sBPFV -> bpf_state

type 'a option2 =
| NOK
| OKS of 'a
| OKN

val eval_snd_op_u32 : snd_op -> reg_map -> Int.int

val eval_snd_op_i32 : snd_op -> reg_map -> Int.int

val eval_snd_op_u64 : snd_op -> reg_map -> Int64.int

val eval_snd_op_i64 : snd_op -> reg_map -> Int64.int

val eval_alu32_aux1 :
  binop -> bpf_ireg -> snd_op -> reg_map -> bool -> reg_map option2

val eval_alu32_aux2 :
  binop -> bpf_ireg -> snd_op -> reg_map -> reg_map option2

val eval_alu32_aux3 :
  binop -> bpf_ireg -> snd_op -> reg_map -> reg_map option2

val eval_alu32 :
  binop -> bpf_ireg -> snd_op -> reg_map -> bool -> reg_map option2

val eval_alu64_aux1 :
  binop -> bpf_ireg -> snd_op -> reg_map -> bool -> reg_map option2

val eval_alu64_aux2 :
  binop -> bpf_ireg -> snd_op -> reg_map -> reg_map option2

val eval_alu64_aux3 :
  binop -> bpf_ireg -> snd_op -> reg_map -> reg_map option2

val eval_add64_imm_R10 : Int.int -> stack_state -> bool -> stack_state option

val eval_alu64 :
  binop -> bpf_ireg -> snd_op -> reg_map -> bool -> reg_map option2

val eval_neg32 : bpf_ireg -> reg_map -> bool -> reg_map option2

val eval_neg64 : bpf_ireg -> reg_map -> bool -> reg_map option2

val eval_le : bpf_ireg -> Int.int -> reg_map -> bool -> reg_map option2

val eval_be : bpf_ireg -> Int.int -> reg_map -> bool -> reg_map option2

val eval_hor64 : bpf_ireg -> Int.int -> reg_map -> bool -> reg_map option2

val eval_pqr32_aux1 :
  pqrop -> bpf_ireg -> snd_op -> reg_map -> reg_map option2

val eval_pqr32_aux2 :
  pqrop -> bpf_ireg -> snd_op -> reg_map -> reg_map option2

val eval_pqr32 :
  pqrop -> bpf_ireg -> snd_op -> reg_map -> bool -> reg_map option2

val eval_pqr64_aux1 :
  pqrop -> bpf_ireg -> snd_op -> reg_map -> reg_map option2

val eval_pqr64_aux2 :
  pqrop -> bpf_ireg -> snd_op -> reg_map -> reg_map option2

val eval_pqr64 :
  pqrop -> bpf_ireg -> snd_op -> reg_map -> bool -> reg_map option2

val eval_pqr64_2 :
  pqrop2 -> bpf_ireg -> snd_op -> reg_map -> bool -> reg_map option2

val concrete_addr_to_abstract_addr : Int64.int -> block -> val0

val memory_chunk_value_of_int64 : memory_chunk -> Int64.int -> val0

val eval_store :
  memory_chunk -> bpf_ireg -> snd_op -> off_ty -> reg_map -> Mem.mem -> block
  -> Mem.mem option

val eval_load :
  memory_chunk -> bpf_ireg -> bpf_ireg -> off_ty -> reg_map -> Mem.mem ->
  reg_map option

val eval_load_imm : bpf_ireg -> Int.int -> Int.int -> reg_map -> reg_map

val eval_jmp : condition -> bpf_ireg -> snd_op -> reg_map -> bool

val list_update : 'a1 list -> int -> 'a1 -> 'a1 list

val push_frame :
  reg_map -> stack_state -> bool -> Int64.int -> bool -> stack_state
  option * reg_map

val eval_call_reg :
  bpf_ireg -> Int.int -> reg_map -> stack_state -> bool -> Int64.int ->
  func_map -> bool -> Int64.int -> ((Int64.int * reg_map) * stack_state)
  option

val eval_call_imm :
  Int64.int -> bpf_ireg -> Int.int -> reg_map -> stack_state -> bool ->
  func_map -> bool -> ((Int64.int * reg_map) * stack_state) option

val eval_exit :
  reg_map -> stack_state -> bool -> (Int64.int * reg_map) * stack_state

val step :
  Int64.int -> bpf_instruction -> reg_map -> Mem.mem -> stack_state -> sBPFV
  -> func_map -> bool -> Int64.int -> Int64.int -> Int64.int -> block ->
  bpf_state

val bpf_interp :
  int -> bpf_bin -> bpf_state -> bool -> Int64.int -> block -> bpf_state

val int_to_byte_list : Int.int list -> Byte.int list

val int_to_int64_list : Int.int list -> Int64.int list

val get_bytes : Byte.int list -> memval list

val byte_list_to_mem : Byte.int list -> Mem.mem -> block -> int64 -> Mem.mem

val bpf_interp_test :
  Int.int list -> Int.int list -> Int.int list -> Int.int -> Int.int ->
  Int.int -> bool -> bool
