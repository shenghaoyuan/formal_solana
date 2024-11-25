Require Import ZArith List.
Require Import Coqlib Zbits.
From compcert.lib Require Import Integers.
Require Import rBPFCommType.

Definition sub_overflowi32 (x y bin : u32) : u32 :=
  let s := (Int.signed x) - (Int.signed y) - (Int.signed bin) in
  if Z.leb (Int.signed i32_MIN) s && Z.leb s (Int.signed i32_MAX) then 
    Int.repr 0 
  else
    Int.repr 1.

Compute (sub_overflowi32 (Int.repr 2147483647) (Int.repr (-1))(Int.repr 2147483647)).

Compute ((Int.signed (Int.repr (-1)))).

Definition sub_overflowi64 (x y bin : u64) : u64 :=
  let s := (Int64.signed x) - (Int64.signed y) - (Int64.signed bin) in
  if Z.leb (Int64.signed i64_MIN) s && Z.leb s (Int64.signed i64_MAX) then 
    Int64.repr 0 
  else
    Int64.repr 1.

Inductive val : Type :=
  | Vundef : val
  | Vbyte : u8 -> val
  | Vshort : u16 -> val
  | Vint : u32 -> val
  | Vlong : u64 -> val.

Print Word.rol.

Definition rol16 (v n : val) : val :=
  match v, n with
  | Vshort v1, Vbyte n1 =>
      Vshort (Word.rol v1 (Word.repr ((Byte.unsigned n1) mod 16)))
  | _, _ => Vundef
  end.

Definition add16 (v1 v2 : val) : val :=
  match v1, v2 with
  | Vshort v1', Vshort v2' =>
      Vshort (Word.add v1' v2')
  | _, _ => Vundef
  end.

Definition long_of_int_unsigned (v : val) : val :=
  match v with
  | Vint v' => 
      Vlong (Int64.repr (Int.unsigned v'))
  | _ => Vundef
  end.

Definition long_of_int_signed (v : val) : val :=
  match v with
  | Vint v' =>
      if Int.testbit v' 31 then
        Vlong (Int64.or (Int64.repr (Int.unsigned v')) (Int64.repr 0xffffffff00000000))
      else
        Vlong (Int64.repr (Int.unsigned v'))
  | _ => Vundef
  end.

Definition int_of_long_low (v : val) : val :=
  match v with
  | Vlong v' =>
      Vint (Int.repr (Int64.unsigned v'))
  | _ => Vundef
  end.

Print Int64.shr.

Definition int_of_long_high (v : val) : val :=
  match v with
  | Vlong v' =>
      Vint (Int.repr (Int64.unsigned (bit_right_shift_int64 v' 32)))
  | _ => Vundef
  end.

Definition signex32 (v : val) : val :=
  match v with
  | Vint v' =>
      int_of_long_high (long_of_int_signed v)
  | _ => Vundef
  end.

Definition neg32 (v : val) : val :=
  match v with
  | Vint v' =>
      Vint (Int.neg v')
  | _ => Vundef
  end.

Definition maketotal (ov : option val) : val :=
  match ov with
  | Some v => v
  | None => Vundef
  end.

Definition add32 (v1 v2 : val) : val :=
  match v1, v2 with
  | Vint v1', Vint v2' =>
      Vint (Int.add v1' v2')
  | _, _ => Vundef
  end.

Definition sub32 (v1 v2 : val) : val :=
  match v1, v2 with
  | Vint v1', Vint v2' =>
      Vint (Int.sub v1' v2')
  | _, _ => Vundef
  end.

Definition mul32 (v1 v2 : val) : val :=
  match v1, v2 with
  | Vint v1', Vint v2' =>
      Vint (Int.mul v1' v2')
  | _, _ => Vundef
  end.

Definition mulhu32 (v1 v2 : val) : val :=
  match v1, v2 with
  | Vint v1', Vint v2' =>
      Vint (Int.mulhu v1' v2')
  | _, _ => Vundef
  end.

Definition mulhs32 (v1 v2 : val) : val :=
  match v1, v2 with
  | Vint v1', Vint v2' =>
      Vint (Int.mulhs v1' v2')
  | _, _ => Vundef
  end.

Definition divmod32u (v1 v2 v3: val) : option (val * val) :=
  match v1, v2, v3 with
  | Vint nh, Vint nl, Vint d =>
      match Int.divmodu2 nh nl d with
      | Some (quotient, remainder) => Some (Vint quotient, Vint remainder)
      | None => None
      end
  | _, _, _ => None
  end.

Definition divmod32s (v1 v2 v3: val) : option (val * val) :=
  match v1, v2, v3 with
  | Vint nh, Vint nl, Vint d =>
      match Int.divmods2 nh nl d with
      | Some (quotient, remainder) => Some (Vint quotient, Vint remainder)
      | None => None
      end
  | _, _, _ => None
  end.

Definition bswap32 (v : val) : val :=
  match v with
  | Vint v' =>
      let byte0 := bit_left_shift_int (Int.and v' (Int.repr 0xFF)) 24 in
      let byte1 := bit_left_shift_int (Int.and v' (Int.repr 0xFF00)) 8 in
      let byte2 := bit_right_shift_int (Int.and v' (Int.repr 0xFF0000)) 8 in
      let byte3 := bit_right_shift_int (Int.and v' (Int.repr 0xFF000000)) 24 in
      Vint (Int.or (Int.or (Int.or byte0 byte1) byte2) byte3)
  | _ => Vundef
  end.

Definition sub_overflow32 (v1 v2 : val) : val :=
  match v1, v2 with
  | Vint v1', Vint v2' =>
      Vint (sub_overflowi32 v1' v2' (Int.repr 0))
  | _, _ => Vundef
  end.

Definition negative32 (v : val) : val :=
  match v with
  | Vint v' =>
      if Int.testbit v' 31 then
        Vint Int.one
      else
        Vint Int.zero
  | _ => Vundef
  end.

Definition or32 (v1 v2 : val) : val :=
  match v1, v2 with
  | Vint v1', Vint v2' =>
      Vint (Int.or v1' v2')
  | _, _ => Vundef
  end.

Definition and32 (v1 v2 : val) : val :=
  match v1, v2 with
  | Vint v1', Vint v2' =>
      Vint (Int.and v1' v2')
  | _, _ => Vundef
  end.

Definition xor32 (v1 v2 : val) : val :=
  match v1, v2 with
  | Vint v1', Vint v2' =>
      Vint (Int.xor v1' v2')
  | _, _ => Vundef
  end.

Definition shl32 (v1 v2 : val) : val :=
  match v1, v2 with
  | Vint v1', Vbyte v2' =>
      Vint (Int.shl v1' (Int.repr (Byte.unsigned v2')))
  | _, _ => Vundef
  end.

Definition shru32 (v1 v2 : val) : val :=
  match v1, v2 with
  | Vint v1', Vbyte v2' =>
      Vint (Int.shru v1' (Int.repr (Byte.unsigned v2')))
  | _, _ => Vundef
  end.

Definition shr32 (v1 v2 : val) : val :=
  match v1, v2 with
  | Vint v1', Vbyte v2' =>
      Vint (Int.shr v1' (Int.repr (Byte.unsigned v2')))
  | _, _ => Vundef
  end.

Definition ror32 (v1 v2 : val) : val :=
  match v1, v2 with
  | Vint v1', Vbyte v2' =>
      Vint (Int.ror v1' (Int.repr (Byte.unsigned v2')))
  | _, _ => Vundef
  end.

Definition signex64 (v : val) : val :=
  match v with
  | Vlong v' =>
      if Int64.testbit v' 63 then
        Vlong ((Int64.repr 0xffffffffffffffff))
      else
        Vlong ((Int64.repr 0))
  | _ => Vundef
  end.

Definition neg64 (v : val) : val :=
  match v with
  | Vlong v' =>
      Vlong (Int64.neg v')
  | _ => Vundef
  end.

Definition add64 (v1 v2 : val) : val :=
  match v1, v2 with
  | Vlong v1', Vlong v2' =>
      Vlong (Int64.add v1' v2')
  | _, _ => Vundef
  end.

Definition sub64 (v1 v2 : val) : val :=
  match v1, v2 with
  | Vlong v1', Vlong v2' =>
      Vlong (Int64.sub v1' v2')
  | _, _ => Vundef
  end.

Definition mul64 (v1 v2 : val) : val :=
  match v1, v2 with
  | Vlong v1', Vlong v2' =>
      Vlong (Int64.mul v1' v2')
  | _, _ => Vundef
  end.

Definition mulhu64 (v1 v2 : val) : val :=
  match v1, v2 with
  | Vlong v1', Vlong v2' =>
      Vlong (Int64.mulhu v1' v2')
  | _, _ => Vundef
  end.

Definition mulhs64 (v1 v2 : val) : val :=
  match v1, v2 with
  | Vlong v1', Vlong v2' =>
      Vlong (Int64.mulhs v1' v2')
  | _, _ => Vundef
  end.

Definition divmod64u (v1 v2 v3: val) : option (val * val) :=
  match v1, v2, v3 with
  | Vlong nh, Vlong nl, Vlong d =>
      match Int64.divmodu2 nh nl d with
      | Some (quotient, remainder) => Some (Vlong quotient, Vlong remainder)
      | None => None
      end
  | _, _, _ => None
  end.

Definition divmod64s (v1 v2 v3: val) : option (val * val) :=
  match v1, v2, v3 with
  | Vlong nh, Vlong nl, Vlong d =>
      match Int64.divmods2 nh nl d with
      | Some (quotient, remainder) => Some (Vlong quotient, Vlong remainder)
      | None => None
      end
  | _, _, _ => None
  end.

Definition sub_overflow64 (v1 v2 : val) : val :=
  match v1, v2 with
  | Vlong v1', Vlong v2' =>
      Vlong (sub_overflowi64 v1' v2' (Int64.repr 0))
  | _, _ => Vundef
  end.

Definition negative64 (v : val) : val :=
  match v with
  | Vlong v' =>
      if Int64.testbit v' 63 then
        Vlong Int64.one
      else
        Vlong Int64.zero
  | _ => Vundef
  end.

Definition or64 (v1 v2 : val) : val :=
  match v1, v2 with
  | Vlong v1', Vlong v2' =>
      Vlong (Int64.or v1' v2')
  | _, _ => Vundef
  end.

Definition and64 (v1 v2 : val) : val :=
  match v1, v2 with
  | Vlong v1', Vlong v2' =>
      Vlong (Int64.and v1' v2')
  | _, _ => Vundef
  end.

Definition xor64 (v1 v2 : val) : val :=
  match v1, v2 with
  | Vlong v1', Vlong v2' =>
      Vlong (Int64.xor v1' v2')
  | _, _ => Vundef
  end.

Definition shl64 (v1 v2 : val) : val :=
  match v1, v2 with
  | Vlong v1', Vbyte v2' =>
      Vlong (Int64.shl v1' (Int64.repr (Byte.unsigned v2')))
  | _, _ => Vundef
  end.

Definition shru64 (v1 v2 : val) : val :=
  match v1, v2 with
  | Vlong v1', Vbyte v2' =>
      Vlong (Int64.shru v1' (Int64.repr (Byte.unsigned v2')))
  | _, _ => Vundef
  end.

Definition shr64 (v1 v2 : val) : val :=
  match v1, v2 with
  | Vlong v1', Vbyte v2' =>
      Vlong (Int64.shr v1' (Int64.repr (Byte.unsigned v2')))
  | _, _ => Vundef
  end.

Definition ror64 (v1 v2 : val) : val :=
  match v1, v2 with
  | Vlong v1', Vbyte v2' =>
      Vlong (Int64.ror v1' (Int64.repr (Byte.unsigned v2')))
  | _, _ => Vundef
  end.

Definition bswap64 (v : val) : val :=
  match v with
  | Vlong v' =>
      let byte0 := bit_left_shift_int64 (Int64.and v' (Int64.repr 0xFF)) 56 in
      let byte1 := bit_left_shift_int64 (Int64.and v' (Int64.repr 0xFF00)) 40 in
      let byte2 := bit_left_shift_int64 (Int64.and v' (Int64.repr 0xFF0000)) 24 in
      let byte3 := bit_left_shift_int64 (Int64.and v' (Int64.repr 0xFF000000)) 8 in
      let byte4 := bit_right_shift_int64 (Int64.and v' (Int64.repr 0xFF0000)) 8 in
      let byte5 := bit_right_shift_int64 (Int64.and v' (Int64.repr 0xFF000000)) 24 in
      let byte6 := bit_right_shift_int64 (Int64.and v' (Int64.repr 0xFF0000)) 40 in
      let byte7 := bit_right_shift_int64 (Int64.and v' (Int64.repr 0xFF000000)) 56 in
      Vlong (Int64.or (Int64.or (Int64.or (Int64.or (Int64.or (Int64.or (Int64.or byte0 byte1)
            byte2) byte3) byte4) byte5) byte6) byte7)
  | _ => Vundef
  end.

Inductive comparison :=
  | Ceq (* equal *)
  | Cne (* not equal *)
  | Clt (* less than *)
  | Cle (* less than or equal *)
  | Cgt (* greater than *)
  | Cge (* greater than or equal *).

Definition cmpi32 (c : comparison) (x y : i32) : bool :=
  match c with
  | Ceq => Int.eq x y
  | Cne => negb (Int.eq x y)
  | Clt => Int.signed x <? Int.signed y
  | Cle => Int.signed x <=? Int.signed y
  | Cgt => Int.signed y <? Int.signed x
  | Cge => Int.signed y <=? Int.signed x
  end.

Definition cmpu32 (c : comparison) (x y : u32) : bool :=
  match c with
  | Ceq => Int.eq x y
  | Cne => negb (Int.eq x y)
  | Clt => Int.unsigned x <? Int.unsigned y
  | Cle => Int.unsigned x <=? Int.unsigned y
  | Cgt => Int.unsigned y <? Int.unsigned x
  | Cge => Int.unsigned y <=? Int.unsigned x
  end.

Definition cmpi64 (c : comparison) (x y : i64) : bool :=
  match c with
  | Ceq => Int64.eq x y
  | Cne => negb (Int64.eq x y)
  | Clt => Int64.signed x <? Int64.signed y
  | Cle => Int64.signed x <=? Int64.signed y
  | Cgt => Int64.signed y <? Int64.signed x
  | Cge => Int64.signed y <=? Int64.signed x
  end.

Definition cmpu64 (c : comparison) (x y : u64) : bool :=
  match c with
  | Ceq => Int64.eq x y
  | Cne => negb (Int64.eq x y)
  | Clt => Int64.unsigned x <? Int64.unsigned y
  | Cle => Int64.unsigned x <=? Int64.unsigned y
  | Cgt => Int64.unsigned y <? Int64.unsigned x
  | Cge => Int64.unsigned y <=? Int64.unsigned x
  end.

Definition cmp_bool (c : comparison) (v1 v2 : val) : option bool :=
  match v1, v2 with
  | Vint v1', Vint v2' =>
      Some (cmpi32 c (Int.repr (Int.signed v1')) (Int.repr (Int.signed v2')))
  | _, _ => None
  end.

Definition cmpu_bool (c : comparison) (v1 v2 : val) : option bool :=
  match v1, v2 with
  | Vint v1', Vint v2' =>
      Some (cmpu32 c v1' v2')
  | _, _ => None
  end.

Definition cmpl_bool (c : comparison) (v1 v2 : val) : option bool :=
  match v1, v2 with
  | Vlong v1', Vlong v2' =>
      Some (cmpi64 c (Int64.repr (Int64.signed v1')) (Int64.repr (Int64.signed v2')))
  | _, _ => None
  end.

Definition cmplu_bool (c : comparison) (v1 v2 : val) : option bool :=
  match v1, v2 with
  | Vlong v1', Vlong v2' =>
      Some (cmpu64 c v1' v2')
  | _, _ => None
  end.

Definition of_optbool (ob : option bool) : val :=
  match ob with
  | Some true  => Vint Int.one
  | Some false => Vint Int.zero
  | None       => Vundef
  end.

Definition cmp (c : comparison) (v1 v2 : val) : val :=
  of_optbool (cmp_bool c v1 v2).

Definition cmpu (c : comparison) (v1 v2 : val) : val :=
  of_optbool (cmpu_bool c v1 v2).

Definition cmpl (c : comparison) (v1 v2 : val) : val :=
  of_optbool (cmpl_bool c v1 v2).

Definition cmplu (c : comparison) (v1 v2 : val) : val :=
  of_optbool (cmplu_bool c v1 v2).









