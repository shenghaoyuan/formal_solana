Require Import ZArith List.
Require Import Coqlib Zbits.
From compcert.lib Require Import Integers Maps.
Require Import rBPFCommType.
Require Import Val.

Print Int64.

Module mem_Eq.
  Definition t := u64.
  Definition eq := Int64.eq_dec.
End mem_Eq.

Module mem_map := EMap(mem_Eq).

Definition mem := mem_map.t (option u8).

Print EMap.

Definition init_mem : mem := mem_map.init None.

Definition addr_type := u64.

Inductive memory_chunk : Type :=
  | M8
  | M16
  | M32
  | M64.

Definition option_u64_of_u8_1 (v : option u8) : option u64 :=
  match v with
  | None => None
  | Some v' => Some (Int64.repr (Byte.unsigned v'))
  end.

Definition option_u64_of_u8_2 (v0 v1 : option u8) : option int64 :=
  match v0, v1 with
  | Some v0', Some v1' =>
      Some (Int64.or (bit_left_shift_int64 (Int64.repr (Byte.unsigned v1')) 8)
                     (Int64.repr (Byte.unsigned v0')))
  | _, _ => None
  end.

Definition option_u64_of_u8_4 (v0 v1 v2 v3 : option u8) : option int64 :=
  match v0, v1, v2, v3 with
  | Some v0', Some v1', Some v2', Some v3' =>
      Some (Int64.or (bit_left_shift_int64 (Int64.repr (Byte.unsigned v3')) 24)
           (Int64.or (bit_left_shift_int64 (Int64.repr (Byte.unsigned v2')) 16)
           (Int64.or (bit_left_shift_int64 (Int64.repr (Byte.unsigned v1')) 8)
                     (Int64.repr (Byte.unsigned v0')))))
  | _, _, _, _ => None
  end.

Definition option_u64_of_u8_8 (v0 v1 v2 v3 v4 v5 v6 v7 : option u8) : option int64 :=
  match v0, v1, v2, v3, v4, v5, v6, v7 with
  | Some v0', Some v1', Some v2', Some v3', Some v4', Some v5', Some v6', Some v7' =>
      Some (Int64.or (bit_left_shift_int64 (Int64.repr (Byte.unsigned v7')) 56)
           (Int64.or (bit_left_shift_int64 (Int64.repr (Byte.unsigned v6')) 48)
           (Int64.or (bit_left_shift_int64 (Int64.repr (Byte.unsigned v5')) 40)
           (Int64.or (bit_left_shift_int64 (Int64.repr (Byte.unsigned v4')) 32)
           (Int64.or (bit_left_shift_int64 (Int64.repr (Byte.unsigned v3')) 24)
           (Int64.or (bit_left_shift_int64 (Int64.repr (Byte.unsigned v2')) 16)
           (Int64.or (bit_left_shift_int64 (Int64.repr (Byte.unsigned v1')) 8)
                     (Int64.repr (Byte.unsigned v0')))))))))
  | _, _, _, _, _, _, _, _ => None
  end.

Definition memory_chunk_value_of_u64 (mc : memory_chunk) (v : u64) : val :=
  match mc with
  | M8  => Vbyte (Byte.repr (Int64.unsigned v))
  | M16 => Vshort (Word.repr (Int64.unsigned v))
  | M32 => Vint (Int.repr (Int64.unsigned v))
  | M64 => Vlong v
  end.
Require Import Coq.PArith.BinPos.

Definition option_val_of_u64 (mc : memory_chunk) (v : option u64) : option val :=
  match v with
  | Some v' => Some (memory_chunk_value_of_u64 mc v')
  | None => None
  end.

Definition loadv (mc : memory_chunk) (m : mem) (addr : addr_type) : option val :=
  option_val_of_u64 mc
    (match mc with
     | M8  => option_u64_of_u8_1 (mem_map.get addr m)
     | M16 => option_u64_of_u8_2 (mem_map.get addr m) (mem_map.get (Int64.add addr (Int64.repr 1)) m)
     | M32 => option_u64_of_u8_4 (mem_map.get addr m)
                                   (mem_map.get (Int64.add addr (Int64.repr 1)) m)
                                   (mem_map.get (Int64.add addr (Int64.repr 1)) m)
                                   (mem_map.get (Int64.add addr (Int64.repr 1)) m)
     | M64 => option_u64_of_u8_8 (mem_map.get addr m)
                                   (mem_map.get (Int64.add addr (Int64.repr 1)) m)
                                   (mem_map.get (Int64.add addr (Int64.repr 1)) m)
                                   (mem_map.get (Int64.add addr (Int64.repr 1)) m)
                                   (mem_map.get (Int64.add addr (Int64.repr 1)) m)
                                   (mem_map.get (Int64.add addr (Int64.repr 1)) m)
                                   (mem_map.get (Int64.add addr (Int64.repr 1)) m)
                                   (mem_map.get (Int64.add addr (Int64.repr 1)) m)
     end).

Definition storev (mc : memory_chunk) (m : mem) (addr : addr_type) (v : val) : option mem :=
  match mc with
  | M8  =>
      match v with
      | Vbyte v' =>
          Some (mem_map.set addr (Some v') m)
      | _        => None
      end
  | M16 =>
      match v with
      | Vshort v' =>
          let l := (u8_list_of_u16 v') in
          let mem' := mem_map.set addr (Some (List.nth 0 l Byte.zero)) m in
          Some (mem_map.set (Int64.add addr (Int64.repr 1)) (Some (List.nth 1 l Byte.zero)) m)
      | _        => None
      end
  | M32 =>
      match v with
      | Vint v' =>
          let l := u8_list_of_u32 v' in
          let mem' := mem_map.set addr (Some (List.nth 0 l Byte.zero)) m in
          let mem' := mem_map.set (Int64.add addr (Int64.repr 1)) (Some (List.nth 1 l Byte.zero)) m in
          let mem' := mem_map.set (Int64.add addr (Int64.repr 2)) (Some (List.nth 2 l Byte.zero)) m in
          Some (mem_map.set (Int64.add addr (Int64.repr 3))  (Some (List.nth 3 l Byte.zero)) m)
      | _        => None
      end
  | M64 =>
      match v with
      | Vlong v' =>
          let l := u8_list_of_u64 v' in
          let mem' := mem_map.set addr (Some (List.nth 0 l Byte.zero)) m in
          let mem' := mem_map.set (Int64.add addr (Int64.repr 1)) (Some (List.nth 1 l Byte.zero)) m in
          let mem' := mem_map.set (Int64.add addr (Int64.repr 2)) (Some (List.nth 2 l Byte.zero)) m in
          let mem' := mem_map.set (Int64.add addr (Int64.repr 3)) (Some (List.nth 3 l Byte.zero)) m in
          let mem' := mem_map.set (Int64.add addr (Int64.repr 4)) (Some (List.nth 4 l Byte.zero)) m in
          let mem' := mem_map.set (Int64.add addr (Int64.repr 5)) (Some (List.nth 5 l Byte.zero)) m in
          let mem' := mem_map.set (Int64.add addr (Int64.repr 6)) (Some (List.nth 6 l Byte.zero)) m in
          Some (mem_map.set (Int64.add addr (Int64.repr 7)) (Some (List.nth 7 l Byte.zero)) m)
      | _        => None
      end   
  end.

Definition vlong_of_memory_chunk (mc : memory_chunk) : val :=
  match mc with
  | M8  => Vlong (Int64.repr 8)
  | M16 => Vlong (Int64.repr 16)
  | M32 => Vlong (Int64.repr 32)
  | M64 => Vlong (Int64.repr 64)
  end.

Axiom store_load_consistency :
  forall (mc: memory_chunk) (m: mem) (place: u64) (v: val),
    storev mc m place v = Some m -> loadv mc m place = Some v.
  

















