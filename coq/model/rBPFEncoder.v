From Coq Require Import ZArith List.
From compcert.lib Require Import Integers Maps.
From compcert.common Require Import Memory AST.
From bpf.model Require Import ebpf rBPFCommType rBPFSyntax.

Import ListNotations.

Definition encode_bpf (v ins: int64) (from size: nat): int64 :=
  Int64.bitfield_insert (Z.of_nat from) (Z.of_nat size) ins v.

Definition binary_to_int64
  (opc : byte) (dv : nat) (sv : nat) (off : int16) (imm : int) : int64 :=
  let v1 := encode_bpf (Int64.repr (Byte.unsigned opc)) (Int64.repr 0%Z) 0 8 in
  let v2 := encode_bpf (Int64.repr (Z.of_nat dv)) v1 8 4 in
  let v3 := encode_bpf (Int64.repr (Z.of_nat sv)) v2 12 4 in
  let v4 := encode_bpf (Int64.repr (Int16.unsigned off)) v3 16 16 in
    encode_bpf (Int64.repr (Int.unsigned imm)) v4 32 32.

Definition rbpf_encoder (ins : bpf_instruction) : list int64 :=
  let l : list int64 := [] in
  match ins with
  | BPF_LD_IMM dst imm1 imm2 =>
      let opc : byte := Byte.repr 0x18%Z in
      let dst_i : nat := bpf_ireg_to_nat dst in
      [binary_to_int64 opc dst_i 0 (Int16.repr 0%Z) imm1 ; binary_to_int64 (Byte.repr 0%Z) 0 0 (Int16.repr 0%Z) imm2]
  | BPF_LDX mc dst src off =>
      let opc : byte := Byte.repr (match mc with
                                 | M8 => 0x71%Z
                                 | M16 => 0x69%Z
                                 | M32 => 0x61%Z
                                 | M64 => 0x79%Z
                                end) in
      let dst_i : nat := bpf_ireg_to_nat dst in
      let src_i : nat := bpf_ireg_to_nat src in
      [binary_to_int64 opc dst_i src_i off (Int.repr 0%Z)]
  | BPF_ST mc dst (SOImm imm) off =>
      let opc : byte := Byte.repr (match mc with
                                 | M8 => 0x72%Z
                                 | M16 => 0x6a%Z
                                 | M32 => 0x62%Z
                                 | M64 => 0x7a%Z
                                end) in
      let dst_i : nat := bpf_ireg_to_nat dst in
      [binary_to_int64 opc dst_i 0 off imm ]
  | BPF_ST mc dst (SOReg src) off =>
      let opc : byte := Byte.repr (match mc with
                                 | M8 => 0x73%Z
                                 | M16 => 0x6b%Z
                                 | M32 => 0x63%Z
                                 | M64 => 0x7b%Z
                                end) in
      let dst_i : nat := bpf_ireg_to_nat dst in
      let src_i : nat := bpf_ireg_to_nat src in
      [binary_to_int64 opc dst_i src_i off (Int.repr 0%Z)]

  | BPF_ADD_STK imm => 
      let opc : byte := Byte.repr 0x07%Z in
      [binary_to_int64 opc 11 0 (Int16.repr 0%Z) imm]

  | BPF_ALU bop dst (SOImm imm) =>
      let opc : byte := Byte.repr (match bop with
                                | BPF_ADD  => 0x04
                                | BPF_SUB  => 0x14
                                | BPF_MUL  => 0x24
                                | BPF_DIV  => 0x34
                                | BPF_OR   => 0x44
                                | BPF_AND  => 0x54
                                | BPF_LSH  => 0x64
                                | BPF_RSH  => 0x74
                                | BPF_MOD  => 0x94
                                | BPF_XOR  => 0xa4
                                | BPF_MOV  => 0xb4
                                | BPF_ARSH => 0xc4
                                end) in
      let dst_i : nat := bpf_ireg_to_nat dst in
      [binary_to_int64 opc dst_i 0 (Int16.repr 0%Z) imm]
  | BPF_ALU bop dst (SOReg src) =>
      let opc : byte := Byte.repr (match bop with
                                | BPF_ADD  => 0x0c
                                | BPF_SUB  => 0x1c
                                | BPF_MUL  => 0x2c
                                | BPF_DIV  => 0x3c
                                | BPF_OR   => 0x4c
                                | BPF_AND  => 0x5c
                                | BPF_LSH  => 0x6c
                                | BPF_RSH  => 0x7c
                                | BPF_MOD  => 0x9c
                                | BPF_XOR  => 0xac
                                | BPF_MOV  => 0xbc
                                | BPF_ARSH => 0xcc
                                end) in
      let dst_i : nat := bpf_ireg_to_nat dst in
      let src_i : nat := bpf_ireg_to_nat src in
      [binary_to_int64 opc dst_i src_i (Int16.repr 0%Z) (Int.repr 0%Z)]

  | BPF_NEG32_REG dst =>
      let opc : byte := Byte.repr 0x84%Z in
      let dst_i : nat := bpf_ireg_to_nat dst in
      [binary_to_int64 opc dst_i 0 (Int16.repr 0%Z) (Int.repr 0%Z)]

  | BPF_LE dst imm => 
      let opc : byte := Byte.repr 0xd4%Z in
      let dst_i : nat := bpf_ireg_to_nat dst in
      [binary_to_int64 opc dst_i 0 (Int16.repr 0%Z) imm]
  | BPF_BE dst imm => 
      let opc : byte := Byte.repr 0xdc%Z in
      let dst_i : nat := bpf_ireg_to_nat dst in
      [binary_to_int64 opc dst_i 0 (Int16.repr 0%Z) imm]

  | BPF_ALU64 bop dst (SOImm imm) =>
      let opc : byte := Byte.repr (match bop with
                                | BPF_ADD  => 0x07
                                | BPF_SUB  => 0x17
                                | BPF_MUL  => 0x27
                                | BPF_DIV  => 0x37
                                | BPF_OR   => 0x47
                                | BPF_AND  => 0x57
                                | BPF_LSH  => 0x67
                                | BPF_RSH  => 0x77
                                | BPF_MOD  => 0x97
                                | BPF_XOR  => 0xa7
                                | BPF_MOV  => 0xb7
                                | BPF_ARSH => 0xc7
                                end) in
      let dst_i : nat := bpf_ireg_to_nat dst in
      [binary_to_int64 opc dst_i 0 (Int16.repr 0%Z) imm]
  | BPF_ALU64 bop dst (SOReg src) =>
      let opc : byte := Byte.repr (match bop with
                                | BPF_ADD  => 0x0f
                                | BPF_SUB  => 0x1f
                                | BPF_MUL  => 0x2f
                                | BPF_DIV  => 0x3f
                                | BPF_OR   => 0x4f
                                | BPF_AND  => 0x5f
                                | BPF_LSH  => 0x6f
                                | BPF_RSH  => 0x7f
                                | BPF_MOD  => 0x9f
                                | BPF_XOR  => 0xaf
                                | BPF_MOV  => 0xbf
                                | BPF_ARSH => 0xcf
                                end) in
      let dst_i : nat := bpf_ireg_to_nat dst in
      let src_i : nat := bpf_ireg_to_nat src in
      [binary_to_int64 opc dst_i src_i (Int16.repr 0%Z) (Int.repr 0%Z)]

  | BPF_NEG64_REG dst =>
      let opc : byte := Byte.repr 0x87%Z in
      let dst_i : nat := bpf_ireg_to_nat dst in
      [binary_to_int64 opc dst_i 0 (Int16.repr 0%Z) (Int.repr 0%Z)]

  | BPF_HOR64_IMM dst imm =>
      let opc : byte := Byte.repr 0xf7%Z in
      let dst_i : nat := bpf_ireg_to_nat dst in
      [binary_to_int64 opc dst_i 0 (Int16.repr 0%Z) imm]

  | BPF_PQR pop dst (SOImm imm) =>
      let opc : byte := Byte.repr (match pop with
                                | BPF_LMUL => 0x86
                                | BPF_UDIV => 0x46
                                | BPF_UREM => 0x66
                                | BPF_SDIV => 0xc6
                                | BPF_SREM => 0xe6
                                end) in
      let dst_i : nat := bpf_ireg_to_nat dst in
      [binary_to_int64 opc dst_i 0 (Int16.repr 0%Z) imm]
  | BPF_PQR pop dst (SOReg src) =>
      let opc : byte := Byte.repr (match pop with
                                | BPF_LMUL => 0x8e
                                | BPF_UDIV => 0x4e
                                | BPF_UREM => 0x6e
                                | BPF_SDIV => 0xce
                                | BPF_SREM => 0xee
                                end) in
      let dst_i : nat := bpf_ireg_to_nat dst in
      let src_i : nat := bpf_ireg_to_nat src in
      [binary_to_int64 opc dst_i src_i (Int16.repr 0%Z) (Int.repr 0%Z)]
  | BPF_PQR64 pop dst (SOImm imm) =>
      let opc : byte := Byte.repr (match pop with
                                | BPF_LMUL => 0x96
                                | BPF_UDIV => 0x56
                                | BPF_UREM => 0x76
                                | BPF_SDIV => 0xd6
                                | BPF_SREM => 0xf6
                                end) in
      let dst_i : nat := bpf_ireg_to_nat dst in
      [binary_to_int64 opc dst_i 0 (Int16.repr 0%Z) imm]
  | BPF_PQR64 pop dst (SOReg src) =>
      let opc : byte := Byte.repr (match pop with
                                | BPF_LMUL => 0x9e
                                | BPF_UDIV => 0x5e
                                | BPF_UREM => 0x7e
                                | BPF_SDIV => 0xde
                                | BPF_SREM => 0xfe
                                end) in
      let dst_i : nat := bpf_ireg_to_nat dst in
      let src_i : nat := bpf_ireg_to_nat src in
      [binary_to_int64 opc dst_i src_i (Int16.repr 0%Z) (Int.repr 0%Z)]
  | BPF_PQR2 pop2 dst (SOImm imm) =>
      let opc : byte := Byte.repr (match pop2 with
                                | BPF_UHMUL => 0x36
                                | BPF_SHMUL => 0xb6
                                end) in
      let dst_i : nat := bpf_ireg_to_nat dst in
      [binary_to_int64 opc dst_i 0 (Int16.repr 0%Z) imm]
  | BPF_PQR2 pop2 dst (SOReg src) =>
      let opc : byte := Byte.repr (match pop2 with
                                | BPF_UHMUL => 0x3e
                                | BPF_SHMUL => 0xbe
                                end) in
      let dst_i : nat := bpf_ireg_to_nat dst in
      let src_i : nat := bpf_ireg_to_nat src in
      [binary_to_int64 opc dst_i src_i (Int16.repr 0%Z) (Int.repr 0%Z)]

  | BPF_JA off =>
      let opc : byte := Byte.repr 0x05%Z in
      [binary_to_int64 opc 0 0 off (Int.repr 0%Z)]

  | BPF_JUMP cond dst (SOImm imm) off =>
      let opc : byte := Byte.repr (match cond with
                                | Eq  => 0x15
                                | Gt  => 0x25
                                | Ge  => 0x35
                                | Lt  => 0xa5
                                | Le  => 0xb5
                                | SEt => 0x45
                                | Ne  => 0x55
                                | SGt => 0x65
                                | SGe => 0x75
                                | SLt => 0xc5
                                | SLe => 0xd5
                                end) in
      let dst_i : nat := bpf_ireg_to_nat dst in
      [binary_to_int64 opc dst_i 0 off imm]
  | BPF_JUMP cond dst (SOReg src) off =>
      let opc : byte := Byte.repr (match cond with
                                | Eq  => 0x1d
                                | Gt  => 0x2d
                                | Ge  => 0x3d
                                | Lt  => 0xad
                                | Le  => 0xbd
                                | SEt => 0x4d
                                | Ne  => 0x5d
                                | SGt => 0x6d
                                | SGe => 0x7d
                                | SLt => 0xcd
                                | SLe => 0xdd
                                end) in
      let dst_i : nat := bpf_ireg_to_nat dst in
      let src_i : nat := bpf_ireg_to_nat src in
      [binary_to_int64 opc dst_i src_i off (Int.repr 0%Z)]

  | BPF_CALL_REG src imm =>
      let opc : byte := Byte.repr 0x8d%Z in
      let src_i : nat := bpf_ireg_to_nat src in
      [binary_to_int64 opc 0 src_i (Int16.repr 0%Z) imm ]
  | BPF_CALL_IMM src imm =>
      let opc : byte := Byte.repr 0x85%Z in
      let src_i : nat := bpf_ireg_to_nat src in
      [binary_to_int64 opc 0 src_i (Int16.repr 0%Z) imm ]
  
  | BPF_EXIT =>
      let opc : byte := Byte.repr 0x95%Z in
      [binary_to_int64 opc 0 0 (Int16.repr 0%Z) (Int.repr 0%Z) ]
  end.


Fixpoint list_in_list {A: Type} (eqA: A -> A -> bool) (l0: list A) (pc: nat) (l: list A) : bool :=
  match l0 with
  | [] => true
  | hd0 :: tl0 =>
    match List.nth_error l pc with
    | None => false
    | Some hd =>
      andb (@eqA hd0 hd) (list_in_list eqA tl0 (S pc) l)
    end
  end.