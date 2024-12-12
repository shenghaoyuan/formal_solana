From Coq Require Import ZArith List.
From compcert.lib Require Import Integers Maps.
From compcert.common Require Import Memory AST.
From bpf.model Require Import ebpf rBPFCommType rBPFSyntax.


Definition decode_bpf (ins: u64) (from size: nat): u64 :=
  Int64.unsigned_bitfield_extract (Z.of_nat from) (Z.of_nat size) ins.

Definition rbpf_decoder_one
  (opc : u8) (dv : u4) (sv : u4) (off : i16) (imm : i32) : option bpf_instruction :=
  if Z.eqb (Byte.unsigned opc) (Z.of_nat 0x07) then
    if dv =? 11 then
      Some (BPF_ADD_STK imm)
    else 
      match u4_to_bpf_ireg dv with
      | None => None
      | Some dst => Some (BPF_ALU64 BPF_ADD dst (SOImm imm))
      end
  else
    match u4_to_bpf_ireg dv with
    | None => None
    | Some dst =>
      match u4_to_bpf_ireg sv with
      | None => None
      | Some src =>
        if Z.eqb (Byte.unsigned opc) (Z.of_nat 0x71) then
          Some (BPF_LDX Mint8unsigned dst src off)
        else if Z.eqb (Byte.unsigned opc) (Z.of_nat 0x69) then
          Some (BPF_LDX Mint16unsigned dst src off)
        else if Z.eqb (Byte.unsigned opc) (Z.of_nat 0x61) then
          Some (BPF_LDX Mint32 dst src off)
        else if Z.eqb (Byte.unsigned opc) (Z.of_nat 0x79) then
          Some (BPF_LDX Mint64 dst src off)

        else if Z.eqb (Byte.unsigned opc) (Z.of_nat 0x72) then
          Some (BPF_ST Mint8unsigned dst (SOImm imm) off)
        else if Z.eqb (Byte.unsigned opc) (Z.of_nat 0x6a) then
          Some (BPF_ST Mint16unsigned dst (SOImm imm) off)
        else if Z.eqb (Byte.unsigned opc) (Z.of_nat 0x62) then
          Some (BPF_ST Mint32 dst (SOImm imm) off)
        else if Z.eqb (Byte.unsigned opc) (Z.of_nat 0x7a) then
          Some (BPF_ST Mint64 dst (SOImm imm) off)

        else if Z.eqb (Byte.unsigned opc) (Z.of_nat 0x73) then
          Some (BPF_ST Mint8unsigned dst  (SOReg src) off)
        else if Z.eqb (Byte.unsigned opc) (Z.of_nat 0x6b) then
          Some (BPF_ST Mint16unsigned dst (SOReg src) off)
        else if Z.eqb (Byte.unsigned opc) (Z.of_nat 0x63) then
          Some (BPF_ST Mint32 dst (SOReg src) off)
        else if Z.eqb (Byte.unsigned opc) (Z.of_nat 0x7b) then
          Some (BPF_ST Mint64 dst (SOReg src) off)

        else if Z.eqb (Byte.unsigned opc) (Z.of_nat 0x04) then
          Some (BPF_ALU BPF_ADD dst (SOImm imm))
        else if Z.eqb (Byte.unsigned opc) (Z.of_nat 0x0c) then
          Some (BPF_ALU BPF_ADD dst (SOReg src))
        else if Z.eqb (Byte.unsigned opc) (Z.of_nat 0x14) then
          Some (BPF_ALU BPF_SUB dst (SOImm imm))
        else if Z.eqb (Byte.unsigned opc) (Z.of_nat 0x1c) then
          Some (BPF_ALU BPF_SUB dst (SOReg src))
        else if Z.eqb (Byte.unsigned opc) (Z.of_nat 0x24) then
          Some (BPF_ALU BPF_MUL dst (SOImm imm))
        else if Z.eqb (Byte.unsigned opc) (Z.of_nat 0x2c) then
          Some (BPF_ALU BPF_MUL dst (SOReg src))
        else if Z.eqb (Byte.unsigned opc) (Z.of_nat 0x34) then
          Some (BPF_ALU BPF_DIV dst (SOImm imm))
        else if Z.eqb (Byte.unsigned opc) (Z.of_nat 0x3c) then
          Some (BPF_ALU BPF_DIV dst (SOReg src))
        else if Z.eqb (Byte.unsigned opc) (Z.of_nat 0x44) then
          Some (BPF_ALU BPF_OR dst (SOImm imm))
        else if Z.eqb (Byte.unsigned opc) (Z.of_nat 0x4c) then
          Some (BPF_ALU BPF_OR dst (SOReg src))
        else if Z.eqb (Byte.unsigned opc) (Z.of_nat 0x54) then
          Some (BPF_ALU BPF_AND dst (SOImm imm))
        else if Z.eqb (Byte.unsigned opc) (Z.of_nat 0x5c) then
          Some (BPF_ALU BPF_AND dst (SOReg src))
        else if Z.eqb (Byte.unsigned opc) (Z.of_nat 0x64) then
          Some (BPF_ALU BPF_LSH dst (SOImm imm))
        else if Z.eqb (Byte.unsigned opc) (Z.of_nat 0x6c) then
          Some (BPF_ALU BPF_LSH dst (SOReg src))
        else if Z.eqb (Byte.unsigned opc) (Z.of_nat 0x74) then
          Some (BPF_ALU BPF_RSH dst (SOImm imm))
        else if Z.eqb (Byte.unsigned opc) (Z.of_nat 0x7c) then
          Some (BPF_ALU BPF_RSH dst (SOReg src))

        else if Z.eqb (Byte.unsigned opc) (Z.of_nat 0x84) then
          Some (BPF_NEG32_REG dst)

        else if Z.eqb (Byte.unsigned opc) (Z.of_nat 0x94) then
          Some (BPF_ALU BPF_MOD dst (SOImm imm))
        else if Z.eqb (Byte.unsigned opc) (Z.of_nat 0x9c) then
          Some (BPF_ALU BPF_MOD dst (SOReg src))
        else if Z.eqb (Byte.unsigned opc) (Z.of_nat 0xa4) then
          Some (BPF_ALU BPF_XOR dst (SOImm imm))
        else if Z.eqb (Byte.unsigned opc) (Z.of_nat 0xac) then
          Some (BPF_ALU BPF_XOR dst (SOReg src))
        else if Z.eqb (Byte.unsigned opc) (Z.of_nat 0xb4) then
          Some (BPF_ALU BPF_MOV dst (SOImm imm))
        else if Z.eqb (Byte.unsigned opc) (Z.of_nat 0xbc) then
          Some (BPF_ALU BPF_MOV dst (SOReg src))
        else if Z.eqb (Byte.unsigned opc) (Z.of_nat 0xc4) then
          Some (BPF_ALU BPF_ARSH dst (SOImm imm))
        else if Z.eqb (Byte.unsigned opc) (Z.of_nat 0xcc) then
          Some (BPF_ALU BPF_ARSH dst (SOReg src))

        else if Z.eqb (Byte.unsigned opc) (Z.of_nat 0xd4) then
          Some (BPF_LE            dst imm)
        else if Z.eqb (Byte.unsigned opc) (Z.of_nat 0xdc) then
          Some (BPF_BE            dst imm)

        else if Z.eqb (Byte.unsigned opc) (Z.of_nat 0x07) then
          Some (BPF_ALU64 BPF_ADD dst (SOImm imm))
        else if Z.eqb (Byte.unsigned opc) (Z.of_nat 0x0f) then
          Some (BPF_ALU64 BPF_ADD dst (SOReg src))
        else if Z.eqb (Byte.unsigned opc) (Z.of_nat 0x17) then
          Some (BPF_ALU64 BPF_SUB dst (SOImm imm))
        else if Z.eqb (Byte.unsigned opc) (Z.of_nat 0x1f) then
          Some (BPF_ALU64 BPF_SUB dst (SOReg src))
        else if Z.eqb (Byte.unsigned opc) (Z.of_nat 0x27) then
          Some (BPF_ALU64 BPF_MUL dst (SOImm imm))
        else if Z.eqb (Byte.unsigned opc) (Z.of_nat 0x2f) then
          Some (BPF_ALU64 BPF_MUL dst (SOReg src))
        else if Z.eqb (Byte.unsigned opc) (Z.of_nat 0x37) then
          Some (BPF_ALU64 BPF_DIV dst (SOImm imm))
        else if Z.eqb (Byte.unsigned opc) (Z.of_nat 0x3f) then
          Some (BPF_ALU64 BPF_DIV dst (SOReg src))
        else if Z.eqb (Byte.unsigned opc) (Z.of_nat 0x47) then
          Some (BPF_ALU64 BPF_OR dst (SOImm imm))
        else if Z.eqb (Byte.unsigned opc) (Z.of_nat 0x4f) then
          Some (BPF_ALU64 BPF_OR dst (SOReg src))
        else if Z.eqb (Byte.unsigned opc) (Z.of_nat 0x57) then
          Some (BPF_ALU64 BPF_AND dst (SOImm imm))
        else if Z.eqb (Byte.unsigned opc) (Z.of_nat 0x5f) then
          Some (BPF_ALU64 BPF_AND dst (SOReg src))
        else if Z.eqb (Byte.unsigned opc) (Z.of_nat 0x67) then
          Some (BPF_ALU64 BPF_LSH dst (SOImm imm))
        else if Z.eqb (Byte.unsigned opc) (Z.of_nat 0x6f) then
          Some (BPF_ALU64 BPF_LSH dst (SOReg src))
        else if Z.eqb (Byte.unsigned opc) (Z.of_nat 0x77) then
          Some (BPF_ALU64 BPF_RSH dst (SOImm imm))
        else if Z.eqb (Byte.unsigned opc) (Z.of_nat 0x7f) then
          Some (BPF_ALU64 BPF_RSH dst (SOReg src))

        else if Z.eqb (Byte.unsigned opc) (Z.of_nat 0x87) then
          Some (BPF_NEG64_REG dst)

        else if Z.eqb (Byte.unsigned opc) (Z.of_nat 0x97) then
          Some (BPF_ALU64 BPF_MOD dst (SOImm imm))
        else if Z.eqb (Byte.unsigned opc) (Z.of_nat 0x9f) then
          Some (BPF_ALU64 BPF_MOD dst (SOReg src))
        else if Z.eqb (Byte.unsigned opc) (Z.of_nat 0xa7) then
          Some (BPF_ALU64 BPF_XOR dst (SOImm imm))
        else if Z.eqb (Byte.unsigned opc) (Z.of_nat 0xaf) then
          Some (BPF_ALU64 BPF_XOR dst (SOReg src))
        else if Z.eqb (Byte.unsigned opc) (Z.of_nat 0xb7) then
          Some (BPF_ALU64 BPF_MOV dst (SOImm imm))
        else if Z.eqb (Byte.unsigned opc) (Z.of_nat 0xbf) then
          Some (BPF_ALU64 BPF_MOV dst (SOReg src))
        else if Z.eqb (Byte.unsigned opc) (Z.of_nat 0xc7) then
          Some (BPF_ALU64 BPF_ARSH dst (SOImm imm))
        else if Z.eqb (Byte.unsigned opc) (Z.of_nat 0xcf) then
          Some (BPF_ALU64 BPF_ARSH dst (SOReg src))

        else if Z.eqb (Byte.unsigned opc) (Z.of_nat 0xf7) then
          Some (BPF_HOR64_IMM     dst imm)

        else if Z.eqb (Byte.unsigned opc) (Z.of_nat 0x86) then
          Some (BPF_PQR BPF_LMUL dst (SOImm imm))
        else if Z.eqb (Byte.unsigned opc) (Z.of_nat 0x8e) then
          Some (BPF_PQR BPF_LMUL dst (SOReg src))
        else if Z.eqb (Byte.unsigned opc) (Z.of_nat 0x96) then
          Some (BPF_PQR64 BPF_LMUL dst (SOImm imm))
        else if Z.eqb (Byte.unsigned opc) (Z.of_nat 0x9e) then
          Some (BPF_PQR64 BPF_LMUL dst (SOReg src))

        else if Z.eqb (Byte.unsigned opc) (Z.of_nat 0x36) then
          Some (BPF_PQR2 BPF_UHMUL dst (SOImm imm))
        else if Z.eqb (Byte.unsigned opc) (Z.of_nat 0x3e) then
          Some (BPF_PQR2 BPF_UHMUL dst (SOReg src))
        else if Z.eqb (Byte.unsigned opc) (Z.of_nat 0xb6) then
          Some (BPF_PQR2 BPF_SHMUL dst (SOImm imm))
        else if Z.eqb (Byte.unsigned opc) (Z.of_nat 0xbe) then
          Some (BPF_PQR2 BPF_SHMUL dst (SOReg src))

        else if Z.eqb (Byte.unsigned opc) (Z.of_nat 0x46) then
          Some (BPF_PQR BPF_UDIV dst (SOImm imm))
        else if Z.eqb (Byte.unsigned opc) (Z.of_nat 0x4e) then
          Some (BPF_PQR BPF_UDIV dst (SOReg src))
        else if Z.eqb (Byte.unsigned opc) (Z.of_nat 0x56) then
          Some (BPF_PQR64 BPF_UDIV dst (SOImm imm))
        else if Z.eqb (Byte.unsigned opc) (Z.of_nat 0x5e) then
          Some (BPF_PQR64 BPF_UDIV dst (SOReg src))

        else if Z.eqb (Byte.unsigned opc) (Z.of_nat 0x66) then
          Some (BPF_PQR BPF_UREM dst (SOImm imm))
        else if Z.eqb (Byte.unsigned opc) (Z.of_nat 0x6e) then
          Some (BPF_PQR BPF_UREM dst (SOReg src))
        else if Z.eqb (Byte.unsigned opc) (Z.of_nat 0x76) then
          Some (BPF_PQR64 BPF_UREM dst (SOImm imm))
        else if Z.eqb (Byte.unsigned opc) (Z.of_nat 0x7e) then
          Some (BPF_PQR64 BPF_UREM dst (SOReg src))

        else if Z.eqb (Byte.unsigned opc) (Z.of_nat 0xc6) then
          Some (BPF_PQR BPF_SDIV dst (SOImm imm))
        else if Z.eqb (Byte.unsigned opc) (Z.of_nat 0xce) then
          Some (BPF_PQR BPF_SDIV dst (SOReg src))
        else if Z.eqb (Byte.unsigned opc) (Z.of_nat 0xd6) then
          Some (BPF_PQR64 BPF_SDIV dst (SOImm imm))
        else if Z.eqb (Byte.unsigned opc) (Z.of_nat 0xde) then
          Some (BPF_PQR64 BPF_SDIV dst (SOReg src))

        else if Z.eqb (Byte.unsigned opc) (Z.of_nat 0xe6) then
          Some (BPF_PQR BPF_SREM dst (SOImm imm))
        else if Z.eqb (Byte.unsigned opc) (Z.of_nat 0xee) then
          Some (BPF_PQR BPF_SREM dst (SOReg src))
        else if Z.eqb (Byte.unsigned opc) (Z.of_nat 0xf6) then
          Some (BPF_PQR64 BPF_SREM dst (SOImm imm))
        else if Z.eqb (Byte.unsigned opc) (Z.of_nat 0xfe) then
          Some (BPF_PQR64 BPF_SREM dst (SOReg src))

        else if Z.eqb (Byte.unsigned opc) (Z.of_nat 0x05) then
          Some (BPF_JA off)

        else if Z.eqb (Byte.unsigned opc) (Z.of_nat 0x15) then
          Some (BPF_JUMP Eq  dst (SOImm imm) off)
        else if Z.eqb (Byte.unsigned opc) (Z.of_nat 0x1d) then
          Some (BPF_JUMP Eq  dst (SOReg src) off)
        else if Z.eqb (Byte.unsigned opc) (Z.of_nat 0x25) then
          Some (BPF_JUMP Gt  dst (SOImm imm) off)
        else if Z.eqb (Byte.unsigned opc) (Z.of_nat 0x2d) then
          Some (BPF_JUMP Gt  dst (SOReg src) off)
        else if Z.eqb (Byte.unsigned opc) (Z.of_nat 0x35) then
          Some (BPF_JUMP Ge  dst (SOImm imm) off)
        else if Z.eqb (Byte.unsigned opc) (Z.of_nat 0x3d) then
          Some (BPF_JUMP Ge  dst (SOReg src) off)
        else if Z.eqb (Byte.unsigned opc) (Z.of_nat 0xa5) then
          Some (BPF_JUMP Lt  dst (SOImm imm) off)
        else if Z.eqb (Byte.unsigned opc) (Z.of_nat 0xad) then
          Some (BPF_JUMP Lt  dst (SOReg src) off)
        else if Z.eqb (Byte.unsigned opc) (Z.of_nat 0xb5) then
          Some (BPF_JUMP Le  dst (SOImm imm) off)
        else if Z.eqb (Byte.unsigned opc) (Z.of_nat 0xbd) then
          Some (BPF_JUMP Le  dst (SOReg src) off)
        else if Z.eqb (Byte.unsigned opc) (Z.of_nat 0x45) then
          Some (BPF_JUMP SEt dst (SOImm imm) off)
        else if Z.eqb (Byte.unsigned opc) (Z.of_nat 0x4d) then
          Some (BPF_JUMP SEt dst (SOReg src) off)
        else if Z.eqb (Byte.unsigned opc) (Z.of_nat 0x55) then
          Some (BPF_JUMP Ne  dst (SOImm imm) off)
        else if Z.eqb (Byte.unsigned opc) (Z.of_nat 0x5d) then
          Some (BPF_JUMP Ne  dst (SOReg src) off)
        else if Z.eqb (Byte.unsigned opc) (Z.of_nat 0x65) then
          Some (BPF_JUMP SGt dst (SOImm imm) off)
        else if Z.eqb (Byte.unsigned opc) (Z.of_nat 0x6d) then
          Some (BPF_JUMP SGt dst (SOReg src) off)
        else if Z.eqb (Byte.unsigned opc) (Z.of_nat 0x75) then
          Some (BPF_JUMP SGe dst (SOImm imm) off)
        else if Z.eqb (Byte.unsigned opc) (Z.of_nat 0x7d) then
          Some (BPF_JUMP SGe dst (SOReg src) off)
        else if Z.eqb (Byte.unsigned opc) (Z.of_nat 0xc5) then
          Some (BPF_JUMP SLt dst (SOImm imm) off)
        else if Z.eqb (Byte.unsigned opc) (Z.of_nat 0xcd) then
          Some (BPF_JUMP SLt dst (SOReg src) off)
        else if Z.eqb (Byte.unsigned opc) (Z.of_nat 0xd5) then
          Some (BPF_JUMP SLe dst (SOImm imm) off)
        else if Z.eqb (Byte.unsigned opc) (Z.of_nat 0xdd) then
          Some (BPF_JUMP SLe dst (SOReg src) off)

        else if Z.eqb (Byte.unsigned opc) (Z.of_nat 0x8d) then
          Some (BPF_CALL_REG src imm)
        else if Z.eqb (Byte.unsigned opc) (Z.of_nat 0x85) then
          Some (BPF_CALL_IMM src imm)

        else if Z.eqb (Byte.unsigned opc) (Z.of_nat 0x95) then
          Some BPF_EXIT
        else
          None
      end
    end.

Definition rbpf_decoder (pc : nat) (l : list u64) : option bpf_instruction :=
  match nth_error l pc with
  | Some data =>
      let op : u8 := Byte.repr (Int64.unsigned (decode_bpf data 0 8)) in
      let dst : u4 := Z.to_nat (Int64.unsigned (decode_bpf data 8 4)) in
      let src : u4 := Z.to_nat (Int64.unsigned (decode_bpf data 12 4)) in
      let off : i16 := Word.repr (Int64.signed (decode_bpf data 16 16)) in
      let imm : i32 := Int.repr (Int64.signed (decode_bpf data 32 32)) in
      if Z.eqb (Byte.unsigned op) (Z.of_nat 0x18) then
        match nth_error l (S pc) with
        | Some data2 =>
            let imm2 : i32 := Int.repr (Int64.signed (decode_bpf data2 32 32)) in
            match u4_to_bpf_ireg dst with
            | None => None
            | Some dst_r => Some (BPF_LD_IMM dst_r imm imm2)
            end
        | None => None
        end
      else
        rbpf_decoder_one op dst src off imm
  | _ => None
  end.