From Coq Require Import ZArith List.
From compcert.lib Require Import Integers Maps.
From compcert.common Require Import Memory AST.
From bpf.model Require Import ebpf rBPFCommType rBPFSyntax.


Definition decode_bpf (ins: int64) (from size: nat): int64 :=
  Int64.unsigned_bitfield_extract (Z.of_nat from) (Z.of_nat size) ins.

Definition rbpf_decoder_one
  (opc : byte) (dv : nat) (sv : nat) (off : int16) (imm : int) : option bpf_instruction :=
  if Z.eqb (Byte.unsigned opc) (Z.of_nat 0x07) then
    if dv =? 11 then
      Some (BPF_ADD_STK imm)
    else 
      match nat_to_bpf_ireg dv with
      | None => None
      | Some dst => Some (BPF_ALU64 BPF_ADD dst (SOImm imm))
      end
  else
    match nat_to_bpf_ireg dv with
    | None => None
    | Some dst =>
      match nat_to_bpf_ireg sv with
      | None => None
      | Some src =>
        if Z.eqb (Byte.unsigned opc) (Z.of_nat 0x71) then
          if (Int.eq imm Int.zero )%bool then
            Some (BPF_LDX M8 dst src off)
          else None
        else if Z.eqb (Byte.unsigned opc) (Z.of_nat 0x69) then
          if (Int.eq imm Int.zero )%bool then
            Some (BPF_LDX M16 dst src off)
          else None
        else if Z.eqb (Byte.unsigned opc) (Z.of_nat 0x61) then
          if (Int.eq imm Int.zero )%bool then
            Some (BPF_LDX M32 dst src off)
          else None
        else if Z.eqb (Byte.unsigned opc) (Z.of_nat 0x79) then
          if (Int.eq imm Int.zero )%bool then
            Some (BPF_LDX M64 dst src off)
          else None

        else if Z.eqb (Byte.unsigned opc) (Z.of_nat 0x72) then
          if (Nat.eqb sv 0 )%bool then
            Some (BPF_ST M8 dst (SOImm imm) off)
          else None
        else if Z.eqb (Byte.unsigned opc) (Z.of_nat 0x6a) then
          if (Nat.eqb sv 0 )%bool then
            Some (BPF_ST M16 dst (SOImm imm) off)
          else None
        else if Z.eqb (Byte.unsigned opc) (Z.of_nat 0x62) then
          if (Nat.eqb sv 0 )%bool then
            Some (BPF_ST M32 dst (SOImm imm) off)
          else None
        else if Z.eqb (Byte.unsigned opc) (Z.of_nat 0x7a) then
          if (Nat.eqb sv 0 )%bool then
            Some (BPF_ST M64 dst (SOImm imm) off)
          else None

        else if Z.eqb (Byte.unsigned opc) (Z.of_nat 0x73) then
          if (Int.eq imm Int.zero )%bool then
            Some (BPF_ST M8 dst  (SOReg src) off)
          else None
        else if Z.eqb (Byte.unsigned opc) (Z.of_nat 0x6b) then
          if (Int.eq imm Int.zero )%bool then
            Some (BPF_ST M16 dst (SOReg src) off)
          else None
        else if Z.eqb (Byte.unsigned opc) (Z.of_nat 0x63) then
          if (Int.eq imm Int.zero )%bool then
            Some (BPF_ST M32 dst (SOReg src) off)
          else None
        else if Z.eqb (Byte.unsigned opc) (Z.of_nat 0x7b) then
          if (Int.eq imm Int.zero )%bool then
            Some (BPF_ST M64 dst (SOReg src) off)
          else None

        else if Z.eqb (Byte.unsigned opc) (Z.of_nat 0x04) then
          if (Nat.eqb sv 0 && Int16.eq off Int16.zero )%bool then
            Some (BPF_ALU BPF_ADD dst (SOImm imm))
          else None
        else if Z.eqb (Byte.unsigned opc) (Z.of_nat 0x0c) then
          if (Int.eq imm Int.zero && Int16.eq off Int16.zero )%bool then
            Some (BPF_ALU BPF_ADD dst (SOReg src))
          else None
        else if Z.eqb (Byte.unsigned opc) (Z.of_nat 0x14) then
          if (Nat.eqb sv 0 && Int16.eq off Int16.zero )%bool then
            Some (BPF_ALU BPF_SUB dst (SOImm imm))
          else None
        else if Z.eqb (Byte.unsigned opc) (Z.of_nat 0x1c) then
          if (Int.eq imm Int.zero && Int16.eq off Int16.zero )%bool then
            Some (BPF_ALU BPF_SUB dst (SOReg src))
          else None
        else if Z.eqb (Byte.unsigned opc) (Z.of_nat 0x24) then
          if (Nat.eqb sv 0 && Int16.eq off Int16.zero )%bool then
            Some (BPF_ALU BPF_MUL dst (SOImm imm))
          else None
        else if Z.eqb (Byte.unsigned opc) (Z.of_nat 0x2c) then
          if (Int.eq imm Int.zero && Int16.eq off Int16.zero )%bool then
            Some (BPF_ALU BPF_MUL dst (SOReg src))
          else None
        else if Z.eqb (Byte.unsigned opc) (Z.of_nat 0x34) then
          if (Nat.eqb sv 0 && Int16.eq off Int16.zero )%bool then
            Some (BPF_ALU BPF_DIV dst (SOImm imm))
          else None
        else if Z.eqb (Byte.unsigned opc) (Z.of_nat 0x3c) then
          if (Int.eq imm Int.zero && Int16.eq off Int16.zero )%bool then
            Some (BPF_ALU BPF_DIV dst (SOReg src))
          else None
        else if Z.eqb (Byte.unsigned opc) (Z.of_nat 0x44) then
          if (Nat.eqb sv 0 && Int16.eq off Int16.zero )%bool then
            Some (BPF_ALU BPF_OR dst (SOImm imm))
          else None
        else if Z.eqb (Byte.unsigned opc) (Z.of_nat 0x4c) then
          if (Int.eq imm Int.zero && Int16.eq off Int16.zero )%bool then
            Some (BPF_ALU BPF_OR dst (SOReg src))
          else None
        else if Z.eqb (Byte.unsigned opc) (Z.of_nat 0x54) then
          if (Nat.eqb sv 0 && Int16.eq off Int16.zero )%bool then
            Some (BPF_ALU BPF_AND dst (SOImm imm))
          else None
        else if Z.eqb (Byte.unsigned opc) (Z.of_nat 0x5c) then
          if (Int.eq imm Int.zero && Int16.eq off Int16.zero )%bool then
            Some (BPF_ALU BPF_AND dst (SOReg src))
          else None
        else if Z.eqb (Byte.unsigned opc) (Z.of_nat 0x64) then
          if (Nat.eqb sv 0 && Int16.eq off Int16.zero )%bool then
            Some (BPF_ALU BPF_LSH dst (SOImm imm))
          else None
        else if Z.eqb (Byte.unsigned opc) (Z.of_nat 0x6c) then
          if (Int.eq imm Int.zero && Int16.eq off Int16.zero )%bool then
            Some (BPF_ALU BPF_LSH dst (SOReg src))
          else None
        else if Z.eqb (Byte.unsigned opc) (Z.of_nat 0x74) then
          if (Nat.eqb sv 0 && Int16.eq off Int16.zero )%bool then
            Some (BPF_ALU BPF_RSH dst (SOImm imm))
          else None
        else if Z.eqb (Byte.unsigned opc) (Z.of_nat 0x7c) then
          if (Int.eq imm Int.zero && Int16.eq off Int16.zero )%bool then
            Some (BPF_ALU BPF_RSH dst (SOReg src))
          else None

        else if Z.eqb (Byte.unsigned opc) (Z.of_nat 0x84) then
          if (Nat.eqb sv 0 && Int16.eq off Int16.zero && Int.eq imm Int.zero )%bool then
            Some (BPF_NEG32_REG dst)
          else None

        else if Z.eqb (Byte.unsigned opc) (Z.of_nat 0x94) then
          if (Nat.eqb sv 0 && Int16.eq off Int16.zero )%bool then
            Some (BPF_ALU BPF_MOD dst (SOImm imm))
          else None
        else if Z.eqb (Byte.unsigned opc) (Z.of_nat 0x9c) then
          if (Int.eq imm Int.zero && Int16.eq off Int16.zero )%bool then
            Some (BPF_ALU BPF_MOD dst (SOReg src))
          else None
        else if Z.eqb (Byte.unsigned opc) (Z.of_nat 0xa4) then
          if (Nat.eqb sv 0 && Int16.eq off Int16.zero )%bool then
            Some (BPF_ALU BPF_XOR dst (SOImm imm))
          else None
        else if Z.eqb (Byte.unsigned opc) (Z.of_nat 0xac) then
          if (Int.eq imm Int.zero && Int16.eq off Int16.zero )%bool then
            Some (BPF_ALU BPF_XOR dst (SOReg src))
          else None
        else if Z.eqb (Byte.unsigned opc) (Z.of_nat 0xb4) then
          if (Nat.eqb sv 0 && Int16.eq off Int16.zero )%bool then
            Some (BPF_ALU BPF_MOV dst (SOImm imm))
          else None
        else if Z.eqb (Byte.unsigned opc) (Z.of_nat 0xbc) then
          if (Int.eq imm Int.zero && Int16.eq off Int16.zero )%bool then
            Some (BPF_ALU BPF_MOV dst (SOReg src))
          else None
        else if Z.eqb (Byte.unsigned opc) (Z.of_nat 0xc4) then
          if (Nat.eqb sv 0 && Int16.eq off Int16.zero )%bool then
            Some (BPF_ALU BPF_ARSH dst (SOImm imm))
          else None
        else if Z.eqb (Byte.unsigned opc) (Z.of_nat 0xcc) then
          if (Int.eq imm Int.zero && Int16.eq off Int16.zero )%bool then
            Some (BPF_ALU BPF_ARSH dst (SOReg src))
          else None

        else if Z.eqb (Byte.unsigned opc) (Z.of_nat 0xd4) then
          if (Nat.eqb sv 0 && Int16.eq off Int16.zero )%bool then
            Some (BPF_LE            dst imm)
          else None
        else if Z.eqb (Byte.unsigned opc) (Z.of_nat 0xdc) then
          if (Nat.eqb sv 0 && Int16.eq off Int16.zero )%bool then
            Some (BPF_BE            dst imm)
          else None

        else if Z.eqb (Byte.unsigned opc) (Z.of_nat 0x07) then
          if (Nat.eqb sv 0 && Int16.eq off Int16.zero )%bool then
            Some (BPF_ALU64 BPF_ADD dst (SOImm imm))
          else None
        else if Z.eqb (Byte.unsigned opc) (Z.of_nat 0x0f) then
          if (Int.eq imm Int.zero && Int16.eq off Int16.zero )%bool then
            Some (BPF_ALU64 BPF_ADD dst (SOReg src))
          else None
        else if Z.eqb (Byte.unsigned opc) (Z.of_nat 0x17) then
          if (Nat.eqb sv 0 && Int16.eq off Int16.zero )%bool then
            Some (BPF_ALU64 BPF_SUB dst (SOImm imm))
          else None
        else if Z.eqb (Byte.unsigned opc) (Z.of_nat 0x1f) then
          if (Int.eq imm Int.zero && Int16.eq off Int16.zero )%bool then
            Some (BPF_ALU64 BPF_SUB dst (SOReg src))
          else None
        else if Z.eqb (Byte.unsigned opc) (Z.of_nat 0x27) then
          if (Nat.eqb sv 0 && Int16.eq off Int16.zero )%bool then
            Some (BPF_ALU64 BPF_MUL dst (SOImm imm))
          else None
        else if Z.eqb (Byte.unsigned opc) (Z.of_nat 0x2f) then
          if (Int.eq imm Int.zero && Int16.eq off Int16.zero )%bool then
            Some (BPF_ALU64 BPF_MUL dst (SOReg src))
          else None
        else if Z.eqb (Byte.unsigned opc) (Z.of_nat 0x37) then
          if (Nat.eqb sv 0 && Int16.eq off Int16.zero )%bool then
            Some (BPF_ALU64 BPF_DIV dst (SOImm imm))
          else None
        else if Z.eqb (Byte.unsigned opc) (Z.of_nat 0x3f) then
          if (Int.eq imm Int.zero && Int16.eq off Int16.zero )%bool then
            Some (BPF_ALU64 BPF_DIV dst (SOReg src))
          else None
        else if Z.eqb (Byte.unsigned opc) (Z.of_nat 0x47) then
          if (Nat.eqb sv 0 && Int16.eq off Int16.zero )%bool then
            Some (BPF_ALU64 BPF_OR dst (SOImm imm))
          else None
        else if Z.eqb (Byte.unsigned opc) (Z.of_nat 0x4f) then
          if (Int.eq imm Int.zero && Int16.eq off Int16.zero )%bool then
            Some (BPF_ALU64 BPF_OR dst (SOReg src))
          else None
        else if Z.eqb (Byte.unsigned opc) (Z.of_nat 0x57) then
          if (Nat.eqb sv 0 && Int16.eq off Int16.zero )%bool then
            Some (BPF_ALU64 BPF_AND dst (SOImm imm))
          else None
        else if Z.eqb (Byte.unsigned opc) (Z.of_nat 0x5f) then
          if (Int.eq imm Int.zero && Int16.eq off Int16.zero )%bool then
            Some (BPF_ALU64 BPF_AND dst (SOReg src))
          else None
        else if Z.eqb (Byte.unsigned opc) (Z.of_nat 0x67) then
          if (Nat.eqb sv 0 && Int16.eq off Int16.zero )%bool then
            Some (BPF_ALU64 BPF_LSH dst (SOImm imm))
          else None
        else if Z.eqb (Byte.unsigned opc) (Z.of_nat 0x6f) then
          if (Int.eq imm Int.zero && Int16.eq off Int16.zero )%bool then
            Some (BPF_ALU64 BPF_LSH dst (SOReg src))
          else None
        else if Z.eqb (Byte.unsigned opc) (Z.of_nat 0x77) then
          if (Nat.eqb sv 0 && Int16.eq off Int16.zero )%bool then
            Some (BPF_ALU64 BPF_RSH dst (SOImm imm))
          else None
        else if Z.eqb (Byte.unsigned opc) (Z.of_nat 0x7f) then
          if (Int.eq imm Int.zero && Int16.eq off Int16.zero )%bool then
            Some (BPF_ALU64 BPF_RSH dst (SOReg src))
          else None

        else if Z.eqb (Byte.unsigned opc) (Z.of_nat 0x87) then
          if (Nat.eqb sv 0 && Int16.eq off Int16.zero && Int.eq imm Int.zero )%bool then
            Some (BPF_NEG64_REG dst)
          else None

        else if Z.eqb (Byte.unsigned opc) (Z.of_nat 0x97) then
          if (Nat.eqb sv 0 && Int16.eq off Int16.zero )%bool then
            Some (BPF_ALU64 BPF_MOD dst (SOImm imm))
          else None
        else if Z.eqb (Byte.unsigned opc) (Z.of_nat 0x9f) then
          if (Int.eq imm Int.zero && Int16.eq off Int16.zero )%bool then
            Some (BPF_ALU64 BPF_MOD dst (SOReg src))
          else None
        else if Z.eqb (Byte.unsigned opc) (Z.of_nat 0xa7) then
          if (Nat.eqb sv 0 && Int16.eq off Int16.zero )%bool then
            Some (BPF_ALU64 BPF_XOR dst (SOImm imm))
          else None
        else if Z.eqb (Byte.unsigned opc) (Z.of_nat 0xaf) then
          if (Int.eq imm Int.zero && Int16.eq off Int16.zero )%bool then
            Some (BPF_ALU64 BPF_XOR dst (SOReg src))
          else None
        else if Z.eqb (Byte.unsigned opc) (Z.of_nat 0xb7) then
          if (Nat.eqb sv 0 && Int16.eq off Int16.zero )%bool then
            Some (BPF_ALU64 BPF_MOV dst (SOImm imm))
          else None
        else if Z.eqb (Byte.unsigned opc) (Z.of_nat 0xbf) then
          if (Int.eq imm Int.zero && Int16.eq off Int16.zero )%bool then
            Some (BPF_ALU64 BPF_MOV dst (SOReg src))
          else None
        else if Z.eqb (Byte.unsigned opc) (Z.of_nat 0xc7) then
          if (Nat.eqb sv 0 && Int16.eq off Int16.zero )%bool then
            Some (BPF_ALU64 BPF_ARSH dst (SOImm imm))
          else None
        else if Z.eqb (Byte.unsigned opc) (Z.of_nat 0xcf) then
          if (Int.eq imm Int.zero && Int16.eq off Int16.zero )%bool then
            Some (BPF_ALU64 BPF_ARSH dst (SOReg src))
          else None

        else if Z.eqb (Byte.unsigned opc) (Z.of_nat 0xf7) then
          if (Nat.eqb sv 0 && Int16.eq off Int16.zero )%bool then
            Some (BPF_HOR64_IMM     dst imm)
          else None

        else if Z.eqb (Byte.unsigned opc) (Z.of_nat 0x86) then
          if (Nat.eqb sv 0 && Int16.eq off Int16.zero )%bool then
            Some (BPF_PQR BPF_LMUL dst (SOImm imm))
          else None
        else if Z.eqb (Byte.unsigned opc) (Z.of_nat 0x8e) then
          if (Int.eq imm Int.zero && Int16.eq off Int16.zero )%bool then
            Some (BPF_PQR BPF_LMUL dst (SOReg src))
          else None
        else if Z.eqb (Byte.unsigned opc) (Z.of_nat 0x96) then
          if (Nat.eqb sv 0 && Int16.eq off Int16.zero )%bool then
            Some (BPF_PQR64 BPF_LMUL dst (SOImm imm))
          else None
        else if Z.eqb (Byte.unsigned opc) (Z.of_nat 0x9e) then
          if (Int.eq imm Int.zero && Int16.eq off Int16.zero )%bool then
            Some (BPF_PQR64 BPF_LMUL dst (SOReg src))
          else None

        else if Z.eqb (Byte.unsigned opc) (Z.of_nat 0x36) then
          if (Nat.eqb sv 0 && Int16.eq off Int16.zero )%bool then
            Some (BPF_PQR2 BPF_UHMUL dst (SOImm imm))
          else None
        else if Z.eqb (Byte.unsigned opc) (Z.of_nat 0x3e) then
          if (Int.eq imm Int.zero && Int16.eq off Int16.zero )%bool then
            Some (BPF_PQR2 BPF_UHMUL dst (SOReg src))
          else None
        else if Z.eqb (Byte.unsigned opc) (Z.of_nat 0xb6) then
          if (Nat.eqb sv 0 && Int16.eq off Int16.zero )%bool then
            Some (BPF_PQR2 BPF_SHMUL dst (SOImm imm))
          else None
        else if Z.eqb (Byte.unsigned opc) (Z.of_nat 0xbe) then
          if (Int.eq imm Int.zero && Int16.eq off Int16.zero )%bool then
            Some (BPF_PQR2 BPF_SHMUL dst (SOReg src))
          else None

        else if Z.eqb (Byte.unsigned opc) (Z.of_nat 0x46) then
          if (Nat.eqb sv 0 && Int16.eq off Int16.zero )%bool then
            Some (BPF_PQR BPF_UDIV dst (SOImm imm))
          else None
        else if Z.eqb (Byte.unsigned opc) (Z.of_nat 0x4e) then
          if (Int.eq imm Int.zero && Int16.eq off Int16.zero )%bool then
            Some (BPF_PQR BPF_UDIV dst (SOReg src))
          else None
        else if Z.eqb (Byte.unsigned opc) (Z.of_nat 0x56) then
          if (Nat.eqb sv 0 && Int16.eq off Int16.zero )%bool then
            Some (BPF_PQR64 BPF_UDIV dst (SOImm imm))
          else None
        else if Z.eqb (Byte.unsigned opc) (Z.of_nat 0x5e) then
          if (Int.eq imm Int.zero && Int16.eq off Int16.zero )%bool then
            Some (BPF_PQR64 BPF_UDIV dst (SOReg src))
          else None

        else if Z.eqb (Byte.unsigned opc) (Z.of_nat 0x66) then
          if (Nat.eqb sv 0 && Int16.eq off Int16.zero )%bool then
            Some (BPF_PQR BPF_UREM dst (SOImm imm))
          else None
        else if Z.eqb (Byte.unsigned opc) (Z.of_nat 0x6e) then
          if (Int.eq imm Int.zero && Int16.eq off Int16.zero )%bool then
            Some (BPF_PQR BPF_UREM dst (SOReg src))
          else None
        else if Z.eqb (Byte.unsigned opc) (Z.of_nat 0x76) then
          if (Nat.eqb sv 0 && Int16.eq off Int16.zero )%bool then
            Some (BPF_PQR64 BPF_UREM dst (SOImm imm))
          else None
        else if Z.eqb (Byte.unsigned opc) (Z.of_nat 0x7e) then
          if (Int.eq imm Int.zero && Int16.eq off Int16.zero )%bool then
            Some (BPF_PQR64 BPF_UREM dst (SOReg src))
          else None

        else if Z.eqb (Byte.unsigned opc) (Z.of_nat 0xc6) then
          if (Nat.eqb sv 0 && Int16.eq off Int16.zero )%bool then
            Some (BPF_PQR BPF_SDIV dst (SOImm imm))
          else None
        else if Z.eqb (Byte.unsigned opc) (Z.of_nat 0xce) then
          if (Int.eq imm Int.zero && Int16.eq off Int16.zero )%bool then
            Some (BPF_PQR BPF_SDIV dst (SOReg src))
          else None
        else if Z.eqb (Byte.unsigned opc) (Z.of_nat 0xd6) then
          if (Nat.eqb sv 0 && Int16.eq off Int16.zero )%bool then
            Some (BPF_PQR64 BPF_SDIV dst (SOImm imm))
          else None
        else if Z.eqb (Byte.unsigned opc) (Z.of_nat 0xde) then
          if (Int.eq imm Int.zero && Int16.eq off Int16.zero )%bool then
            Some (BPF_PQR64 BPF_SDIV dst (SOReg src))
          else None

        else if Z.eqb (Byte.unsigned opc) (Z.of_nat 0xe6) then
          if (Nat.eqb sv 0 && Int16.eq off Int16.zero )%bool then
            Some (BPF_PQR BPF_SREM dst (SOImm imm))
          else None
        else if Z.eqb (Byte.unsigned opc) (Z.of_nat 0xee) then
          if (Int.eq imm Int.zero && Int16.eq off Int16.zero )%bool then
            Some (BPF_PQR BPF_SREM dst (SOReg src))
          else None
        else if Z.eqb (Byte.unsigned opc) (Z.of_nat 0xf6) then
          if (Nat.eqb sv 0 && Int16.eq off Int16.zero )%bool then
            Some (BPF_PQR64 BPF_SREM dst (SOImm imm))
          else None
        else if Z.eqb (Byte.unsigned opc) (Z.of_nat 0xfe) then
          if (Int.eq imm Int.zero && Int16.eq off Int16.zero )%bool then
            Some (BPF_PQR64 BPF_SREM dst (SOReg src))
          else None

        else if Z.eqb (Byte.unsigned opc) (Z.of_nat 0x05) then
          if (Nat.eqb sv 0 && Nat.eqb dv 0 )%bool then
            Some (BPF_JA off)
          else None

        else if Z.eqb (Byte.unsigned opc) (Z.of_nat 0x15) then
          if (Nat.eqb sv 0 )%bool then
            Some (BPF_JUMP Eq  dst (SOImm imm) off)
          else None
        else if Z.eqb (Byte.unsigned opc) (Z.of_nat 0x1d) then
          if (Int.eq imm Int.zero )%bool then
            Some (BPF_JUMP Eq  dst (SOReg src) off)
          else None
        else if Z.eqb (Byte.unsigned opc) (Z.of_nat 0x25) then
          if (Nat.eqb sv 0 )%bool then
            Some (BPF_JUMP Gt  dst (SOImm imm) off)
          else None
        else if Z.eqb (Byte.unsigned opc) (Z.of_nat 0x2d) then
          if (Int.eq imm Int.zero )%bool then
            Some (BPF_JUMP Gt  dst (SOReg src) off)
          else None
        else if Z.eqb (Byte.unsigned opc) (Z.of_nat 0x35) then
          if (Nat.eqb sv 0 )%bool then
            Some (BPF_JUMP Ge  dst (SOImm imm) off)
          else None
        else if Z.eqb (Byte.unsigned opc) (Z.of_nat 0x3d) then
          if (Int.eq imm Int.zero )%bool then
            Some (BPF_JUMP Ge  dst (SOReg src) off)
          else None
        else if Z.eqb (Byte.unsigned opc) (Z.of_nat 0xa5) then
          if (Nat.eqb sv 0 )%bool then
            Some (BPF_JUMP Lt  dst (SOImm imm) off)
          else None
        else if Z.eqb (Byte.unsigned opc) (Z.of_nat 0xad) then
          if (Int.eq imm Int.zero )%bool then
            Some (BPF_JUMP Lt  dst (SOReg src) off)
          else None
        else if Z.eqb (Byte.unsigned opc) (Z.of_nat 0xb5) then
          if (Nat.eqb sv 0 )%bool then
            Some (BPF_JUMP Le  dst (SOImm imm) off)
          else None
        else if Z.eqb (Byte.unsigned opc) (Z.of_nat 0xbd) then
          if (Int.eq imm Int.zero )%bool then
            Some (BPF_JUMP Le  dst (SOReg src) off)
          else None
        else if Z.eqb (Byte.unsigned opc) (Z.of_nat 0x45) then
          if (Nat.eqb sv 0 )%bool then
            Some (BPF_JUMP SEt dst (SOImm imm) off)
          else None
        else if Z.eqb (Byte.unsigned opc) (Z.of_nat 0x4d) then
          if (Int.eq imm Int.zero )%bool then
            Some (BPF_JUMP SEt dst (SOReg src) off)
          else None
        else if Z.eqb (Byte.unsigned opc) (Z.of_nat 0x55) then
          if (Nat.eqb sv 0 )%bool then
            Some (BPF_JUMP Ne  dst (SOImm imm) off)
          else None
        else if Z.eqb (Byte.unsigned opc) (Z.of_nat 0x5d) then
          if (Int.eq imm Int.zero )%bool then
            Some (BPF_JUMP Ne  dst (SOReg src) off)
          else None
        else if Z.eqb (Byte.unsigned opc) (Z.of_nat 0x65) then
          if (Nat.eqb sv 0 )%bool then
            Some (BPF_JUMP SGt dst (SOImm imm) off)
          else None
        else if Z.eqb (Byte.unsigned opc) (Z.of_nat 0x6d) then
          if (Int.eq imm Int.zero )%bool then
            Some (BPF_JUMP SGt dst (SOReg src) off)
          else None
        else if Z.eqb (Byte.unsigned opc) (Z.of_nat 0x75) then
          if (Nat.eqb sv 0 )%bool then
            Some (BPF_JUMP SGe dst (SOImm imm) off)
          else None
        else if Z.eqb (Byte.unsigned opc) (Z.of_nat 0x7d) then
          if (Int.eq imm Int.zero )%bool then
            Some (BPF_JUMP SGe dst (SOReg src) off)
          else None
        else if Z.eqb (Byte.unsigned opc) (Z.of_nat 0xc5) then
          if (Nat.eqb sv 0 )%bool then
            Some (BPF_JUMP SLt dst (SOImm imm) off)
          else None
        else if Z.eqb (Byte.unsigned opc) (Z.of_nat 0xcd) then
          if (Int.eq imm Int.zero )%bool then
            Some (BPF_JUMP SLt dst (SOReg src) off)
          else None
        else if Z.eqb (Byte.unsigned opc) (Z.of_nat 0xd5) then
          if (Nat.eqb sv 0 )%bool then
            Some (BPF_JUMP SLe dst (SOImm imm) off)
          else None
        else if Z.eqb (Byte.unsigned opc) (Z.of_nat 0xdd) then
          if (Int.eq imm Int.zero )%bool then
            Some (BPF_JUMP SLe dst (SOReg src) off)
          else None

        else if Z.eqb (Byte.unsigned opc) (Z.of_nat 0x8d) then
          if (Nat.eqb dv 0 && Int16.eq off Int16.zero )%bool then
            Some (BPF_CALL_REG src imm)
          else None
        else if Z.eqb (Byte.unsigned opc) (Z.of_nat 0x85) then
          if (Nat.eqb dv 0 && Int16.eq off Int16.zero )%bool then
            Some (BPF_CALL_IMM src imm)
          else None

        else if Z.eqb (Byte.unsigned opc) (Z.of_nat 0x95) then
          if (Nat.eqb sv 0 && Int16.eq off Int16.zero && Nat.eqb dv 0 && Int.eq imm Int.zero )%bool then
            Some BPF_EXIT
          else None
        else
          None
      end
    end.

Definition rbpf_decoder (pc : nat) (l : list int64) : option bpf_instruction :=
  match nth_error l pc with
  | Some data =>
      let op  := Byte.repr (Int64.unsigned (decode_bpf data 0 8)) in
      let dst := Z.to_nat (Int64.unsigned (decode_bpf data 8 4)) in
      let src := Z.to_nat (Int64.unsigned (decode_bpf data 12 4)) in
      let off := Int16.repr (Int64.signed (decode_bpf data 16 16)) in
      let imm := Int.repr (Int64.signed (decode_bpf data 32 32)) in
      if Z.eqb (Byte.unsigned op) 0x18%Z then
        match nth_error l (S pc) with
        | Some data2 =>
            let op2  := Byte.repr (Int64.unsigned (decode_bpf data2 0 8)) in
            let dst2 := Z.to_nat (Int64.unsigned (decode_bpf data2 8 4)) in
            let src2 := Z.to_nat (Int64.unsigned (decode_bpf data2 12 4)) in
            let off2 := Int16.repr (Int64.signed (decode_bpf data2 16 16)) in
            let imm2 := Int.repr (Int64.signed (decode_bpf data2 32 32)) in
            match nat_to_bpf_ireg dst with
            | None => None
            | Some dst_r =>
              if (Nat.eqb src 0 && Int16.eq off (Int16.repr 0) &&
                 Byte.eq op2 (Byte.repr 0) && Nat.eqb dst2 0 && Nat.eqb src2 0 &&
                 Int16.eq off2 (Int16.repr 0))%bool then
                Some (BPF_LD_IMM dst_r imm imm2)
              else
                None
            end
        | None => None
        end
      else
        rbpf_decoder_one op dst src off imm
  | _ => None
  end.