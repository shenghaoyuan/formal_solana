From Coq Require Import ZArith List.
From compcert.lib Require Import Integers Maps.
From compcert.common Require Import AST.

From bpf Require Import rBPFCommType rBPFSyntax.


(*   basic instruction check   *)
Definition insn (opc : u8) (dst : u4) (src : u4) (off : i16) (imm : i32) : option ebpf_binary :=
  if  orb (Nat.ltb 10 dst) (Nat.ltb 10 src) then
    None
  else
    Some {|
      bpf_opc := opc;
      bpf_dst := dst;
      bpf_src := src;
      bpf_off := off;
      bpf_imm := imm
    |}
  .

(*   get instruction opcode   *)
Definition ldx_chunk2opcode (m : memory_chunk) : u8 :=
  match m with
  | Mint8unsigned  => Byte.repr 0x71%Z
  | Mint16unsigned => Byte.repr 0x69%Z
  | Mint32         => Byte.repr 0x61%Z
  | Mint64         => Byte.repr 0x79%Z
  | _              => Byte.repr 0%Z
  end.

Definition st_chunk2opcode_imm (m : memory_chunk) : u8 :=
  match m with
  | Mint8unsigned  => Byte.repr 0x72%Z
  | Mint16unsigned => Byte.repr 0x6a%Z
  | Mint32         => Byte.repr 0x62%Z
  | Mint64         => Byte.repr 0x7a%Z
  | _              => Byte.repr 0%Z
  end.

Definition st_chunk2opcode_reg (m : memory_chunk) : u8 :=
  match m with
  | Mint8unsigned  => Byte.repr 0x73%Z
  | Mint16unsigned => Byte.repr 0x6b%Z
  | Mint32         => Byte.repr 0x63%Z
  | Mint64         => Byte.repr 0x7b%Z
  | _              => Byte.repr 0%Z
  end.

Definition alu2opcode_imm (bop : binop) : u8 :=
  match bop with
  | BPF_ADD  => Byte.repr 0x04%Z
  | BPF_SUB  => Byte.repr 0x14%Z
  | BPF_MUL  => Byte.repr 0x24%Z
  | BPF_DIV  => Byte.repr 0x34%Z
  | BPF_OR   => Byte.repr 0x44%Z
  | BPF_AND  => Byte.repr 0x54%Z
  | BPF_LSH  => Byte.repr 0x64%Z
  | BPF_RSH  => Byte.repr 0x74%Z
  | BPF_MOD  => Byte.repr 0x94%Z
  | BPF_XOR  => Byte.repr 0xa4%Z
  | BPF_MOV  => Byte.repr 0xb4%Z
  | BPF_ARSH => Byte.repr 0xc4%Z
  end.

Definition alu2opcode_reg (bop : binop) : u8 :=
  match bop with
  | BPF_ADD  => Byte.repr 0x0c%Z
  | BPF_SUB  => Byte.repr 0x1c%Z
  | BPF_MUL  => Byte.repr 0x2c%Z
  | BPF_DIV  => Byte.repr 0x3c%Z
  | BPF_OR   => Byte.repr 0x4c%Z
  | BPF_AND  => Byte.repr 0x5c%Z
  | BPF_LSH  => Byte.repr 0x6c%Z
  | BPF_RSH  => Byte.repr 0x7c%Z
  | BPF_MOD  => Byte.repr 0x9c%Z
  | BPF_XOR  => Byte.repr 0xac%Z
  | BPF_MOV  => Byte.repr 0xbc%Z
  | BPF_ARSH => Byte.repr 0xcc%Z
  end.

Definition alu642opcode_imm (bop : binop) : u8 :=
  match bop with
  | BPF_ADD  => Byte.repr 0x07%Z
  | BPF_SUB  => Byte.repr 0x17%Z
  | BPF_MUL  => Byte.repr 0x27%Z
  | BPF_DIV  => Byte.repr 0x37%Z
  | BPF_OR   => Byte.repr 0x47%Z
  | BPF_AND  => Byte.repr 0x57%Z
  | BPF_LSH  => Byte.repr 0x67%Z
  | BPF_RSH  => Byte.repr 0x77%Z
  | BPF_MOD  => Byte.repr 0x97%Z
  | BPF_XOR  => Byte.repr 0xa7%Z
  | BPF_MOV  => Byte.repr 0xb7%Z
  | BPF_ARSH => Byte.repr 0xc7%Z
  end.

Definition alu642opcode_reg (bop : binop) : u8 :=
  match bop with
  | BPF_ADD  => Byte.repr 0x0f%Z
  | BPF_SUB  => Byte.repr 0x1f%Z
  | BPF_MUL  => Byte.repr 0x2f%Z
  | BPF_DIV  => Byte.repr 0x3f%Z
  | BPF_OR   => Byte.repr 0x4f%Z
  | BPF_AND  => Byte.repr 0x5f%Z
  | BPF_LSH  => Byte.repr 0x6f%Z
  | BPF_RSH  => Byte.repr 0x7f%Z
  | BPF_MOD  => Byte.repr 0x9f%Z
  | BPF_XOR  => Byte.repr 0xaf%Z
  | BPF_MOV  => Byte.repr 0xbf%Z
  | BPF_ARSH => Byte.repr 0xcf%Z
  end.

Definition pqr2opcode_imm (pop : pqrop) : u8 :=
  match pop with
  | BPF_LMUL => Byte.repr 0x86%Z
  | BPF_UDIV => Byte.repr 0x46%Z
  | BPF_UREM => Byte.repr 0x66%Z
  | BPF_SDIV => Byte.repr 0xc6%Z
  | BPF_SREM => Byte.repr 0xe6%Z
  end.

Definition pqr2opcode_reg (pop : pqrop) : u8 :=
  match pop with
  | BPF_LMUL => Byte.repr 0x8e%Z
  | BPF_UDIV => Byte.repr 0x4e%Z
  | BPF_UREM => Byte.repr 0x6e%Z
  | BPF_SDIV => Byte.repr 0xce%Z
  | BPF_SREM => Byte.repr 0xee%Z
  end.

Definition pqr642opcode_imm (pop : pqrop) : u8 :=
  match pop with
  | BPF_LMUL => Byte.repr 0x96%Z
  | BPF_UDIV => Byte.repr 0x56%Z
  | BPF_UREM => Byte.repr 0x76%Z
  | BPF_SDIV => Byte.repr 0xd6%Z
  | BPF_SREM => Byte.repr 0xf6%Z
  end.

Definition pqr642opcode_reg (pop : pqrop) : u8 :=
  match pop with
  | BPF_LMUL => Byte.repr 0x9e%Z
  | BPF_UDIV => Byte.repr 0x5e%Z
  | BPF_UREM => Byte.repr 0x7e%Z
  | BPF_SDIV => Byte.repr 0xde%Z
  | BPF_SREM => Byte.repr 0xfe%Z
  end.

Definition pqr22opcode_imm (pop2 : pqrop2) : u8 :=
  match pop2 with
  | BPF_UHMUL => Byte.repr 0x36%Z
  | BPF_SHMUL => Byte.repr 0xb6%Z
  end.

Definition pqr22opcode_reg (pop2 : pqrop2) : u8 :=
  match pop2 with
  | BPF_UHMUL => Byte.repr 0x3e%Z
  | BPF_SHMUL => Byte.repr 0xbe%Z
  end.

Definition condition2opcode_imm (c : condition) : u8 :=
  match c with
  | Eq  => Byte.repr 0x15%Z
  | Gt  => Byte.repr 0x25%Z
  | Ge  => Byte.repr 0x35%Z
  | Lt  => Byte.repr 0xa5%Z
  | Le  => Byte.repr 0xb5%Z
  | SEt => Byte.repr 0x45%Z
  | Ne  => Byte.repr 0x55%Z
  | SGt => Byte.repr 0x65%Z
  | SGe => Byte.repr 0x75%Z
  | SLt => Byte.repr 0xc5%Z
  | SLe => Byte.repr 0xd5%Z
  end.

Definition condition2opcode_reg (c : condition) : u8 :=
  match c with
  | Eq  => Byte.repr 0x1d%Z
  | Gt  => Byte.repr 0x2d%Z
  | Ge  => Byte.repr 0x3d%Z
  | Lt  => Byte.repr 0xad%Z
  | Le  => Byte.repr 0xbd%Z
  | SEt => Byte.repr 0x4d%Z
  | Ne  => Byte.repr 0x5d%Z
  | SGt => Byte.repr 0x6d%Z
  | SGe => Byte.repr 0x7d%Z
  | SLt => Byte.repr 0xcd%Z
  | SLe => Byte.repr 0xdd%Z
  end.

(*   assemble one instruction    *)
Definition assemble_one_instruction (bi : bpf_instruction) : option ebpf_binary :=
  match bi with
  | BPF_LD_IMM dst i1 i2 => insn (Byte.repr 0x18%Z) (bpf_ireg_to_u4 dst) 0 (Word.repr 0%Z) i1
  | BPF_LDX ck dst src off => insn (ldx_chunk2opcode ck) (bpf_ireg_to_u4 dst) (bpf_ireg_to_u4 src) off (Int.repr 0%Z)
  | BPF_ST ck dst (SOReg ir) off => insn (st_chunk2opcode_reg ck) (bpf_ireg_to_u4 dst) (bpf_ireg_to_u4 ir) off (Int.repr 0%Z)
  | BPF_ST ck dst (SOImm im) off => insn (st_chunk2opcode_imm ck) (bpf_ireg_to_u4 dst) 0 off im

  | BPF_NEG32_REG dst => insn (Byte.repr 0x84%Z) (bpf_ireg_to_u4 dst) 0 (Word.repr 0%Z) (Int.repr 0%Z)
  | BPF_NEG64_REG dst => insn (Byte.repr 0x87%Z) (bpf_ireg_to_u4 dst) 0 (Word.repr 0%Z) (Int.repr 0%Z)

  | BPF_ALU bop dst (SOReg ir) => insn (alu2opcode_reg bop) (bpf_ireg_to_u4 dst) (bpf_ireg_to_u4 ir) (Word.repr 0%Z) (Int.repr 0%Z)
  | BPF_ALU bop dst (SOImm im) => insn (alu2opcode_imm bop) (bpf_ireg_to_u4 dst) 0 (Word.repr 0%Z) im
  | BPF_LE dst imm => insn (Byte.repr 0xd4%Z) (bpf_ireg_to_u4 dst) 0 (Word.repr 0%Z) imm
  | BPF_BE dst imm => insn (Byte.repr 0xdc%Z) (bpf_ireg_to_u4 dst) 0 (Word.repr 0%Z) imm

  | BPF_PQR pop dst (SOReg ir) => insn (pqr2opcode_reg pop) (bpf_ireg_to_u4 dst) (bpf_ireg_to_u4 ir) (Word.repr 0%Z) (Int.repr 0%Z)
  | BPF_PQR pop dst (SOImm im) => insn (pqr2opcode_imm pop) (bpf_ireg_to_u4 dst) 0 (Word.repr 0%Z) im
  | BPF_PQR64 pop dst (SOReg ir) => insn (pqr642opcode_reg pop) (bpf_ireg_to_u4 dst) (bpf_ireg_to_u4 ir) (Word.repr 0%Z) (Int.repr 0%Z)
  | BPF_PQR64 pop dst (SOImm im) => insn (pqr642opcode_imm pop) (bpf_ireg_to_u4 dst) 0 (Word.repr 0%Z) im
  | BPF_PQR2 pop dst (SOReg ir) => insn (pqr22opcode_reg pop) (bpf_ireg_to_u4 dst) (bpf_ireg_to_u4 ir) (Word.repr 0%Z) (Int.repr 0%Z)
  | BPF_PQR2 pop dst (SOImm im) => insn (pqr22opcode_imm pop) (bpf_ireg_to_u4 dst) 0 (Word.repr 0%Z) im

  | BPF_JA off => insn (Byte.repr 0x05%Z) 0 0 off (Int.repr 0%Z)
  | BPF_JUMP cop dst (SOReg ir) off => insn (condition2opcode_reg cop) (bpf_ireg_to_u4 dst) (bpf_ireg_to_u4 ir) off (Int.repr 0%Z)
  | BPF_JUMP cop dst (SOImm im) off => insn (condition2opcode_imm cop) (bpf_ireg_to_u4 dst) 0 off im

  | BPF_CALL_REG src imm => insn (Byte.repr 0x8d%Z) 0 (bpf_ireg_to_u4 src) (Word.repr 0%Z) imm
  | BPF_CALL_IMM src imm => insn (Byte.repr 0x85%Z) 0 (bpf_ireg_to_u4 src) (Word.repr 0%Z) imm

  | BPF_EXIT => insn (Byte.repr 0x95%Z) 0 0 (Word.repr 0%Z) (Int.repr 0%Z)
  | _ => None
  end.

(*    assemble a set of instruction    *)
Fixpoint assemble (asm : ebpf_asm) : option ebpf_abin :=
  match asm with
  | nil => Some nil
  | h :: t =>
      match assemble_one_instruction h with
      | None => None
      | Some h_i =>
          match assemble t with
          | None => None
          | Some tl_i =>
              match h with
              | BPF_LD_IMM dst i1 i2 =>
                  match insn (Byte.repr 0%Z) 0 0 (Word.repr 0%Z) i2 with
                  | None => None 
                  | Some h_i2 => Some (h_i :: h_i2 :: tl_i)
                  end
              | _ => Some (h_i :: tl_i)
              end
          end
      end
  end.




















