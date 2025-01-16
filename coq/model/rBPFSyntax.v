From Coq Require Import List.
From compcert.lib Require Import Coqlib Integers.
From compcert.common Require Import AST.

From bpf.model Require Import rBPFCommType.

Inductive bpf_ireg : Type :=
  | BR0 : bpf_ireg
  | BR1 : bpf_ireg
  | BR2 : bpf_ireg
  | BR3 : bpf_ireg
  | BR4 : bpf_ireg
  | BR5 : bpf_ireg
  | BR6 : bpf_ireg
  | BR7 : bpf_ireg
  | BR8 : bpf_ireg
  | BR9 : bpf_ireg
  | BR10 : bpf_ireg.

(* BR Constructor and Program counter *)
Inductive bpf_preg : Type :=
  | BR : bpf_ireg -> bpf_preg
  | BPC : bpf_preg.

Definition off_ty := int16.
(*
Definition imm_ty := int.

Definition dst_ty := bpf_ireg.
Definition src_ty := bpf_ireg. *)

(* Source operator *)
Inductive snd_op : Type :=
  | SOImm : int -> snd_op
  | SOReg : bpf_ireg -> snd_op.

Inductive arch : Type :=
  | A32 : arch
  | A64 : arch.

Definition arch2int (a : arch) : Z :=
  match a with
  | A32 => 32
  | A64 => 64
  end.

Inductive condition : Type :=
  | Eq  : condition
  | Gt  : condition
  | Ge  : condition
  | Lt  : condition
  | Le  : condition
  | SEt : condition
  | Ne  : condition
  | SGt : condition
  | SGe : condition
  | SLt : condition
  | SLe : condition.

Inductive binop : Type :=
  | BPF_ADD  : binop
  | BPF_SUB  : binop
  | BPF_MUL  : binop
  | BPF_DIV  : binop
  | BPF_OR   : binop
  | BPF_AND  : binop
  | BPF_LSH  : binop
  | BPF_RSH  : binop
  | BPF_MOD  : binop
  | BPF_XOR  : binop
  | BPF_MOV  : binop
  | BPF_ARSH : binop.

Inductive pqrop : Type :=
  | BPF_LMUL  : pqrop
  | BPF_UDIV  : pqrop
  | BPF_UREM  : pqrop
  | BPF_SDIV  : pqrop
  | BPF_SREM  : pqrop.

Inductive pqrop2 : Type :=
  | BPF_UHMUL : pqrop2
  | BPF_SHMUL : pqrop2.

Inductive SBPFV : Type :=
  | V1  : SBPFV
  | V2  : SBPFV
  (* | V3 : SBPFV *) (* The future format with BTF support *)
.

Inductive MChunk := M8 | M16 | M32 | M64.

Definition memory_chunk_of_MChunk (mc : MChunk) : memory_chunk :=
  match mc with
  | M8  => Mint8unsigned
  | M16 => Mint16unsigned
  | M32 => Mint32
  | M64 => Mint64
  end.


Inductive bpf_instruction : Type :=
  | BPF_LD_IMM : bpf_ireg -> int -> int -> bpf_instruction
  | BPF_LDX : MChunk -> bpf_ireg -> bpf_ireg -> int16 -> bpf_instruction
  | BPF_ST : MChunk -> bpf_ireg -> snd_op -> int16 -> bpf_instruction
  | BPF_ADD_STK : int -> bpf_instruction
  | BPF_ALU : binop -> bpf_ireg -> snd_op -> bpf_instruction
  | BPF_NEG32_REG : bpf_ireg -> bpf_instruction
  | BPF_LE : bpf_ireg -> int -> bpf_instruction
  | BPF_BE : bpf_ireg -> int -> bpf_instruction
  | BPF_ALU64 : binop -> bpf_ireg -> snd_op -> bpf_instruction
  | BPF_NEG64_REG : bpf_ireg -> bpf_instruction
  | BPF_HOR64_IMM : bpf_ireg -> int -> bpf_instruction
  | BPF_PQR : pqrop -> bpf_ireg -> snd_op -> bpf_instruction
  | BPF_PQR64 : pqrop -> bpf_ireg -> snd_op -> bpf_instruction
  | BPF_PQR2 : pqrop2 -> bpf_ireg -> snd_op -> bpf_instruction
  | BPF_JA : off_ty -> bpf_instruction
  | BPF_JUMP : condition -> bpf_ireg -> snd_op -> off_ty -> bpf_instruction
  | BPF_CALL_REG : bpf_ireg -> int -> bpf_instruction
  | BPF_CALL_IMM : bpf_ireg -> int -> bpf_instruction
  | BPF_EXIT : bpf_instruction.

Definition ebpf_asm := list bpf_instruction.

Definition bpf_bin := list int64.

Definition bpf_ireg_to_nat (r : bpf_ireg) : nat :=
  match r with
  | BR0  =>  0%nat
  | BR1  =>  1%nat
  | BR2  =>  2%nat
  | BR3  =>  3%nat
  | BR4  =>  4%nat
  | BR5  =>  5%nat
  | BR6  =>  6%nat
  | BR7  =>  7%nat
  | BR8  =>  8%nat
  | BR9  =>  9%nat
  | BR10 => 10%nat
  end.

Definition nat_to_bpf_ireg (dst : nat) : option bpf_ireg :=
       if Nat.eqb dst 0  then Some BR0
  else if Nat.eqb dst 1  then Some BR1
  else if Nat.eqb dst 2  then Some BR2
  else if Nat.eqb dst 3  then Some BR3
  else if Nat.eqb dst 4  then Some BR4
  else if Nat.eqb dst 5  then Some BR5
  else if Nat.eqb dst 6  then Some BR6
  else if Nat.eqb dst 7  then Some BR7
  else if Nat.eqb dst 8  then Some BR8
  else if Nat.eqb dst 9  then Some BR9
  else if Nat.eqb dst 10 then Some BR10
  else None.
