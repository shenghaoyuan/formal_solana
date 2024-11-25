Require Import Coqlib ZArith.
Require Import rBPFCommType ebpf Mem vm vm_state rBPFDecoder rBPFSyntax.
Import ListNotations.
Require Import String.
Open Scope string_scope.
From compcert.lib Require Import Integers.

Record stack_state := {
  call_depth : u64;
  stack_pointer : u64;
  call_frames : list CallFrame;
}.

Definition eval_reg (dst : dst_ty) (rm : reg_map) : u64 :=
  rm dst.

Fixpoint create_list {A : Type} (n : nat) (def_v : A) : list A :=
  match n with
  | O => []
  | S n' => def_v :: create_list n' def_v
  end.

Example test_create_list_0 : create_list 0 42 = nil.
Proof. reflexivity. Qed.

Example test_create_list_1 : create_list 3 "hello" = ["hello"; "hello"; "hello"].
Proof. reflexivity. Qed.

Definition MM_INPUT_START : u64 := Int64.repr 0x400000000.

Definition init_stack_state : stack_state :=
  {|
    call_depth := Int64.repr 0;
    stack_pointer := Int64.add MM_STACK_START (Int64.mul stack_frame_size max_call_depth);
    call_frames := create_list (Z.to_nat (Int64.unsigned max_call_depth))
                    {|
                      caller_saved_registers := [];
                      frame_pointer := Int64.repr 0;
                      target_pc := Int64.repr 0
                    |}
  |}.

Inductive bpf_state : Type :=
  | BPF_OK : u64 -> reg_map -> mem -> stack_state -> SBPFV -> func_map -> u64 -> u64 -> bpf_state
  | BPF_Success : u64 -> bpf_state
  | BPF_EFlag : bpf_state
  | BPF_Err : bpf_state.

Definition init_reg_map : reg_map := fun _ => Int64.repr 0.

Definition init_bpf_state (rm : reg_map) (m : mem) (v : u64) (sbpfv : SBPFV) : (bs : bpf_state) :=
  BPF_OK (Int64.repr 0) (reg_map BR10)


















