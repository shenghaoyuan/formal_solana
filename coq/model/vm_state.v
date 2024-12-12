From Coq Require Import List.
From compcert.lib Require Import Coqlib Integers Maps.
From bpf.model Require Import rBPFCommType rBPFSyntax.

Record CallFrame := {
  caller_saved_registers : list int64;
  frame_pointer : int64;
  target_pc : int64
}.

Lemma reg_eq: forall (x y: bpf_ireg), {x=y} + {x<>y}.
Proof.
  decide equality.
Qed.

Module reg_Eq.
  Definition t := bpf_ireg.
  Definition eq := reg_eq.
End reg_Eq.

Module reg_Map := EMap (reg_Eq).

Definition reg_map := reg_Map.t int64.

Record EbpfVmState := {
  host_stack_pointer : int64;
  call_depth : int64;
  stack_pointer : int64;
  previous_instruction_meter : int64;
  due_insn_count : int64;
  stopwatch_numerator : int64;
  stopwatch_denominator : int64;
  registers : reg_map;
  program_result : option int64;
  memory_mapping : (int64 * int64) -> int64;
  call_frames : list CallFrame;
  loader : bpf_bin
}.