From Coq Require Import List.
From compcert.lib Require Import Coqlib Integers Maps.
From bpf.model Require Import rBPFCommType rBPFSyntax.

Record CallFrame := {
  caller_saved_registers : list u64;
  frame_pointer : u64;
  target_pc : u64
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

Definition reg_map := reg_Map.t u64.

Record EbpfVmState := {
  host_stack_pointer : u64;
  call_depth : u64;
  stack_pointer : u64;
  previous_instruction_meter : u64;
  due_insn_count : u64;
  stopwatch_numerator : u64;
  stopwatch_denominator : u64;
  registers : reg_map;
  program_result : option u64;
  memory_mapping : (u64 * u64) -> u64;
  call_frames : list CallFrame;
  loader : bpf_bin
}.