Require Import rBPFCommType.
Require Import rBPFSyntax.
Require Import Coqlib List.
From compcert.lib Require Import Integers.

Record CallFrame := {
  caller_saved_registers : list u64;
  frame_pointer : u64;
  target_pc : u64
}.

Definition reg_map := bpf_ireg -> u64.

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