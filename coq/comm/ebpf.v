Require Import rBPFCommType.
Require Import rBPFSyntax.
From compcert.lib Require Import Integers Maps.
Require Import ZArith.

Definition SCRATCH_REGS : nat := 4. (* Number of scratch registers *)
Definition INSN_SIZE : nat := 8.    (* Instruction size in bytes *)

Definition MM_STACK_START : u64 := Int64.repr 0x200000000. (* Stack start address *)

Definition func_key := u32.         (* Function registry key type *)
Definition func_val := u64.         (* Function registry value type *)

Definition func_map := func_key -> option func_val. (* Function registry as a map *)

Definition init_func_map : func_map := fun _ => None.

Definition get_function_registry (key : func_key) (fm : func_map) : option func_val :=
  fm key.