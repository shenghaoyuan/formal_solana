From Coq Require Import ZArith.
From compcert.lib Require Import Integers Maps.

From bpf.model Require Import rBPFCommType rBPFSyntax.

Definition SCRATCH_REGS : nat := 4. (* Number of scratch registers *)
Definition INSN_SIZE : nat := 8.    (* Instruction size in bytes *)

Definition MM_STACK_START : int64 := Int64.repr 0x200000000. (* Stack start address *)

Definition func_key := int.         (* Function registry key type *)
Definition func_val := int64.         (* Function registry value type *)

Module func_Eq.
  Definition t := func_key.
  Definition eq := Int.eq_dec.
End func_Eq.

Module func_Map := EMap(func_Eq).

Definition func_map := func_Map.t (option func_val).

Definition init_func_map : func_map := func_Map.init None.

Definition get_function_registry (key : func_key) (fm : func_map) : option func_val :=
  func_Map.get key fm.