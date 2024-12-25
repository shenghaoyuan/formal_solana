From Coq Require Import ExtrOcamlBasic ExtrOcamlString.

From Coq Require Import Ascii String List ZArith PArith.
Import ListNotations.

From compcert.lib Require Import Integers.
From bpf.model Require Import rBPFCommType ebpf vm vm_state rBPFDecoder rBPFSyntax Interpreter.


(*
(**r replace some extraction from ExtrOcamlZInt *)
Extract Constant Pos.succ => "Stdlib.succ".
Extract Constant Pos.pred => "fun n -> Stdlib.max 1 (n-1)".
Extract Constant Pos.sub => "fun n m -> Stdlib.max 1 (n-m)".
Extract Constant Pos.min => "Stdlib.min".
Extract Constant Pos.max => "Stdlib.max". (*
Extract Constant Pos.compare =>
 "fun x y -> if x=y then 0 else if x<y then (-1) else 1".
Extract Constant Pos.compare_cont =>
 "fun c x y -> if x=y then c else if x<y then (-1) else 1". *)

Extract Constant N.succ => "Stdlib.succ".
Extract Constant N.pred => "fun n -> Stdlib.max 0 (n-1)".
Extract Constant N.sub => "fun n m -> Stdlib.max 0 (n-m)".
Extract Constant N.min => "Stdlib.min".
Extract Constant N.max => "Stdlib.max". (*
Extract Constant N.compare =>
 "fun x y -> if x=y then 0 else if x<y then (-1) else 1". *)

Extract Constant Z.succ => "Stdlib.succ".
Extract Constant Z.pred => "Stdlib.pred".
Extract Constant Z.abs => "Stdlib.abs".
Extract Constant Z.min => "Stdlib.min".
Extract Constant Z.max => "Stdlib.max". (*
Extract Constant Z.compare =>
 "fun x y -> if x=y then 0 else if x<y then (-1) else 1". *)
Extract Constant Z.abs_N => "Stdlib.abs".*)


Extract Inductive int => "z" [""].
Extract Inductive int64 => "z" [""].
Extract Inductive Int128.int => "z" [""].
Extract Inductive Ptrofs.int => "z" [""].
Extract Inductive Int16.int => "z" [""].
Extract Inductive Byte.int => "z" [""].
(*
Extract Inductive nat => int [ "Z0" "" ] "(fun fO fS n -> if n=0 then fO () else fS (n-1))".*)

Extract Inductive bool => "bool" [ "true" "false" ].
Extract Inductive sumbool => "bool" [ "true" "false" ].
Extract Inductive list => "list" [ "[]" "(::)" ].

Set Extraction AccessOpaque.

Extraction TestCompile step_test.

Extraction "/home/liuhao/formal_solana/coq/test/interpreter_test.ml" bpf_interp_test.
Extraction "/home/liuhao/formal_solana/coq/test/step_test.ml" step_test.


