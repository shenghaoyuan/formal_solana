From Coq Require Import ZArith List Lia.
From compcert.lib Require Import Integers Maps Zbits.
From compcert.common Require Import Memory AST.
From bpf.model Require Import ebpf rBPFCommType rBPFSyntax MyTactic.
From bpf.model Require Import rBPFDecoder rBPFEncoder BitfieldLemma BinSolver.

Lemma rbpf_decode_encode_consistency:
  forall l_bin pc l ins
    (HL: list_in_list Int64.eq l_bin pc l = true)
    (Hdecode: rbpf_decoder pc l = Some ins),
      rbpf_encoder ins = l_bin.
Proof.
  intros. 
  unfold rbpf_encoder, rbpf_decoder in *.
  destruct ins.
  - bsolver.
destruct nth_error as [ins |] eqn :Hnth in Hdecode.
    + 