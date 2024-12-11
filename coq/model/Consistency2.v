From Coq Require Import ZArith List.
From compcert.lib Require Import Integers Maps.
From compcert.common Require Import Memory AST.
From bpf.model Require Import ebpf rBPFCommType rBPFSyntax rBPFDecoder rBPFEncoder.

Import ListNotations.

Lemma rbpf_decode_encode_consistency:
  forall l_bin pc l ins
    (HL: list_in_list Int64.eq l_bin pc l = true)
    (Hdecode: rbpf_decoder pc l = Some ins),
      rbpf_encoder ins = l_bin.
Admitted.