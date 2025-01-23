From Coq Require Import ZArith List Lia.
From compcert.lib Require Import Integers Maps Zbits.
From compcert.common Require Import Memory AST.
From bpf.model Require Import ebpf rBPFCommType rBPFSyntax MyTactic.
From bpf.model Require Import rBPFDecoder rBPFEncoder BitfieldLemma BinSolver.

Lemma rbpf_decode_encode_consistency:
  forall pc l ins
    (Hdecode: rbpf_decoder pc l = Some ins),
     exists l_bin, rbpf_encoder ins = l_bin /\ 
     list_in_list Int64.eq l_bin pc l = true.
Proof.
  intros.
  unfold rbpf_encoder, rbpf_decoder in *.
  destruct nth_error eqn:Hnth; [| inversion Hdecode].
  destruct ins; try ( eexists; split; [reflexivity |] ).
  - unfold_bin. simpl. 
Admitted.