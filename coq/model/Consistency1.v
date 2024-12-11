From Coq Require Import ZArith List.
From compcert.lib Require Import Integers Maps.
From compcert.common Require Import Memory AST.
From bpf.model Require Import ebpf rBPFCommType rBPFSyntax.
From bpf.model Require Import rBPFDecoder rBPFEncoder BinSolver.

Import ListNotations.

Lemma rbpf_encode_decode_consistency:
  forall l_bin pc l ins
    (HL: list_in_list Int64.eq l_bin pc l = true)
    (Hencode: rbpf_encoder ins = l_bin),
      rbpf_decoder pc l = Some ins.
Proof.
  intros.
  unfold rbpf_encoder, rbpf_decoder in *.
  destruct ins; rewrite <- Hencode in HL; simpl in HL.
  - destruct nth_error as [ins |] eqn: Hnth; [| inversion HL].
    rewrite Bool.andb_true_iff in HL.
    destruct HL as (Hins & HL).
    destruct l as [| h0 l0]; [inversion HL |].
    destruct nth_error as [ins0 |] eqn: Hnth0 in HL.
    rewrite Bool.andb_true_iff in HL.
    destruct HL as (Hins0 & _).
    apply Int64.same_if_eq in Hins, Hins0.
    subst.
    assert (Heq: Byte.unsigned (Byte.repr (Int64.unsigned (decode_bpf (
      binary_to_u64 (Byte.repr 24)
      (bpf_ireg_to_u4 d) 0%nat (Word.repr 0) i) 0 8))) = Z.of_nat 24).
    { unfold binary_to_u64.
      atp_de decode_bpf encode_bpf.
      ...
Admitted.