From Coq Require Import ZArith List Lia.
From compcert.lib Require Import Integers Maps.
From compcert.common Require Import Memory AST.
From bpf.model Require Import ebpf rBPFCommType rBPFSyntax.
From bpf.model Require Import rBPFDecoder rBPFEncoder BitfieldLemma BinSolver.

Import ListNotations.

Ltac bin_solver :=
  match goal with
  | |- context[Int64.unsigned_bitfield_extract ?p1 ?w1 (Int64.bitfield_insert ?p0 ?w0 ?i0 _)] =>
    ( match eval compute in (p0 + w0 - p1)%Z with
      | Zpos _ => idtac
      | _ =>
        erewrite unsigned_bitfield_extract_bitfield_insert_same_2 with
        (pos0 := p0) (width0 := w0) (pos1 := p1) (width1 := w1) (i := i0);
      [ try reflexivity | try lia | try (replace Int64.zwordsize with 64%Z by reflexivity; lia) ]
      end ||
      match eval compute in (p1 + w1 - p0)%Z with
      | Zpos _ => idtac
      | _ =>
        erewrite unsigned_bitfield_extract_bitfield_insert_same_2 with
        (pos0 := p0) (width0 := w0) (pos1 := p1) (width1 := w1) (i := i0);
      [ try reflexivity | try lia | try (replace Int64.zwordsize with 64%Z by reflexivity; lia) ]
      end)
  end.

Ltac bsolver := repeat bin_solver.

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
    destruct nth_error as [ins0 |] eqn: Hnth0 in HL; [| inversion HL].
    rewrite Bool.andb_true_iff in HL.
    destruct HL as (Hins0 & _).
    apply Int64.same_if_eq in Hins, Hins0.
    subst.
    assert (Heq: Byte.unsigned (Byte.repr (Int64.unsigned (decode_bpf (
      binary_to_u64 (Byte.repr 24)
      (bpf_ireg_to_u4 d) 0%nat (Word.repr 0) i) 0 8))) = Z.of_nat 24).
    { unfold binary_to_u64.
      unfold decode_bpf, encode_bpf.
      bsolver.
    }
    rewrite Heq; clear Heq.
    simpl.
    rewrite Hnth0.
(** TODO: remove all u64/u32 ... *)
      ...
Admitted.