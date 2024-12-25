From Coq Require Import ZArith List Lia.
From compcert.lib Require Import Integers Maps.
From compcert.common Require Import Memory AST.
From bpf.model Require Import ebpf rBPFCommType rBPFSyntax.
From bpf.model Require Import rBPFDecoder rBPFEncoder BitfieldLemma BinSolver.

Import ListNotations.

Ltac bin_solver :=
  match goal with


  | |- context[Int64.unsigned_bitfield_extract ?p0 ?w0 (Int64.bitfield_insert ?p0 ?w0 ?i0 ?v0)] =>
    erewrite unsigned_bitfield_extract_bitfield_insert_same_1 with (pos := p0) (width := w0);
    [ match goal with
      | |- context [Int64.bitfield_insert] => idtac
      | |- context [Int64.unsigned_bitfield_extract] => idtac
      | |- ?X = ?X => reflexivity
      | |- _ => idtac
      end
      | replace Int64.zwordsize with 64%Z by reflexivity; lia
      |]


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

Ltac unfold_bin := unfold binary_to_int64, decode_bpf, encode_bpf.

Lemma int64_size_int_sign_le32: forall i,
  Int64.size (Int64.repr (Int.signed i)) <= 32.
Admitted.

Global Hint Resolve int64_size_int_sign_le32 : int_size.

Ltac bsolver := unfold_bin; simpl; repeat bin_solver; auto with int_size.

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
    bsolver.
    change (Byte.unsigned (Byte.repr (Int64.unsigned (Int64.repr (Byte.unsigned (Byte.repr 24))))) =? 24) with true.
    simpl.
    rewrite Hnth0.
    + bsolver. (*TODO
  match goal with


  | |- context[Int64.unsigned_bitfield_extract ?p0 ?w0 (Int64.bitfield_insert ?p0 ?w0 ?i0 ?v0)] =>
    erewrite unsigned_bitfield_extract_bitfield_insert_same_1 with (pos := p0) (width := w0)
  end.*)

Admitted.