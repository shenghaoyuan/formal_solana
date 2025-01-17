From Coq Require Import ZArith List Lia.
From compcert.lib Require Import Integers Maps Zbits.
From compcert.common Require Import Memory AST.
From bpf.model Require Import ebpf rBPFCommType rBPFSyntax.
From bpf.model Require Import rBPFDecoder rBPFEncoder BitfieldLemma BinSolver.

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

Lemma int64_size_int_unsign_le32: forall i,
  Int64.size (Int64.repr (Int.unsigned i)) <= 32.
Proof.
  intros.
  apply Int64.bits_size_3; [lia |].
  intros n Hrange.
  rewrite Int64.testbit_repr; [| lia].
  apply Ztestbit_above with (n := 32%nat); [| lia].
  unfold two_power_nat; simpl.
  apply Int.unsigned_range.
Qed.

Lemma int64_size_int16_unsign_le16: forall i,
  Int64.size (Int64.repr (Int16.unsigned i)) <= 16.
Proof.
  intros.
  apply Int64.bits_size_3; [lia |].
  intros n Hrange.
  rewrite Int64.testbit_repr; [| lia].
  apply Ztestbit_above with (n := 16%nat); [| lia].
  unfold two_power_nat; simpl.
  apply Int16.unsigned_range.
Qed.
  

Lemma int64_size_byte_unsign_le8: forall i,
  Int64.size (Int64.repr (Byte.unsigned (Byte.repr i))) <= 8.
Proof.
  intros.
  apply Int64.bits_size_3; [lia |].
  intros n Hrange.
  rewrite Int64.testbit_repr; [| lia].
  apply Ztestbit_above with (n := 8%nat); [| lia].
  unfold two_power_nat; simpl.
  apply Byte.unsigned_range.
Qed.

Global Hint Resolve int64_size_int_unsign_le32 : int_size.
Global Hint Resolve int64_size_int16_unsign_le16 : int16_size.
Global Hint Resolve int64_size_byte_unsign_le8 : byte_size.

Ltac bsolver := unfold_bin; simpl; repeat bin_solver; auto with int_size int16_size byte_size.


Lemma int64_range_int_range_unsign_le: forall i,
  Int64.min_signed <= Int.unsigned i <= Int64.max_signed.
Proof.
  intros.
  pose proof Int.unsigned_range i as Hrange.
  destruct Hrange as [H1 H2].
  split.
  - rewrite <- H1.
    unfold Int64.min_signed.
    simpl.
    lia.
  - unfold Int64.max_signed, Int.modulus, two_power_nat in *.
    simpl in *.
    lia.
Qed.

Lemma bpf_ireg_nat_trans_cons : forall b,
  nat_to_bpf_ireg 
    (Z.to_nat 
      (Int64.unsigned 
        (Int64.repr 
          (Z.of_nat 
            (bpf_ireg_to_nat b))))) = Some b.
Proof.
  unfold bpf_ireg_to_nat, nat_to_bpf_ireg.
  destruct b; rewrite Int64.unsigned_repr; simpl;
  try reflexivity; change Int64.max_unsigned with 18446744073709551615; lia.
Qed.

Lemma int_repr_int64_repr_cons : forall i, 
  Int.repr (Int64.signed (Int64.repr (Int.unsigned i))) = i.
Proof.
  intros i.
  rewrite Int64.signed_repr. 
  - rewrite Int.repr_unsigned.
    reflexivity.
  - apply int64_range_int_range_unsign_le.
Qed.

Lemma byte_int64_eq : forall i,
  (0 <= i <= 255) -> (
  Byte.unsigned
      (Byte.repr
         (Int64.unsigned
            (Int64.repr
               (Byte.unsigned
                  (Byte.repr
                     i))))) = i).
Proof.
  intros.
  rewrite Byte.unsigned_repr; rewrite Int64.unsigned_repr; rewrite Byte.unsigned_repr;
  try reflexivity; 
  try (unfold Byte.max_unsigned; simpl; apply H); 
  try (unfold Int64.max_unsigned; simpl; destruct H as [H1 H2];
       split; [apply H1 |]; rewrite H2; lia).
Qed.

Lemma int64_range_int16_range_unsign_le: forall i,
  Int64.min_signed <= Int16.unsigned i <= Int64.max_signed.
Proof.
  intros.
  pose proof Int16.unsigned_range i as Hrange.
  destruct Hrange as [H1 H2].
  split.
  - rewrite <- H1.
    unfold Int64.min_signed.
    simpl.
    lia.
  - unfold Int64.max_signed, Int16.modulus, two_power_nat in *.
    simpl in *.
    lia.
Qed.

Lemma int16_int64_eq: forall i,
  (Int16.repr (Int64.signed (Int64.repr (Int16.unsigned i)))) = i.
Proof.
  intros.
  rewrite Int64.signed_repr.
  - rewrite Int16.repr_unsigned.
    reflexivity.
  - apply int64_range_int16_range_unsign_le.
Qed.

Lemma bpf_ireg_to_nat_size_le4 : forall b,
  Int64.size (Int64.repr (Z.of_nat (bpf_ireg_to_nat b))) <= 4.
Proof.
  destruct b;
  try ( simpl; unfold Int64.size, Zsize; rewrite Int64.unsigned_repr;
  [ simpl; lia | unfold Int64.max_unsigned; simpl; lia ] ).
Qed.
