From Coq Require Import ZArith List Lia.
From compcert.lib Require Import Integers Maps Zbits.
From compcert.common Require Import Memory AST.
From bpf.model Require Import ebpf rBPFCommType rBPFSyntax.
From bpf.model Require Import rBPFDecoder rBPFEncoder BitfieldLemma BinSolver.

Ltac bin_solver :=
  match goal with
  | |- context [Int64.unsigned_bitfield_extract 0 64 _] =>
     erewrite int64_extract_same; eauto

  | |- context [Int64.bitfield_insert 0 ?w (Int64.repr 0) (Int64.unsigned_bitfield_extract 0 ?w ?i)] =>
      erewrite unsigned_bitfield_insert_extract_zero_eq;
      [| change Int64.zwordsize with 64; lia]
  | |- context [Int64.bitfield_insert ?p ?w  (Int64.unsigned_bitfield_extract 0 ?p ?i) (Int64.unsigned_bitfield_extract ?p ?w ?i)] =>
      erewrite unsigned_bitfield_extract_extend;
      [simpl | change Int64.zwordsize with 64; lia]

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
(*
Ltac bin_solver2 :=
  match goal with


  | |- context[Int64.bitfield_insert ?p0 ?w0 ?i0 ?v0] =>
    erewrite bitfield_insert_over_size_zero with (pos := p0) (width := w0) ;
    [ match goal with
      | |- context [Int64.bitfield_insert] => idtac
      | |- ?X = ?X => reflexivity
      | |- _ => idtac
      end
      | replace Int64.zwordsize with 64%Z by reflexivity; lia
      |]


  | |- context[Int64.bitfield_insert ?p0 ?w0 ?i0 _] =>
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
  end.*)

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

Lemma int64_zero_to_nat :
  Int64.size (Int64.repr 0) = 0.
Proof.
  fold Int64.zero.
  rewrite Int64.size_zero.
  reflexivity.
Qed.

Lemma some_eq_eq: forall {A:Type} (a b:A),
  Some a = Some b -> a = b.
Proof.
  intros.
  inversion H.
  reflexivity.
Qed.

Ltac simp_if_context_false :=
  let K := fresh "K" in
  match goal with
    | H: (if ?A then _ else _) = _ |- _ => destruct A eqn: K; [ inversion H | simp_if_context_false]
    | H: None = Some _ |- _ => inversion H
    end.

Ltac simp_if_context_post :=
    match goal with
    | K: (Z.to_nat ?v =? ?n)%nat = true |- Z.of_nat ?n = ?v  =>
  rewrite Nat.eqb_eq in K;
rewrite <- K;
rewrite Z2Nat.id; [reflexivity | assumption]
    end.

Ltac simp_if_context :=
  simp_if_context_false; simp_if_context_post.

Lemma bpf_reg_decode_eq:
  forall v r
   (HZ: (0 <= v)%Z)
    (HR: nat_to_bpf_ireg (Z.to_nat v) = Some r),
    Z.of_nat (bpf_ireg_to_nat r) = v.
Proof.
  intros.
  unfold nat_to_bpf_ireg, bpf_ireg_to_nat in *.
  destruct r; simp_if_context.
Qed.

Lemma int64_unsigned_ge_0:
  forall v,
    0 <= Int64.unsigned v.
Proof.
  intros.
  pose proof (Int64.unsigned_range_2 v) as H.
  lia.
Qed.

Lemma int64_eq_iff:
  forall x y,
    Int64.eq x y = true <-> x = y.
Proof.
  intros.
  split.
  apply Int64.same_if_eq.
  intro Heq; subst.
  apply Int64.eq_true.
Qed.

Lemma int16_eq_iff:
  forall x y,
    Int16.eq x y = true <-> x = y.
Proof.
  intros.
  split.
  apply Int16.same_if_eq.
  intro Heq; subst.
  apply Int16.eq_true.
Qed.

Lemma int_eq_iff:
  forall x y,
    Int.eq x y = true <-> x = y.
Proof.
  intros.
  split.
  apply Int.same_if_eq.
  intro Heq; subst.
  apply Int.eq_true.
Qed.

Lemma byte_eq_iff:
  forall x y,
    Byte.eq x y = true <-> x = y.
Proof.
  intros.
  split.
  apply Byte.same_if_eq.
  intro Heq; subst.
  apply Byte.eq_true.
Qed.


Lemma int64_sign_int_extract_32_eq:
  forall i,
    (Int64.repr
     (Int.unsigned
        (Int.repr
           (Int64.signed
              (Int64.unsigned_bitfield_extract 32 32 i))))) = (Int64.unsigned_bitfield_extract 32 32 i).
Proof.
  intros.
  unfold Int64.unsigned_bitfield_extract. simpl.
  rewrite Int.unsigned_repr; [rewrite Int64.repr_signed; reflexivity |]. 
  rewrite Int64.signed_eq_unsigned;
  pose proof Int64.zero_ext_range 32 (Int64.shru i (Int64.repr 32)) as Hrange;
  unfold Int64.zwordsize, two_p, two_power_pos in Hrange;
  simpl in Hrange.
  - change Int.max_unsigned with 4294967295.
    lia.
  - change Int64.max_signed with 9223372036854775807.
    lia.
Qed.


Lemma int64_unsign_byte_extract_8_eq:
  forall i,
    (Int64.repr
       (Byte.unsigned
          (Byte.repr
             (Int64.unsigned
                (Int64.unsigned_bitfield_extract
                   (Z.of_nat 0) 
                   (Z.of_nat 8) i))))) =
    (Int64.unsigned_bitfield_extract
                             (Z.of_nat 0) 
                             (Z.of_nat 8) i).
Proof.
  intros.
  unfold Int64.unsigned_bitfield_extract. simpl.
  rewrite Byte.unsigned_repr; [rewrite Int64.repr_unsigned; reflexivity |].
  pose proof Int64.zero_ext_range 8 (Int64.shru i (Int64.repr 0)) as Hrange.
  unfold Int64.zwordsize, two_p, two_power_pos in Hrange.
  simpl in Hrange.
  change Byte.max_unsigned with 255.
  lia.
Qed.


Lemma int64_sign_int16_extract_16_eq:
  forall i,
    (Int64.repr
        (Int16.unsigned
           (Int16.repr
              (Int64.signed
                 (Int64.unsigned_bitfield_extract
                    (Z.of_nat 16) (Z.of_nat 16) i))))) =
    (Int64.unsigned_bitfield_extract
                    (Z.of_nat 16) (Z.of_nat 16) i).
Proof.
  intros.
  unfold Int64.unsigned_bitfield_extract.
  rewrite Int16.unsigned_repr; [rewrite Int64.repr_signed; reflexivity |].
  simpl.
  rewrite Int64.signed_eq_unsigned;
  pose proof Int64.zero_ext_range 16 (Int64.shru i (Int64.repr 16)) as Hrange;
  unfold Int64.zwordsize, two_p, two_power_pos in Hrange;
  simpl in Hrange.
  - change Int16.max_unsigned with 65535.
    lia.
  - change Int64.max_signed with 9223372036854775807.
    lia.
Qed.

Lemma int64_unsign_z_nat_16_eq :
  forall i,
    (Int64.repr
           (Z.of_nat
              (Z.to_nat
                 (Int64.unsigned i)))) = i.
Proof.
  intros.
  rewrite Z2Nat.id.
  - rewrite Int64.repr_unsigned.
    reflexivity.
  - pose proof Int64.unsigned_range i as Hrange.
    destruct Hrange as [H1 H2].
    apply H1.
Qed.