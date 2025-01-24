From Coq Require Import ZArith List Lia.
From compcert.lib Require Import Integers Maps Zbits.
From compcert.common Require Import Memory AST.
From bpf.model Require Import ebpf rBPFCommType rBPFSyntax MyTactic.
From bpf.model Require Import rBPFDecoder rBPFEncoder BitfieldLemma BinSolver.

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

Admitted.

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

Admitted.


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

Admitted.

Lemma int64_unsign_z_nat_16_eq :
  forall i,
    (Int64.repr
           (Z.of_nat
              (Z.to_nat
                 (Int64.unsigned i)))) = i.
Proof.

Admitted.


Lemma rbpf_decode_encode_consistency:
  forall pc l ins
    (Hdecode: rbpf_decoder pc l = Some ins),
     exists l_bin, rbpf_encoder ins = l_bin /\ 
     list_in_list Int64.eq l_bin pc l = true.
Proof.
  unfold rbpf_encoder, rbpf_decoder in *.
  intros.
  destruct nth_error eqn:Hnth; [| inversion Hdecode].
  destruct ins; try ( eexists; split; [reflexivity |] ).
  - (* LDDW*)
    destruct (_ =? _)%Z eqn: Hlddw in Hdecode.
    + destruct nth_error eqn:Hnth1 in Hdecode; [| inversion Hdecode].
      destruct (nat_to_bpf_ireg _) as [dst | ] eqn: Hdst; [| inversion Hdecode].
      destruct (_ && _)%bool eqn: Hlddwb in Hdecode; inversion Hdecode; subst.
      rewrite ! Bool.andb_true_iff in *.
      destruct Hlddwb as (((((Hb1 & Hb2) & Hb3) & Hb4) & Hb5) & Hb6).
      rewrite ! Nat.eqb_eq, Z.eqb_eq in *.
      rewrite ! int16_eq_iff, byte_eq_iff in *.
      rewrite <- Hb1 at 1.
      rewrite <- Hb2 at 1.
      rewrite <- Hb3 at 1.
      rewrite <- Hb4 at 9.
      rewrite <- Hb5 at 11.
      rewrite <- Hb6 at 1.
      rewrite <- Hlddw.
      simpl in *.
      rewrite Hnth, Hnth1.
      unfold_bin.
      erewrite bpf_reg_decode_eq with (r := b); [| apply int64_unsigned_ge_0 | apply Hdst].
      clear Hdecode Hnth Hnth1 Hlddw.
      apply andb_true_intro.
      split.
      * apply int64_eq_iff.
        rewrite ! Int64.repr_unsigned, Byte.repr_unsigned.
        rewrite ! int64_sign_int_extract_32_eq, int64_sign_int16_extract_16_eq,  int64_unsign_byte_extract_8_eq, int64_unsign_z_nat_16_eq.
        bsolver.
Admitted.