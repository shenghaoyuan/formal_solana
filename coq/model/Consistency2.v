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
      * apply andb_true_intro.
        split; [| reflexivity].
        apply int64_eq_iff.
        rewrite ! int64_sign_int_extract_32_eq, int64_sign_int16_extract_16_eq,  int64_unsign_byte_extract_8_eq, int64_unsign_z_nat_16_eq, int64_unsign_z_nat_16_eq.
        bsolver.
    + exfalso.
      clear Hlddw Hnth.
      unfold rbpf_decoder_one, binary_to_int64, decode_bpf, encode_bpf in Hdecode.
      simpl in *.
      destruct (_ =? _)%Z eqn:Heq1 in Hdecode.
      * destruct (_ =? _)%nat eqn:Hstk in Hdecode; [inversion Hdecode |].
        destruct (nat_to_bpf_ireg (Z.to_nat (Int64.unsigned (Int64.unsigned_bitfield_extract 8 4 i)))) eqn:Hnat in Hdecode;
        inversion Hdecode.
      * repeat (destruct (nat_to_bpf_ireg _) in Hdecode; [| inversion Hdecode]).
        repeat (destruct (_ =? _) in Hdecode; [inversion Hdecode |]).
        inversion Hdecode.
  - destruct (_ =? _)%Z eqn: Hlddw in Hdecode.
    + destruct nth_error eqn:Hnth1 in Hdecode; [| inversion Hdecode].
      destruct (nat_to_bpf_ireg _) as [dst | ] eqn: Hdst; [| inversion Hdecode].
      destruct (_ && _)%bool eqn: Hlddwb in Hdecode; inversion Hdecode.
    + unfold rbpf_decoder_one, binary_to_int64, decode_bpf, encode_bpf in *.
      simpl in *.
      clear Hlddw.
      destruct (_ =? _)%Z eqn:Heq1 in Hdecode.
      * destruct (_ =? _)%nat eqn:Hstk in Hdecode; [inversion Hdecode |].
        destruct (nat_to_bpf_ireg (Z.to_nat (Int64.unsigned (Int64.unsigned_bitfield_extract 8 4 i)))) eqn:Hnat in Hdecode;
        inversion Hdecode.
      * destruct (nat_to_bpf_ireg _) eqn:Hdst in Hdecode; [| inversion Hdecode].
        destruct (nat_to_bpf_ireg _) eqn:Hsrc in Hdecode; [| inversion Hdecode].
        destruct m.
        destruct (_ =? _) eqn:Heq in Hdecode.
        -- inversion Hdecode.
           subst.
           rewrite Hnth.
           apply andb_true_intro.
           split.
           --- apply int64_eq_iff.
               rewrite ! Byte.unsigned_repr in *; try (unfold Byte.max_unsigned; simpl; lia).
               rewrite Z.eqb_eq in Heq.
               rewrite <- Heq.
               
               bsolver.
               Search Int64.bitfield_insert.
               rewrite Z.eqb_neq in *.
               admit.



        rewrite Hnth.
        -- apply andb_true_intro.
           split.
           --- apply int64_eq_iff.
               rewrite ! Byte.unsigned_repr; [| unfold Byte.max_unsigned; simpl; lia].
               rewrite ! Int.unsigned_repr; [| unfold Int.max_unsigned; simpl; lia].
               Search Int64.bitfield_insert.
               bsolver. 
               rewrite Z.eqb_neq in *.
               admit.
           --- destruct l as [| h0 l0]; [rewrite Coqlib.nth_error_nil in Hnth; inversion Hnth |].
               destruct (nth_error l0 pc) eqn:Hnth2. ---- apply andb_true_intro. split. apply int64_eq_iff.



Admitted.
    