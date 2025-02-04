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
  unfold rbpf_encoder, rbpf_decoder in *.
  intros.
  destruct nth_error eqn:Hnth; [| inversion Hdecode].
  eexists; split; [reflexivity |].
  destruct (_ =? _)%Z eqn: Hlddw in Hdecode.
  {(*          BPF_LD_IMM            *)
    destruct nth_error eqn:Hnth1 in Hdecode; [| inversion Hdecode].
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
    erewrite bpf_reg_decode_eq with (r := dst); [| apply int64_unsigned_ge_0 | apply Hdst].
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
  }
  unfold rbpf_decoder_one in *.
  destruct (_ =? _)%Z eqn: Hadd in Hdecode.
  {
    destruct (_ =? _)%nat eqn:Hdst in Hdecode.
    { (*          BPF_ADD_STK            *)
      destruct (_ && _)%bool eqn: Haddstk in Hdecode; inversion Hdecode. subst.
      rewrite ! Bool.andb_true_iff in *.
      destruct Haddstk as (Hb1 & Hb2).
      rewrite ! Nat.eqb_eq, Z.eqb_eq, int16_eq_iff in *.
      simpl in Hadd.
      rewrite <- Hadd.
      rewrite <- Hdst at 1.
      rewrite <- Hb1 at 5.
      unfold Int16.zero in Hb2.
      rewrite <- Hb2.
      simpl in *.
      rewrite Hnth.
      unfold_bin.
      apply andb_true_intro.
      split; [| reflexivity].
      apply int64_eq_iff.
      rewrite Z2Nat.id; [| apply int64_unsigned_ge_0].
      rewrite ! Byte.repr_unsigned, Int64.repr_unsigned.
      rewrite ! int64_sign_int_extract_32_eq, int64_sign_int16_extract_16_eq,  int64_unsign_byte_extract_8_eq, int64_unsign_z_nat_16_eq.
      bsolver.
    }(*          BPF_ADD           *)
    destruct (_ && _)%bool eqn: Haddnum in Hdecode; [| inversion Hdecode].
    rewrite ! Bool.andb_true_iff in *.
    destruct Haddnum as (Hb1 & Hb2).
    rewrite ! Nat.eqb_eq, Z.eqb_eq, int16_eq_iff in *.
    simpl in Hadd.
    clear Hlddw Hdst.
    destruct (nat_to_bpf_ireg _) as [dst | ] eqn: Hdst; [| inversion Hdecode].
    inversion Hdecode; subst.
    rewrite <- Hadd.
    rewrite <- Hb1 at 3.
    unfold Int16.zero in Hb2.
    rewrite <- Hb2.
    simpl in *.
    rewrite Hnth.
    unfold_bin.
    erewrite bpf_reg_decode_eq with (r := dst); [| apply int64_unsigned_ge_0 | apply Hdst].
    apply andb_true_intro.
    split; [| reflexivity].
    apply int64_eq_iff.
    rewrite Z2Nat.id; [| apply int64_unsigned_ge_0].
    rewrite ! Byte.repr_unsigned, Int64.repr_unsigned, Int64.repr_unsigned.
    rewrite ! int64_sign_int_extract_32_eq, int64_sign_int16_extract_16_eq,  int64_unsign_byte_extract_8_eq.
    bsolver.
  }
  clear Hlddw Hadd.
  destruct (nat_to_bpf_ireg _) as [dst | ] eqn: Hdst in Hdecode; [| inversion Hdecode].
  destruct (nat_to_bpf_ireg _) as [src | ] eqn: Hsrc in Hdecode; [| inversion Hdecode].
  do 4 ((*          BPF_LDX           *)
    destruct (_ =? _)%Z eqn: Hldx in Hdecode;
    try (
      destruct (Int.eq _ _) eqn:Himm; [| inversion Hdecode];
      inversion Hdecode; subst;
      rewrite ! int_eq_iff, Z.eqb_eq in *;
      simpl in Hldx;
      unfold Int.zero in Himm;
      rewrite <- Hldx;
      rewrite <- Himm;
      simpl in *;
      rewrite Hnth;
      unfold_bin;
      erewrite bpf_reg_decode_eq with (r := dst); [| apply int64_unsigned_ge_0 | apply Hdst];
      erewrite bpf_reg_decode_eq with (r := src); [| apply int64_unsigned_ge_0 | apply Hsrc];
      apply andb_true_intro;
      split; [| reflexivity];
      apply int64_eq_iff;
      rewrite ! Byte.repr_unsigned, Int64.repr_unsigned, Int64.repr_unsigned;
      rewrite ! int64_sign_int_extract_32_eq, int64_sign_int16_extract_16_eq,  int64_unsign_byte_extract_8_eq;
      bsolver
    );
    clear Hldx
  ).
  do 4 ((*          BPF_ST_IMM           *)
    destruct (_ =? _)%Z eqn: Hst in Hdecode;
    try (
      destruct (_ =? _)%nat eqn:Himm; [| inversion Hdecode];
      inversion Hdecode; subst;
      rewrite ! Nat.eqb_eq, Z.eqb_eq in *;
      simpl in Hst;
      unfold Int.zero in Himm;
      rewrite <- Hst at 1;
      rewrite <- Himm at 3;
      simpl in *;
      rewrite Hnth;
      unfold_bin;
      erewrite bpf_reg_decode_eq with (r := dst); [| apply int64_unsigned_ge_0 | apply Hdst];
      apply andb_true_intro;
      split; [| reflexivity];
      apply int64_eq_iff;
      rewrite Z2Nat.id; [| apply int64_unsigned_ge_0];
      rewrite ! Byte.repr_unsigned, Int64.repr_unsigned, Int64.repr_unsigned;
      rewrite ! int64_sign_int_extract_32_eq, int64_sign_int16_extract_16_eq,  int64_unsign_byte_extract_8_eq;
      bsolver
    );
    clear Hst
  ).
  do 4 ((*          BPF_ST_REG           *)
    destruct (_ =? _)%Z eqn: Hst in Hdecode;
    try (
      destruct (Int.eq _ _)%nat eqn:Himm; [| inversion Hdecode];
      inversion Hdecode; subst;
      rewrite ! int_eq_iff, Z.eqb_eq in *;
      simpl in Hst;
      unfold Int.zero in Himm;
      rewrite <- Hst at 1;
      rewrite <- Himm;
      simpl in *;
      rewrite Hnth;
      unfold_bin;
      erewrite bpf_reg_decode_eq with (r := dst); [| apply int64_unsigned_ge_0 | apply Hdst];
      erewrite bpf_reg_decode_eq with (r := src); [| apply int64_unsigned_ge_0 | apply Hsrc];
      apply andb_true_intro;
      split; [| reflexivity];
      apply int64_eq_iff;
      rewrite ! Byte.repr_unsigned, Int64.repr_unsigned, Int64.repr_unsigned;
      rewrite ! int64_sign_int_extract_32_eq, int64_sign_int16_extract_16_eq,  int64_unsign_byte_extract_8_eq;
      bsolver
    );
    clear Hst
  ).
  do 8 ((*          BPF_ALU           *)
    destruct (_ =? _)%Z eqn: Halu in Hdecode;
    try(
        destruct (_ && _)%bool eqn:Halu2 in Hdecode; [| inversion Hdecode];
        rewrite ! Bool.andb_true_iff in *;
        destruct Halu2 as (Hb1 & Hb2);
        rewrite ! Nat.eqb_eq, Z.eqb_eq, int16_eq_iff in *;
        inversion Hdecode; subst;
        simpl in Halu;
        unfold Int16.zero in Hb2;
        rewrite <- Halu at 1;
        rewrite <- Hb1 at 3;
        rewrite <- Hb2;
        simpl in *;
        rewrite Hnth;
        unfold_bin;
        erewrite bpf_reg_decode_eq with (r := dst); [| apply int64_unsigned_ge_0 | apply Hdst];
        apply andb_true_intro;
        split; [| reflexivity];
        apply int64_eq_iff;
        rewrite Z2Nat.id; [| apply int64_unsigned_ge_0];
        rewrite ! Byte.repr_unsigned, Int64.repr_unsigned, Int64.repr_unsigned;
        rewrite ! int64_sign_int_extract_32_eq, int64_sign_int16_extract_16_eq,  int64_unsign_byte_extract_8_eq;
        bsolver
    );
    clear Halu;
    destruct (_ =? _)%Z eqn: Halu in Hdecode;
    try(
      destruct (_ && _)%bool eqn:Halu2 in Hdecode; [| inversion Hdecode];
      rewrite ! Bool.andb_true_iff in *;
      destruct Halu2 as (Hb1 & Hb2);
      rewrite ! int_eq_iff, Z.eqb_eq, int16_eq_iff in *;
      inversion Hdecode; subst;
      simpl in Halu;
      unfold Int16.zero in Hb2;
      unfold Int.zero in Hb1;
      rewrite <- Halu at 1;
      rewrite <- Hb1;
      rewrite <- Hb2;
      simpl in *;
      rewrite Hnth;
      unfold_bin;
      erewrite bpf_reg_decode_eq with (r := dst); [| apply int64_unsigned_ge_0 | apply Hdst];
      erewrite bpf_reg_decode_eq with (r := src); [| apply int64_unsigned_ge_0 | apply Hsrc];
      apply andb_true_intro;
      split; [| reflexivity];
      apply int64_eq_iff;
      rewrite ! Byte.repr_unsigned, Int64.repr_unsigned, Int64.repr_unsigned;
      rewrite ! int64_sign_int_extract_32_eq, int64_sign_int16_extract_16_eq,  int64_unsign_byte_extract_8_eq;
      bsolver
    );
    clear Halu
  ).

  destruct (_ =? _)%Z eqn: Hneg32 in Hdecode.
  {  (*          BPF_NEG32           *)
    destruct (_ && _)%bool eqn:Hneg322 in Hdecode; [| inversion Hdecode].
    rewrite ! Bool.andb_true_iff in *.
    destruct Hneg322 as ((Hb1 & Hb2) & Hb3).
    rewrite ! Nat.eqb_eq, Z.eqb_eq, int16_eq_iff, int_eq_iff in *.
    inversion Hdecode; subst.
    simpl in Hneg32.
    rewrite <- Hneg32.
    rewrite <- Hb1 at 3.
    unfold Int16.zero in Hb2.
    unfold Int.zero in Hb3.
    rewrite <- Hb2.
    rewrite <- Hb3.
    simpl in *.
    rewrite Hnth.
    unfold_bin.
    erewrite bpf_reg_decode_eq with (r := dst); [| apply int64_unsigned_ge_0 | apply Hdst].
    apply andb_true_intro.
    split; [| reflexivity].
    apply int64_eq_iff.
    rewrite Z2Nat.id; [| apply int64_unsigned_ge_0].
    rewrite ! Byte.repr_unsigned, Int64.repr_unsigned, Int64.repr_unsigned.
    rewrite ! int64_sign_int_extract_32_eq, int64_sign_int16_extract_16_eq,  int64_unsign_byte_extract_8_eq.
    bsolver.
  }
  clear Hneg32.
  do 4 ((*          BPF_ALU           *)
    destruct (_ =? _)%Z eqn: Halu in Hdecode;
    try(
        destruct (_ && _)%bool eqn:Halu2 in Hdecode; [| inversion Hdecode];
        rewrite ! Bool.andb_true_iff in *;
        destruct Halu2 as (Hb1 & Hb2);
        rewrite ! Nat.eqb_eq, Z.eqb_eq, int16_eq_iff in *;
        inversion Hdecode; subst;
        simpl in Halu;
        unfold Int16.zero in Hb2;
        rewrite <- Halu at 1;
        rewrite <- Hb1 at 3;
        rewrite <- Hb2;
        simpl in *;
        rewrite Hnth;
        unfold_bin;
        erewrite bpf_reg_decode_eq with (r := dst); [| apply int64_unsigned_ge_0 | apply Hdst];
        apply andb_true_intro;
        split; [| reflexivity];
        apply int64_eq_iff;
        rewrite Z2Nat.id; [| apply int64_unsigned_ge_0];
        rewrite ! Byte.repr_unsigned, Int64.repr_unsigned, Int64.repr_unsigned;
        rewrite ! int64_sign_int_extract_32_eq, int64_sign_int16_extract_16_eq,  int64_unsign_byte_extract_8_eq;
        bsolver
    );
    clear Halu;
    destruct (_ =? _)%Z eqn: Halu in Hdecode;
    try(
      destruct (_ && _)%bool eqn:Halu2 in Hdecode; [| inversion Hdecode];
      rewrite ! Bool.andb_true_iff in *;
      destruct Halu2 as (Hb1 & Hb2);
      rewrite ! int_eq_iff, Z.eqb_eq, int16_eq_iff in *;
      inversion Hdecode; subst;
      simpl in Halu;
      unfold Int16.zero in Hb2;
      unfold Int.zero in Hb1;
      rewrite <- Halu at 1;
      rewrite <- Hb1;
      rewrite <- Hb2;
      simpl in *;
      rewrite Hnth;
      unfold_bin;
      erewrite bpf_reg_decode_eq with (r := dst); [| apply int64_unsigned_ge_0 | apply Hdst];
      erewrite bpf_reg_decode_eq with (r := src); [| apply int64_unsigned_ge_0 | apply Hsrc];
      apply andb_true_intro;
      split; [| reflexivity];
      apply int64_eq_iff;
      rewrite ! Byte.repr_unsigned, Int64.repr_unsigned, Int64.repr_unsigned;
      rewrite ! int64_sign_int_extract_32_eq, int64_sign_int16_extract_16_eq,  int64_unsign_byte_extract_8_eq;
      bsolver
    );
    clear Halu
  ).
  do 2 ((*          BPF_BE/LE           *)
    destruct (_ =? _)%Z eqn: Hswap in Hdecode;
    try(
      destruct (_ && _)%bool eqn:Hswap2 in Hdecode; [| inversion Hdecode];
      rewrite ! Bool.andb_true_iff in *;
      destruct Hswap2 as (Hb1 & Hb2);
      rewrite ! Nat.eqb_eq, Z.eqb_eq, int16_eq_iff in *;
      inversion Hdecode; subst;
      simpl in Hswap;
      unfold Int16.zero in Hb2;
      rewrite <- Hswap at 1;
      rewrite <- Hb1 at 3;
      rewrite <- Hb2;
      simpl in *;
      rewrite Hnth;
      unfold_bin;
      erewrite bpf_reg_decode_eq with (r := dst); [| apply int64_unsigned_ge_0 | apply Hdst];
      apply andb_true_intro;
      split; [| reflexivity];
      apply int64_eq_iff;
      rewrite Z2Nat.id; [| apply int64_unsigned_ge_0];
      rewrite ! Byte.repr_unsigned, Int64.repr_unsigned, Int64.repr_unsigned;
      rewrite ! int64_sign_int_extract_32_eq, int64_sign_int16_extract_16_eq,  int64_unsign_byte_extract_8_eq;
      bsolver
    );
    clear Hswap
  ).

  destruct (_ =? _)%Z eqn: Halu64 in Hdecode.
  {(*          BPF_ALU64           *)
    destruct (_ && _)%bool eqn:Halu642 in Hdecode; [| inversion Hdecode].
      rewrite ! Bool.andb_true_iff in *.
      destruct Halu642 as (Hb1 & Hb2).
      rewrite ! int_eq_iff, Z.eqb_eq, int16_eq_iff in *.
      inversion Hdecode; subst.
      simpl in Halu64.
      unfold Int16.zero in Hb2.
      unfold Int.zero in Hb1.
      rewrite <- Halu64 at 1.
      rewrite <- Hb1.
      rewrite <- Hb2.
      simpl in *.
      rewrite Hnth.
      unfold_bin.
      erewrite bpf_reg_decode_eq with (r := dst); [| apply int64_unsigned_ge_0 | apply Hdst].
      erewrite bpf_reg_decode_eq with (r := src); [| apply int64_unsigned_ge_0 | apply Hsrc].
      apply andb_true_intro.
      split; [| reflexivity].
      apply int64_eq_iff.
      rewrite ! Byte.repr_unsigned, Int64.repr_unsigned, Int64.repr_unsigned.
      rewrite ! int64_sign_int_extract_32_eq, int64_sign_int16_extract_16_eq,  int64_unsign_byte_extract_8_eq.
      bsolver.
  }
  clear Halu64.
  do 7 ((*          BPF_ALU64           *)
    destruct (_ =? _)%Z eqn: Halu64 in Hdecode;
    try(
        destruct (_ && _)%bool eqn:Halu642 in Hdecode; [| inversion Hdecode];
        rewrite ! Bool.andb_true_iff in *;
        destruct Halu642 as (Hb1 & Hb2);
        rewrite ! Nat.eqb_eq, Z.eqb_eq, int16_eq_iff in *;
        inversion Hdecode; subst;
        simpl in Halu64;
        unfold Int16.zero in Hb2;
        rewrite <- Halu64 at 1;
        rewrite <- Hb1 at 3;
        rewrite <- Hb2;
        simpl in *;
        rewrite Hnth;
        unfold_bin;
        erewrite bpf_reg_decode_eq with (r := dst); [| apply int64_unsigned_ge_0 | apply Hdst];
        apply andb_true_intro;
        split; [| reflexivity];
        apply int64_eq_iff;
        rewrite Z2Nat.id; [| apply int64_unsigned_ge_0];
        rewrite ! Byte.repr_unsigned, Int64.repr_unsigned, Int64.repr_unsigned;
        rewrite ! int64_sign_int_extract_32_eq, int64_sign_int16_extract_16_eq,  int64_unsign_byte_extract_8_eq;
        bsolver
    );
    clear Halu64;
    destruct (_ =? _)%Z eqn: Halu64 in Hdecode;
    try(
      destruct (_ && _)%bool eqn:Halu642 in Hdecode; [| inversion Hdecode];
      rewrite ! Bool.andb_true_iff in *;
      destruct Halu642 as (Hb1 & Hb2);
      rewrite ! int_eq_iff, Z.eqb_eq, int16_eq_iff in *;
      inversion Hdecode; subst;
      simpl in Halu64;
      unfold Int16.zero in Hb2;
      unfold Int.zero in Hb1;
      rewrite <- Halu64 at 1;
      rewrite <- Hb1;
      rewrite <- Hb2;
      simpl in *;
      rewrite Hnth;
      unfold_bin;
      erewrite bpf_reg_decode_eq with (r := dst); [| apply int64_unsigned_ge_0 | apply Hdst];
      erewrite bpf_reg_decode_eq with (r := src); [| apply int64_unsigned_ge_0 | apply Hsrc];
      apply andb_true_intro;
      split; [| reflexivity];
      apply int64_eq_iff;
      rewrite ! Byte.repr_unsigned, Int64.repr_unsigned, Int64.repr_unsigned;
      rewrite ! int64_sign_int_extract_32_eq, int64_sign_int16_extract_16_eq,  int64_unsign_byte_extract_8_eq;
      bsolver
    );
    clear Halu64
  ).
  destruct (_ =? _)%Z eqn: Hneg64 in Hdecode.
  {(*          BPF_NEG64           *)
    destruct (_ && _)%bool eqn:Hneg642 in Hdecode; [| inversion Hdecode].
    rewrite ! Bool.andb_true_iff in *.
    destruct Hneg642 as ((Hb1 & Hb2) & Hb3).
    rewrite ! Nat.eqb_eq, int16_eq_iff, int_eq_iff, Z.eqb_eq in *.
    inversion Hdecode; subst.
    simpl in Hneg64.
    rewrite <- Hneg64.
    rewrite <- Hb1 at 3.
    unfold Int16.zero in Hb2.
    unfold Int.zero in Hb3.
    rewrite <- Hb2.
    rewrite <- Hb3.
    simpl in *.
    rewrite Hnth.
    unfold_bin.
    erewrite bpf_reg_decode_eq with (r := dst); [| apply int64_unsigned_ge_0 | apply Hdst].
    apply andb_true_intro.
    split; [| reflexivity].
    apply int64_eq_iff.
    rewrite Z2Nat.id; [| apply int64_unsigned_ge_0].
    rewrite ! Byte.repr_unsigned, Int64.repr_unsigned, Int64.repr_unsigned.
    rewrite ! int64_sign_int_extract_32_eq, int64_sign_int16_extract_16_eq,  int64_unsign_byte_extract_8_eq.
    bsolver.
  }
  clear Hneg64.
  do 4 ((*          BPF_ALU64           *)
    destruct (_ =? _)%Z eqn: Halu64 in Hdecode;
    try(
        destruct (_ && _)%bool eqn:Halu642 in Hdecode; [| inversion Hdecode];
        rewrite ! Bool.andb_true_iff in *;
        destruct Halu642 as (Hb1 & Hb2);
        rewrite ! Nat.eqb_eq, Z.eqb_eq, int16_eq_iff in *;
        inversion Hdecode; subst;
        simpl in Halu64;
        unfold Int16.zero in Hb2;
        rewrite <- Halu64 at 1;
        rewrite <- Hb1 at 3;
        rewrite <- Hb2;
        simpl in *;
        rewrite Hnth;
        unfold_bin;
        erewrite bpf_reg_decode_eq with (r := dst); [| apply int64_unsigned_ge_0 | apply Hdst];
        apply andb_true_intro;
        split; [| reflexivity];
        apply int64_eq_iff;
        rewrite Z2Nat.id; [| apply int64_unsigned_ge_0];
        rewrite ! Byte.repr_unsigned, Int64.repr_unsigned, Int64.repr_unsigned;
        rewrite ! int64_sign_int_extract_32_eq, int64_sign_int16_extract_16_eq,  int64_unsign_byte_extract_8_eq;
        bsolver
    );
    clear Halu64;
    destruct (_ =? _)%Z eqn: Halu64 in Hdecode;
    try(
      destruct (_ && _)%bool eqn:Halu642 in Hdecode; [| inversion Hdecode];
      rewrite ! Bool.andb_true_iff in *;
      destruct Halu642 as (Hb1 & Hb2);
      rewrite ! int_eq_iff, Z.eqb_eq, int16_eq_iff in *;
      inversion Hdecode; subst;
      simpl in Halu64;
      unfold Int16.zero in Hb2;
      unfold Int.zero in Hb1;
      rewrite <- Halu64 at 1;
      rewrite <- Hb1;
      rewrite <- Hb2;
      simpl in *;
      rewrite Hnth;
      unfold_bin;
      erewrite bpf_reg_decode_eq with (r := dst); [| apply int64_unsigned_ge_0 | apply Hdst];
      erewrite bpf_reg_decode_eq with (r := src); [| apply int64_unsigned_ge_0 | apply Hsrc];
      apply andb_true_intro;
      split; [| reflexivity];
      apply int64_eq_iff;
      rewrite ! Byte.repr_unsigned, Int64.repr_unsigned, Int64.repr_unsigned;
      rewrite ! int64_sign_int_extract_32_eq, int64_sign_int16_extract_16_eq,  int64_unsign_byte_extract_8_eq;
      bsolver
    );
    clear Halu64
  ).
  destruct (_ =? _)%Z eqn: Hhor64 in Hdecode.
  {(*          BPF_HOR64_IMM           *)
    destruct (_ && _)%bool eqn:Hhor642 in Hdecode; [| inversion Hdecode].
    rewrite ! Bool.andb_true_iff in *.
    destruct Hhor642 as (Hb1 & Hb2).
    rewrite ! Nat.eqb_eq, Z.eqb_eq, int16_eq_iff in *.
    inversion Hdecode; subst.
    simpl in Hhor64.
    unfold Int16.zero in Hb2.
    rewrite <- Hhor64 at 1.
    rewrite <- Hb1 at 3.
    rewrite <- Hb2.
    simpl in *.
    rewrite Hnth.
    unfold_bin.
    erewrite bpf_reg_decode_eq with (r := dst); [| apply int64_unsigned_ge_0 | apply Hdst].
    apply andb_true_intro.
    split; [| reflexivity].
    apply int64_eq_iff.
    rewrite Z2Nat.id; [| apply int64_unsigned_ge_0].
    rewrite ! Byte.repr_unsigned, Int64.repr_unsigned, Int64.repr_unsigned.
    rewrite ! int64_sign_int_extract_32_eq, int64_sign_int16_extract_16_eq,  int64_unsign_byte_extract_8_eq.
    bsolver.
  }
  clear Hhor64.
  do 12 ((*          BPF_PQR           *)
    destruct (_ =? _)%Z eqn: Hpqr in Hdecode;
    try(
        destruct (_ && _)%bool eqn:Hpqr2 in Hdecode; [| inversion Hdecode];
        rewrite ! Bool.andb_true_iff in *;
        destruct Hpqr2 as (Hb1 & Hb2);
        rewrite ! Nat.eqb_eq, Z.eqb_eq, int16_eq_iff in *;
        inversion Hdecode; subst;
        simpl in Hpqr;
        unfold Int16.zero in Hb2;
        rewrite <- Hpqr at 1;
        rewrite <- Hb1 at 3;
        rewrite <- Hb2;
        simpl in *;
        rewrite Hnth;
        unfold_bin;
        erewrite bpf_reg_decode_eq with (r := dst); [| apply int64_unsigned_ge_0 | apply Hdst];
        apply andb_true_intro;
        split; [| reflexivity];
        apply int64_eq_iff;
        rewrite Z2Nat.id; [| apply int64_unsigned_ge_0];
        rewrite ! Byte.repr_unsigned, Int64.repr_unsigned, Int64.repr_unsigned;
        rewrite ! int64_sign_int_extract_32_eq, int64_sign_int16_extract_16_eq,  int64_unsign_byte_extract_8_eq;
        bsolver
    );
    clear Hpqr;
    destruct (_ =? _)%Z eqn: Hpqr in Hdecode;
    try(
      destruct (_ && _)%bool eqn:Hpqr2 in Hdecode; [| inversion Hdecode];
      rewrite ! Bool.andb_true_iff in *;
      destruct Hpqr2 as (Hb1 & Hb2);
      rewrite ! int_eq_iff, Z.eqb_eq, int16_eq_iff in *;
      inversion Hdecode; subst;
      simpl in Hpqr;
      unfold Int16.zero in Hb2;
      unfold Int.zero in Hb1;
      rewrite <- Hpqr at 1;
      rewrite <- Hb1;
      rewrite <- Hb2;
      simpl in *;
      rewrite Hnth;
      unfold_bin;
      erewrite bpf_reg_decode_eq with (r := dst); [| apply int64_unsigned_ge_0 | apply Hdst];
      erewrite bpf_reg_decode_eq with (r := src); [| apply int64_unsigned_ge_0 | apply Hsrc];
      apply andb_true_intro;
      split; [| reflexivity];
      apply int64_eq_iff;
      rewrite ! Byte.repr_unsigned, Int64.repr_unsigned, Int64.repr_unsigned;
      rewrite ! int64_sign_int_extract_32_eq, int64_sign_int16_extract_16_eq,  int64_unsign_byte_extract_8_eq;
      bsolver
    );
    clear Hpqr
  ).
  destruct (_ =? _)%Z eqn: Hja in Hdecode.
  {(*          BPF_JA           *)
      destruct (_ && _)%bool eqn:Hja2 in Hdecode; [| inversion Hdecode].
      rewrite ! Bool.andb_true_iff in *.
      destruct Hja2 as ((Hb1 & Hb2) & Hb3).
      rewrite ! int_eq_iff, Z.eqb_eq, Nat.eqb_eq in *.
      inversion Hdecode; subst.
      simpl in Hja.
      unfold Int16.zero in Hb2.
      unfold Int.zero in Hb3.
      rewrite <- Hja at 1.
      rewrite <- Hb1 at 4.
      rewrite <- Hb2 at 3.
      rewrite <- Hb3.
      simpl in *.
      rewrite Hnth.
      unfold_bin.
      apply andb_true_intro.
      split; [| reflexivity].
      apply int64_eq_iff.
      rewrite Z2Nat.id; [| apply int64_unsigned_ge_0].
      rewrite Z2Nat.id; [| apply int64_unsigned_ge_0].
      rewrite ! Byte.repr_unsigned, Int64.repr_unsigned, Int64.repr_unsigned.
      rewrite ! int64_sign_int_extract_32_eq, int64_sign_int16_extract_16_eq,  int64_unsign_byte_extract_8_eq.
      bsolver.
  }
  clear Hja.
  do 11 ((*          BPF_JUMP           *)
    destruct (_ =? _)%Z eqn: Hjump in Hdecode;
    try (
      destruct (_ =? _)%nat eqn:Hsrc2; [| inversion Hdecode];
      inversion Hdecode; subst;
      rewrite ! Z.eqb_eq, Nat.eqb_eq in *;
      simpl in Hjump;
      unfold Int.zero in Hsrc2;
      rewrite <- Hjump;
      rewrite <- Hsrc2 at 3;
      simpl in *;
      rewrite Hnth;
      unfold_bin;
      erewrite bpf_reg_decode_eq with (r := dst); [| apply int64_unsigned_ge_0 | apply Hdst];
      apply andb_true_intro;
      split; [| reflexivity];
      apply int64_eq_iff;
      rewrite Z2Nat.id; [| apply int64_unsigned_ge_0];
      rewrite ! Byte.repr_unsigned, Int64.repr_unsigned, Int64.repr_unsigned;
      rewrite ! int64_sign_int_extract_32_eq, int64_sign_int16_extract_16_eq,  int64_unsign_byte_extract_8_eq;
      bsolver
    );
    clear Hjump;
    destruct (_ =? _)%Z eqn: Hjump in Hdecode;
    try(
      destruct (Int.eq _ _)%nat eqn:Himm; [| inversion Hdecode];
      inversion Hdecode; subst;
      rewrite ! Z.eqb_eq, int_eq_iff in *;
      simpl in Hjump;
      unfold Int.zero in Himm;
      rewrite <- Hjump;
      rewrite <- Himm;
      simpl in *;
      rewrite Hnth;
      unfold_bin;
      erewrite bpf_reg_decode_eq with (r := dst); [| apply int64_unsigned_ge_0 | apply Hdst];
      erewrite bpf_reg_decode_eq with (r := src); [| apply int64_unsigned_ge_0 | apply Hsrc];
      apply andb_true_intro;
      split; [| reflexivity];
      apply int64_eq_iff;
      rewrite ! Byte.repr_unsigned, Int64.repr_unsigned, Int64.repr_unsigned;
      rewrite ! int64_sign_int_extract_32_eq, int64_sign_int16_extract_16_eq,  int64_unsign_byte_extract_8_eq;
      bsolver
    );
    clear Hjump
  ).
  do 2 ((*          BPF_CALL           *)
    destruct (_ =? _)%Z eqn: Hcall in Hdecode;
    try(
      destruct (_ && _)%bool eqn:Hcall2 in Hdecode; [| inversion Hdecode];
      rewrite ! Bool.andb_true_iff in *;
      destruct Hcall2 as (Hb1 & Hb2);
      rewrite ! int16_eq_iff, Z.eqb_eq, Nat.eqb_eq in *;
      inversion Hdecode; subst;
      simpl in Hcall;
      unfold Int16.zero in Hb2;
      rewrite <- Hcall;
      rewrite <- Hb1 at 3;
      rewrite <- Hb2;
      simpl in *;
      rewrite Hnth;
      unfold_bin;
      erewrite bpf_reg_decode_eq with (r := src); [| apply int64_unsigned_ge_0 | apply Hsrc];
      apply andb_true_intro;
      split; [| reflexivity];
      apply int64_eq_iff;
      rewrite Z2Nat.id; [| apply int64_unsigned_ge_0];
      rewrite ! Byte.repr_unsigned, Int64.repr_unsigned, Int64.repr_unsigned;
      rewrite ! int64_sign_int_extract_32_eq, int64_sign_int16_extract_16_eq,  int64_unsign_byte_extract_8_eq;
      bsolver
    );
    clear Hcall
  ).
  destruct (_ =? _)%Z eqn: Hexit in Hdecode.
  {
    destruct (_ && _)%bool eqn:Hexit2 in Hdecode; [| inversion Hdecode].
    rewrite ! Bool.andb_true_iff in *.
    destruct Hexit2 as (((Hb1 & Hb2) & Hb3) & Hb4).
    rewrite ! int_eq_iff, int16_eq_iff, Z.eqb_eq, Nat.eqb_eq in *.
    inversion Hdecode; subst.
    simpl in Hexit.
    unfold Int16.zero in Hb2.
    unfold Int.zero in Hb4.
    rewrite <- Hexit.
    rewrite <- Hb1 at 4.
    rewrite <- Hb2.
    rewrite <- Hb4.
    rewrite <- Hb3 at 3.
    simpl in *.
    rewrite Hnth.
    unfold_bin.
    apply andb_true_intro.
    split; [| reflexivity].
    apply int64_eq_iff.
    rewrite Z2Nat.id; [| apply int64_unsigned_ge_0].
    rewrite Z2Nat.id; [| apply int64_unsigned_ge_0].
    rewrite ! Byte.repr_unsigned, Int64.repr_unsigned, Int64.repr_unsigned.
    rewrite ! int64_sign_int_extract_32_eq, int64_sign_int16_extract_16_eq,  int64_unsign_byte_extract_8_eq.
    bsolver.
  }
  inversion Hdecode.
Qed.










