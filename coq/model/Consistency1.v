From Coq Require Import ZArith List Lia.
From compcert.lib Require Import Integers Maps Zbits.
From compcert.common Require Import Memory AST.
From bpf.model Require Import ebpf rBPFCommType rBPFSyntax MyTactic.
From bpf.model Require Import rBPFDecoder rBPFEncoder BitfieldLemma BinSolver.

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
(*       BPF_LD_IMM       *)
  - destruct nth_error as [ins |] eqn: Hnth; [| inversion HL].
    rewrite Bool.andb_true_iff in HL.
    destruct HL as (Hins & HL).
    destruct l as [| h0 l0]; [inversion HL |].
    destruct nth_error as [ins0 |] eqn: Hnth0 in HL; [| inversion HL].
    rewrite Bool.andb_true_iff in HL.
    destruct HL as (Hins0 & _).
    apply Int64.same_if_eq in Hins, Hins0.
    subst. unfold_bin.
    bsolver.
    change (Byte.unsigned (Byte.repr (Int64.unsigned (Int64.repr (Byte.unsigned (Byte.repr 24))))) =? 24) with true.
    simpl.
    rewrite Hnth0.
    + bsolver.
      rewrite bpf_ireg_nat_trans_cons.
      rewrite int_repr_int64_repr_cons.
      rewrite int_repr_int64_repr_cons.
      reflexivity.
    + fold Int64.zero.
      rewrite Int64.size_zero.
      lia.
    + unfold Int64.size, Zsize.
      rewrite Int64.unsigned_repr; [lia |].
      unfold Int64.max_unsigned.
      simpl.
      lia.
    + rewrite bpf_ireg_to_nat_size_le4.
      lia.
    + rewrite Byte.unsigned_repr.
      * unfold Int64.size, Zsize. 
        rewrite Int64.unsigned_repr;
        [ simpl; lia | unfold Int64.max_unsigned; simpl; lia ].
      * unfold Byte.max_unsigned.
        simpl.
        lia.
(*       BPF_LDX       *)
  - destruct nth_error as [ins |]; [| inversion HL].
    rewrite Bool.andb_true_iff in HL.
    destruct HL as (Hins & HL).
    destruct l as [| h0 l0]; [inversion HL |].
    destruct nth_error as [ins0 |] in HL; [| inversion HL].
    rewrite Bool.andb_true_iff in HL.
    destruct HL as (Hins0 & _).
    apply Int64.same_if_eq in Hins, Hins0.
    unfold rbpf_decoder_one.
    subst.
    bsolver.
    rewrite byte_int64_eq.
    destruct m; simpl; rewrite bpf_ireg_nat_trans_cons;
    rewrite bpf_ireg_nat_trans_cons; rewrite int16_int64_eq;
    reflexivity.
    + destruct m; lia.
    + rewrite int64_size_int16_unsign_le16.
      lia.
    + rewrite bpf_ireg_to_nat_size_le4.
      lia.
    + rewrite bpf_ireg_to_nat_size_le4.
      lia.
    + destruct m; rewrite int64_size_byte_unsign_le8; lia.
(*       BPF_ST       *)
  - destruct s as [SOi | SOr] eqn: Hseq in HL, Hencode; simpl in HL.
    + destruct nth_error as [ins |]; [| inversion HL].
      rewrite Bool.andb_true_iff in HL.
      destruct HL as (Hins & HL).
      destruct l as [| h0 l0]; [inversion HL |].
      destruct nth_error as [ins0 |] in HL; [| inversion HL].
      rewrite Bool.andb_true_iff in HL.
      destruct HL as (Hins0 & _).
      apply Int64.same_if_eq in Hins, Hins0.
      unfold rbpf_decoder_one.
      subst.
      bsolver.
      rewrite byte_int64_eq.
      destruct m; simpl; 
      try (
        rewrite bpf_ireg_nat_trans_cons;
        rewrite Int64.unsigned_repr; [| unfold Int64.max_unsigned; simpl; lia];
        simpl;
        rewrite Int64.signed_repr; [| apply int64_range_int_range_unsign_le ];
        rewrite Int64.signed_repr; [| apply int64_range_int16_range_unsign_le ];
        rewrite Int.repr_unsigned, Int16.repr_unsigned;
        reflexivity ).
      * destruct m; lia.
      * apply int64_size_int16_unsign_le16.
      * unfold Int64.size, Zsize; rewrite Int64.unsigned_repr;
        [ simpl; lia | unfold Int64.max_unsigned; simpl; lia ].
      * apply bpf_ireg_to_nat_size_le4.
      * rewrite int64_size_byte_unsign_le8.
        lia.
    + destruct nth_error as [ins |]; [| inversion HL].
      rewrite Bool.andb_true_iff in HL.
      destruct HL as (Hins & HL).
      destruct l as [| h0 l0]; [inversion HL |].
      destruct nth_error as [ins0 |] in HL; [| inversion HL].
      rewrite Bool.andb_true_iff in HL.
      destruct HL as (Hins0 & _).
      apply Int64.same_if_eq in Hins, Hins0.
      unfold rbpf_decoder_one.
      subst.
      bsolver.
      rewrite byte_int64_eq.
      destruct m; simpl;
      try ( 
        rewrite bpf_ireg_nat_trans_cons;
        rewrite bpf_ireg_nat_trans_cons;
        rewrite Int64.signed_repr; [| apply int64_range_int16_range_unsign_le ];
        rewrite Int16.repr_unsigned;
        reflexivity ).
      * destruct m; lia.
      * apply int64_size_int16_unsign_le16.
      * apply bpf_ireg_to_nat_size_le4.
      * apply bpf_ireg_to_nat_size_le4.
      * rewrite int64_size_byte_unsign_le8.
        lia.
(*       BPF_ADD_STK       *)
  - destruct nth_error as [ins |]; [| inversion HL].
    rewrite Bool.andb_true_iff in HL.
    destruct HL as (Hins & HL).
    destruct l as [| h0 l0]; [inversion HL |].
    destruct nth_error as [ins0 |] in HL; [| inversion HL].
    rewrite Bool.andb_true_iff in HL.
    destruct HL as (Hins0 & _).
    apply Int64.same_if_eq in Hins, Hins0.
    unfold rbpf_decoder_one.
    subst.
    bsolver.
    rewrite byte_int64_eq.
    simpl.
    + rewrite Int64.unsigned_repr; [| unfold Int64.max_unsigned; simpl; lia ]. 
      simpl.
      rewrite Int64.signed_repr; [| apply int64_range_int_range_unsign_le ].
      rewrite Int.repr_unsigned.
      reflexivity.
    + lia.
    + unfold Int64.size.
      rewrite Int64.unsigned_repr;
      try (unfold Int64.max_unsigned); simpl; lia.
    + unfold Int64.size.
      rewrite Int64.unsigned_repr;
      try (unfold Int64.max_unsigned); simpl; lia.
    + unfold Int64.size.
      rewrite Int64.unsigned_repr;
      try (unfold Int64.max_unsigned); simpl; lia.
    + apply int64_size_byte_unsign_le8.
(*       BPF_ALU       *)
  - destruct s as [SOi | SOr] eqn: Hseq in HL, Hencode; simpl in HL.
    + destruct nth_error as [ins |]; [| inversion HL].
      rewrite Bool.andb_true_iff in HL.
      destruct HL as (Hins & HL).
      destruct l as [| h0 l0]; [inversion HL |].
      destruct nth_error as [ins0 |] in HL; [| inversion HL].
      rewrite Bool.andb_true_iff in HL.
      destruct HL as (Hins0 & _).
      apply Int64.same_if_eq in Hins, Hins0.
      unfold rbpf_decoder_one.
      subst.
      bsolver.
      rewrite byte_int64_eq.
      destruct b; simpl;
      try (
        rewrite bpf_ireg_nat_trans_cons;
        rewrite Int64.unsigned_repr; [| unfold Int64.max_unsigned; simpl; lia];
        simpl;
        rewrite Int64.signed_repr; [| apply int64_range_int_range_unsign_le ];
        rewrite Int.repr_unsigned;
        reflexivity ).
      * destruct b; lia.
      * unfold Int64.size, Zsize; rewrite Int64.unsigned_repr;
        [ simpl; lia | unfold Int64.max_unsigned; simpl; lia ].
      * unfold Int64.size, Zsize; rewrite Int64.unsigned_repr;
        [ simpl; lia | unfold Int64.max_unsigned; simpl; lia ].
      * apply bpf_ireg_to_nat_size_le4.
      * rewrite int64_size_byte_unsign_le8.
        lia.
    + destruct nth_error as [ins |]; [| inversion HL].
      rewrite Bool.andb_true_iff in HL.
      destruct HL as (Hins & HL).
      destruct l as [| h0 l0]; [inversion HL |].
      destruct nth_error as [ins0 |] in HL; [| inversion HL].
      rewrite Bool.andb_true_iff in HL.
      destruct HL as (Hins0 & _).
      apply Int64.same_if_eq in Hins, Hins0.
      unfold rbpf_decoder_one.
      subst.
      bsolver.
      rewrite byte_int64_eq.
      destruct b; simpl;
      try ( 
        rewrite bpf_ireg_nat_trans_cons;
        rewrite bpf_ireg_nat_trans_cons;
        reflexivity ).
      * destruct b; lia.
      * unfold Int64.size, Zsize; rewrite Int64.unsigned_repr;
        [ simpl; lia | unfold Int64.max_unsigned; simpl; lia ].
      * apply bpf_ireg_to_nat_size_le4.
      * apply bpf_ireg_to_nat_size_le4.
      * rewrite int64_size_byte_unsign_le8.
        lia.
(*       BPF_NEG32_REG       *)
  - destruct nth_error as [ins |]; [| inversion HL].
    rewrite Bool.andb_true_iff in HL.
    destruct HL as (Hins & HL).
    destruct l as [| h0 l0]; [inversion HL |].
    destruct nth_error as [ins0 |] in HL; [| inversion HL].
    rewrite Bool.andb_true_iff in HL.
    destruct HL as (Hins0 & _).
    apply Int64.same_if_eq in Hins, Hins0.
    unfold rbpf_decoder_one.
    subst.
    bsolver.
    rewrite byte_int64_eq.
    simpl.
    + rewrite bpf_ireg_nat_trans_cons.
      rewrite Int64.unsigned_repr; [| unfold Int64.max_unsigned; simpl; lia].
      simpl.
      reflexivity.
    + lia.
    + unfold Int64.size, Zsize; rewrite Int64.unsigned_repr;
      [ simpl; lia | unfold Int64.max_unsigned; simpl; lia ].
    + unfold Int64.size, Zsize; rewrite Int64.unsigned_repr;
      [ simpl; lia | unfold Int64.max_unsigned; simpl; lia ].
    + apply bpf_ireg_to_nat_size_le4.
    + rewrite int64_size_byte_unsign_le8.
      lia.
(*       BPF_LE       *)  
  - destruct nth_error as [ins |]; [| inversion HL].
    rewrite Bool.andb_true_iff in HL.
    destruct HL as (Hins & HL).
    destruct l as [| h0 l0]; [inversion HL |].
    destruct nth_error as [ins0 |] in HL; [| inversion HL].
    rewrite Bool.andb_true_iff in HL.
    destruct HL as (Hins0 & _).
    apply Int64.same_if_eq in Hins, Hins0.
    unfold rbpf_decoder_one.
    subst.
    bsolver.
    rewrite byte_int64_eq.
    simpl.
    + rewrite bpf_ireg_nat_trans_cons.
      rewrite Int64.unsigned_repr; [| unfold Int64.max_unsigned; simpl; lia].
      simpl.
      rewrite Int64.signed_repr; [| apply int64_range_int_range_unsign_le ].
      rewrite Int.repr_unsigned.
      reflexivity.
    + lia.
    + unfold Int64.size, Zsize; rewrite Int64.unsigned_repr;
      [ simpl; lia | unfold Int64.max_unsigned; simpl; lia ].
    + unfold Int64.size, Zsize; rewrite Int64.unsigned_repr;
      [ simpl; lia | unfold Int64.max_unsigned; simpl; lia ].
    + apply bpf_ireg_to_nat_size_le4.
    + rewrite int64_size_byte_unsign_le8.
      lia.
(*       BPF_BE       *)  
  - destruct nth_error as [ins |]; [| inversion HL].
    rewrite Bool.andb_true_iff in HL.
    destruct HL as (Hins & HL).
    destruct l as [| h0 l0]; [inversion HL |].
    destruct nth_error as [ins0 |] in HL; [| inversion HL].
    rewrite Bool.andb_true_iff in HL.
    destruct HL as (Hins0 & _).
    apply Int64.same_if_eq in Hins, Hins0.
    unfold rbpf_decoder_one.
    subst.
    bsolver.
    rewrite byte_int64_eq.
    simpl.
    + rewrite bpf_ireg_nat_trans_cons.
      rewrite Int64.unsigned_repr; [| unfold Int64.max_unsigned; simpl; lia].
      simpl.
      rewrite Int64.signed_repr; [| apply int64_range_int_range_unsign_le ].
      rewrite Int.repr_unsigned.
      reflexivity.
    + lia.
    + unfold Int64.size, Zsize; rewrite Int64.unsigned_repr;
      [ simpl; lia | unfold Int64.max_unsigned; simpl; lia ].
    + unfold Int64.size, Zsize; rewrite Int64.unsigned_repr;
      [ simpl; lia | unfold Int64.max_unsigned; simpl; lia ].
    + apply bpf_ireg_to_nat_size_le4.
    + rewrite int64_size_byte_unsign_le8.
      lia.
(*       BPF_ALU64       *)
  - destruct s as [SOi | SOr] eqn: Hseq in HL, Hencode; simpl in HL.
    + destruct nth_error as [ins |]; [| inversion HL].
      rewrite Bool.andb_true_iff in HL.
      destruct HL as (Hins & HL).
      destruct l as [| h0 l0]; [inversion HL |].
      destruct nth_error as [ins0 |] in HL; [| inversion HL].
      rewrite Bool.andb_true_iff in HL.
      destruct HL as (Hins0 & _).
      apply Int64.same_if_eq in Hins, Hins0.
      unfold rbpf_decoder_one.
      subst.
      bsolver.
      rewrite byte_int64_eq.
      destruct b; try ( 
        simpl; 
        try (
          rewrite bpf_ireg_nat_trans_cons;
          rewrite Int64.unsigned_repr; [| unfold Int64.max_unsigned; simpl; lia];
          simpl;
          rewrite Int64.signed_repr; [| apply int64_range_int_range_unsign_le ];
          rewrite Int.repr_unsigned;
          reflexivity )).
      * rewrite bpf_ireg_nat_trans_cons.
        rewrite Int64.unsigned_repr.
        -- rewrite Nat2Z.id.
           destruct b0; try (simpl;
           rewrite Int64.signed_repr; [| apply int64_range_int_range_unsign_le ];
           rewrite Int.repr_unsigned;
           reflexivity).
        -- destruct b0; unfold Int64.max_unsigned; simpl; lia.
      * destruct b; lia.
      * unfold Int64.size, Zsize; rewrite Int64.unsigned_repr;
        [ simpl; lia | unfold Int64.max_unsigned; simpl; lia ].
      * unfold Int64.size, Zsize; rewrite Int64.unsigned_repr;
        [ simpl; lia | unfold Int64.max_unsigned; simpl; lia ].
      * apply bpf_ireg_to_nat_size_le4.
      * rewrite int64_size_byte_unsign_le8.
        lia.
    + destruct nth_error as [ins |]; [| inversion HL].
      rewrite Bool.andb_true_iff in HL.
      destruct HL as (Hins & HL).
      destruct l as [| h0 l0]; [inversion HL |].
      destruct nth_error as [ins0 |] in HL; [| inversion HL].
      rewrite Bool.andb_true_iff in HL.
      destruct HL as (Hins0 & _).
      apply Int64.same_if_eq in Hins, Hins0.
      unfold rbpf_decoder_one.
      subst.
      bsolver.
      rewrite byte_int64_eq.
      destruct b; simpl;
      try ( 
        rewrite bpf_ireg_nat_trans_cons;
        rewrite bpf_ireg_nat_trans_cons;
        reflexivity ).
      * destruct b; lia.
      * unfold Int64.size, Zsize; rewrite Int64.unsigned_repr;
        [ simpl; lia | unfold Int64.max_unsigned; simpl; lia ].
      * apply bpf_ireg_to_nat_size_le4.
      * apply bpf_ireg_to_nat_size_le4.
      * rewrite int64_size_byte_unsign_le8.
        lia.
(*       BPF_NEG64_REG       *)
  - destruct nth_error as [ins |]; [| inversion HL].
    rewrite Bool.andb_true_iff in HL.
    destruct HL as (Hins & HL).
    destruct l as [| h0 l0]; [inversion HL |].
    destruct nth_error as [ins0 |] in HL; [| inversion HL].
    rewrite Bool.andb_true_iff in HL.
    destruct HL as (Hins0 & _).
    apply Int64.same_if_eq in Hins, Hins0.
    unfold rbpf_decoder_one.
    subst.
    bsolver.
    rewrite byte_int64_eq.
    simpl.
    + rewrite bpf_ireg_nat_trans_cons.
      rewrite Int64.unsigned_repr; [| unfold Int64.max_unsigned; simpl; lia].
      simpl.
      reflexivity.
    + lia.
    + unfold Int64.size, Zsize; rewrite Int64.unsigned_repr;
      [ simpl; lia | unfold Int64.max_unsigned; simpl; lia ].
    + unfold Int64.size, Zsize; rewrite Int64.unsigned_repr;
      [ simpl; lia | unfold Int64.max_unsigned; simpl; lia ].
    + apply bpf_ireg_to_nat_size_le4.
    + rewrite int64_size_byte_unsign_le8.
      lia.
(*       BPF_HOR64_IMM       *)
  - destruct nth_error as [ins |]; [| inversion HL].
    rewrite Bool.andb_true_iff in HL.
    destruct HL as (Hins & HL).
    destruct l as [| h0 l0]; [inversion HL |].
    destruct nth_error as [ins0 |] in HL; [| inversion HL].
    rewrite Bool.andb_true_iff in HL.
    destruct HL as (Hins0 & _).
    apply Int64.same_if_eq in Hins, Hins0.
    unfold rbpf_decoder_one.
    subst.
    bsolver.
    rewrite byte_int64_eq.
    simpl.
    + rewrite bpf_ireg_nat_trans_cons.
      rewrite Int64.unsigned_repr; [| unfold Int64.max_unsigned; simpl; lia].
      simpl.
      rewrite Int64.signed_repr; [| apply int64_range_int_range_unsign_le ].
      rewrite Int.repr_unsigned.
      reflexivity.
    + lia.
    + unfold Int64.size, Zsize; rewrite Int64.unsigned_repr;
      [ simpl; lia | unfold Int64.max_unsigned; simpl; lia ].
    + unfold Int64.size, Zsize; rewrite Int64.unsigned_repr;
      [ simpl; lia | unfold Int64.max_unsigned; simpl; lia ].
    + apply bpf_ireg_to_nat_size_le4.
    + rewrite int64_size_byte_unsign_le8.
      lia.
(*       BPF_PQR       *)
  - destruct s as [SOi | SOr] eqn: Hseq in HL, Hencode; simpl in HL.
    + destruct nth_error as [ins |]; [| inversion HL].
      rewrite Bool.andb_true_iff in HL.
      destruct HL as (Hins & HL).
      destruct l as [| h0 l0]; [inversion HL |].
      destruct nth_error as [ins0 |] in HL; [| inversion HL].
      rewrite Bool.andb_true_iff in HL.
      destruct HL as (Hins0 & _).
      apply Int64.same_if_eq in Hins, Hins0.
      unfold rbpf_decoder_one.
      subst.
      bsolver.
      rewrite byte_int64_eq.
      destruct p; simpl;
      try (
        rewrite bpf_ireg_nat_trans_cons;
        rewrite Int64.unsigned_repr; [| unfold Int64.max_unsigned; simpl; lia];
        simpl;
        rewrite Int64.signed_repr; [| apply int64_range_int_range_unsign_le ];
        rewrite Int.repr_unsigned;
        reflexivity ).
      * destruct p; lia.
      * unfold Int64.size, Zsize; rewrite Int64.unsigned_repr;
        [ simpl; lia | unfold Int64.max_unsigned; simpl; lia ].
      * unfold Int64.size, Zsize; rewrite Int64.unsigned_repr;
        [ simpl; lia | unfold Int64.max_unsigned; simpl; lia ].
      * apply bpf_ireg_to_nat_size_le4.
      * rewrite int64_size_byte_unsign_le8.
        lia.
    + destruct nth_error as [ins |]; [| inversion HL].
      rewrite Bool.andb_true_iff in HL.
      destruct HL as (Hins & HL).
      destruct l as [| h0 l0]; [inversion HL |].
      destruct nth_error as [ins0 |] in HL; [| inversion HL].
      rewrite Bool.andb_true_iff in HL.
      destruct HL as (Hins0 & _).
      apply Int64.same_if_eq in Hins, Hins0.
      unfold rbpf_decoder_one.
      subst.
      bsolver.
      rewrite byte_int64_eq.
      destruct p; simpl;
      try ( 
        rewrite bpf_ireg_nat_trans_cons;
        rewrite bpf_ireg_nat_trans_cons;
        reflexivity ).
      * destruct p; lia.
      * unfold Int64.size, Zsize; rewrite Int64.unsigned_repr;
        [ simpl; lia | unfold Int64.max_unsigned; simpl; lia ].
      * apply bpf_ireg_to_nat_size_le4.
      * apply bpf_ireg_to_nat_size_le4.
      * rewrite int64_size_byte_unsign_le8.
        lia.
(*       BPF_PQR64       *)
  - destruct s as [SOi | SOr] eqn: Hseq in HL, Hencode; simpl in HL.
    + destruct nth_error as [ins |]; [| inversion HL].
      rewrite Bool.andb_true_iff in HL.
      destruct HL as (Hins & HL).
      destruct l as [| h0 l0]; [inversion HL |].
      destruct nth_error as [ins0 |] in HL; [| inversion HL].
      rewrite Bool.andb_true_iff in HL.
      destruct HL as (Hins0 & _).
      apply Int64.same_if_eq in Hins, Hins0.
      unfold rbpf_decoder_one.
      subst.
      bsolver.
      rewrite byte_int64_eq.
      destruct p; simpl;
      try (
        rewrite bpf_ireg_nat_trans_cons;
        rewrite Int64.unsigned_repr; [| unfold Int64.max_unsigned; simpl; lia];
        simpl;
        rewrite Int64.signed_repr; [| apply int64_range_int_range_unsign_le ];
        rewrite Int.repr_unsigned;
        reflexivity ).
      * destruct p; lia.
      * unfold Int64.size, Zsize; rewrite Int64.unsigned_repr;
        [ simpl; lia | unfold Int64.max_unsigned; simpl; lia ].
      * unfold Int64.size, Zsize; rewrite Int64.unsigned_repr;
        [ simpl; lia | unfold Int64.max_unsigned; simpl; lia ].
      * apply bpf_ireg_to_nat_size_le4.
      * rewrite int64_size_byte_unsign_le8.
        lia.
    + destruct nth_error as [ins |]; [| inversion HL].
      rewrite Bool.andb_true_iff in HL.
      destruct HL as (Hins & HL).
      destruct l as [| h0 l0]; [inversion HL |].
      destruct nth_error as [ins0 |] in HL; [| inversion HL].
      rewrite Bool.andb_true_iff in HL.
      destruct HL as (Hins0 & _).
      apply Int64.same_if_eq in Hins, Hins0.
      unfold rbpf_decoder_one.
      subst.
      bsolver.
      rewrite byte_int64_eq.
      destruct p; simpl;
      try ( 
        rewrite bpf_ireg_nat_trans_cons;
        rewrite bpf_ireg_nat_trans_cons;
        reflexivity ).
      * destruct p; lia.
      * unfold Int64.size, Zsize; rewrite Int64.unsigned_repr;
        [ simpl; lia | unfold Int64.max_unsigned; simpl; lia ].
      * apply bpf_ireg_to_nat_size_le4.
      * apply bpf_ireg_to_nat_size_le4.
      * rewrite int64_size_byte_unsign_le8.
        lia.
(*       BPF_PQR2       *)
  - destruct s as [SOi | SOr] eqn: Hseq in HL, Hencode; simpl in HL.
    + destruct nth_error as [ins |]; [| inversion HL].
      rewrite Bool.andb_true_iff in HL.
      destruct HL as (Hins & HL).
      destruct l as [| h0 l0]; [inversion HL |].
      destruct nth_error as [ins0 |] in HL; [| inversion HL].
      rewrite Bool.andb_true_iff in HL.
      destruct HL as (Hins0 & _).
      apply Int64.same_if_eq in Hins, Hins0.
      unfold rbpf_decoder_one.
      subst.
      bsolver.
      rewrite byte_int64_eq.
      destruct p; simpl;
      try (
        rewrite bpf_ireg_nat_trans_cons;
        rewrite Int64.unsigned_repr; [| unfold Int64.max_unsigned; simpl; lia];
        simpl;
        rewrite Int64.signed_repr; [| apply int64_range_int_range_unsign_le ];
        rewrite Int.repr_unsigned;
        reflexivity ).
      * destruct p; lia.
      * unfold Int64.size, Zsize; rewrite Int64.unsigned_repr;
        [ simpl; lia | unfold Int64.max_unsigned; simpl; lia ].
      * unfold Int64.size, Zsize; rewrite Int64.unsigned_repr;
        [ simpl; lia | unfold Int64.max_unsigned; simpl; lia ].
      * apply bpf_ireg_to_nat_size_le4.
      * rewrite int64_size_byte_unsign_le8.
        lia.
    + destruct nth_error as [ins |]; [| inversion HL].
      rewrite Bool.andb_true_iff in HL.
      destruct HL as (Hins & HL).
      destruct l as [| h0 l0]; [inversion HL |].
      destruct nth_error as [ins0 |] in HL; [| inversion HL].
      rewrite Bool.andb_true_iff in HL.
      destruct HL as (Hins0 & _).
      apply Int64.same_if_eq in Hins, Hins0.
      unfold rbpf_decoder_one.
      subst.
      bsolver.
      rewrite byte_int64_eq.
      destruct p; simpl;
      try ( 
        rewrite bpf_ireg_nat_trans_cons;
        rewrite bpf_ireg_nat_trans_cons;
        reflexivity ).
      * destruct p; lia.
      * unfold Int64.size, Zsize; rewrite Int64.unsigned_repr;
        [ simpl; lia | unfold Int64.max_unsigned; simpl; lia ].
      * apply bpf_ireg_to_nat_size_le4.
      * apply bpf_ireg_to_nat_size_le4.
      * rewrite int64_size_byte_unsign_le8.
        lia.
(*       BPF_JA       *)
  - destruct nth_error as [ins |]; [| inversion HL].
    rewrite Bool.andb_true_iff in HL.
    destruct HL as (Hins & HL).
    destruct l as [| h0 l0]; [inversion HL |].
    destruct nth_error as [ins0 |] in HL; [| inversion HL].
    rewrite Bool.andb_true_iff in HL.
    destruct HL as (Hins0 & _).
    apply Int64.same_if_eq in Hins, Hins0.
    unfold rbpf_decoder_one.
    subst.
    bsolver.
    rewrite byte_int64_eq.
    simpl.
    + rewrite Int64.unsigned_repr; [| unfold Int64.max_unsigned; simpl; lia].
      simpl.
      rewrite Int64.signed_repr; [| apply int64_range_int16_range_unsign_le ].
      rewrite Int16.repr_unsigned.
      reflexivity.
    + lia.
    + apply int64_size_int16_unsign_le16.
    + unfold Int64.size, Zsize; rewrite Int64.unsigned_repr;
      [ simpl; lia | unfold Int64.max_unsigned; simpl; lia ].
    + unfold Int64.size, Zsize; rewrite Int64.unsigned_repr;
      [ simpl; lia | unfold Int64.max_unsigned; simpl; lia ].
    + rewrite int64_size_byte_unsign_le8.
      lia.
(*       BPF_JUMP       *)
  - destruct s as [SOi | SOr] eqn: Hseq in HL, Hencode; simpl in HL.
    + destruct nth_error as [ins |]; [| inversion HL].
      rewrite Bool.andb_true_iff in HL.
      destruct HL as (Hins & HL).
      destruct l as [| h0 l0]; [inversion HL |].
      destruct nth_error as [ins0 |] in HL; [| inversion HL].
      rewrite Bool.andb_true_iff in HL.
      destruct HL as (Hins0 & _).
      apply Int64.same_if_eq in Hins, Hins0.
      unfold rbpf_decoder_one.
      subst.
      bsolver.
      rewrite byte_int64_eq.
      destruct c; simpl;
      try (
        rewrite bpf_ireg_nat_trans_cons;
        rewrite Int64.unsigned_repr; [| unfold Int64.max_unsigned; simpl; lia];
        simpl;
        rewrite Int64.signed_repr; [| apply int64_range_int_range_unsign_le ];
        rewrite Int64.signed_repr; [| apply int64_range_int16_range_unsign_le ];
        rewrite Int.repr_unsigned, Int16.repr_unsigned;
        reflexivity ).
      * destruct c; lia.
      * apply int64_size_int16_unsign_le16.
      * unfold Int64.size, Zsize; rewrite Int64.unsigned_repr;
        [ simpl; lia | unfold Int64.max_unsigned; simpl; lia ].
      * apply bpf_ireg_to_nat_size_le4.
      * rewrite int64_size_byte_unsign_le8.
        lia.
    + destruct nth_error as [ins |]; [| inversion HL].
      rewrite Bool.andb_true_iff in HL.
      destruct HL as (Hins & HL).
      destruct l as [| h0 l0]; [inversion HL |].
      destruct nth_error as [ins0 |] in HL; [| inversion HL].
      rewrite Bool.andb_true_iff in HL.
      destruct HL as (Hins0 & _).
      apply Int64.same_if_eq in Hins, Hins0.
      unfold rbpf_decoder_one.
      subst.
      bsolver.
      rewrite byte_int64_eq.
      destruct c; simpl;
      try ( 
        rewrite bpf_ireg_nat_trans_cons;
        rewrite bpf_ireg_nat_trans_cons;
        rewrite Int64.signed_repr; [| apply int64_range_int16_range_unsign_le ];
        rewrite Int16.repr_unsigned;
        reflexivity ).
      * destruct c; lia.
      * apply int64_size_int16_unsign_le16.
      * apply bpf_ireg_to_nat_size_le4.
      * apply bpf_ireg_to_nat_size_le4.
      * rewrite int64_size_byte_unsign_le8.
        lia.
(*       BPF_CALL_REG       *)
  - destruct nth_error as [ins |]; [| inversion HL].
    rewrite Bool.andb_true_iff in HL.
    destruct HL as (Hins & HL).
    destruct l as [| h0 l0]; [inversion HL |].
    destruct nth_error as [ins0 |] in HL; [| inversion HL].
    rewrite Bool.andb_true_iff in HL.
    destruct HL as (Hins0 & _).
    apply Int64.same_if_eq in Hins, Hins0.
    unfold rbpf_decoder_one.
    subst.
    bsolver.
    rewrite byte_int64_eq.
    simpl.
    + rewrite Int64.unsigned_repr; [| unfold Int64.max_unsigned; simpl; lia].
      rewrite bpf_ireg_nat_trans_cons.
      simpl.
      rewrite Int64.signed_repr; [| apply int64_range_int_range_unsign_le ].
      rewrite Int.repr_unsigned.
      reflexivity.
    + lia.
    + unfold Int64.size, Zsize; rewrite Int64.unsigned_repr;
      [ simpl; lia | unfold Int64.max_unsigned; simpl; lia ].
    + apply bpf_ireg_to_nat_size_le4.
    + unfold Int64.size, Zsize; rewrite Int64.unsigned_repr;
      [ simpl; lia | unfold Int64.max_unsigned; simpl; lia ].
    + rewrite int64_size_byte_unsign_le8.
      lia.
(*       BPF_CALL_IMM       *)
  - destruct nth_error as [ins |]; [| inversion HL].
    rewrite Bool.andb_true_iff in HL.
    destruct HL as (Hins & HL).
    destruct l as [| h0 l0]; [inversion HL |].
    destruct nth_error as [ins0 |] in HL; [| inversion HL].
    rewrite Bool.andb_true_iff in HL.
    destruct HL as (Hins0 & _).
    apply Int64.same_if_eq in Hins, Hins0.
    unfold rbpf_decoder_one.
    subst.
    bsolver.
    rewrite byte_int64_eq.
    simpl.
    + rewrite Int64.unsigned_repr; [| unfold Int64.max_unsigned; simpl; lia].
      rewrite bpf_ireg_nat_trans_cons.
      simpl.
      rewrite Int64.signed_repr; [| apply int64_range_int_range_unsign_le ].
      rewrite Int.repr_unsigned.
      reflexivity.
    + lia.
    + unfold Int64.size, Zsize; rewrite Int64.unsigned_repr;
      [ simpl; lia | unfold Int64.max_unsigned; simpl; lia ].
    + apply bpf_ireg_to_nat_size_le4.
    + unfold Int64.size, Zsize; rewrite Int64.unsigned_repr;
      [ simpl; lia | unfold Int64.max_unsigned; simpl; lia ].
    + rewrite int64_size_byte_unsign_le8.
      lia.
(*       BPF_EXIT       *)
  - destruct nth_error as [ins |]; [| inversion HL].
    rewrite Bool.andb_true_iff in HL.
    destruct HL as (Hins & HL).
    destruct l as [| h0 l0]; [inversion HL |].
    destruct nth_error as [ins0 |] in HL; [| inversion HL].
    rewrite Bool.andb_true_iff in HL.
    destruct HL as (Hins0 & _).
    apply Int64.same_if_eq in Hins, Hins0.
    unfold rbpf_decoder_one.
    subst.
    bsolver.
Qed.

