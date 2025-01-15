From Coq Require Import ZArith List Lia.
From compcert.lib Require Import Integers Maps Zbits.
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
  

Global Hint Resolve int64_size_int_unsign_le32 : int_size.
Global Hint Resolve int64_size_int16_unsign_le16 : int16_size.

Ltac bsolver := unfold_bin; simpl; repeat bin_solver; auto with int_size.


Lemma int64_range_int_range_sign_le: forall i,
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
  - apply int64_range_int_range_sign_le.
Qed.

Lemma simple_memory_op : forall m,
  Byte.unsigned
      (Byte.repr
         (Int64.unsigned
            (Int64.repr
               (Byte.unsigned
                  (Byte.repr
                     match m with
                     | Mint8unsigned => 113
                     | Mint16unsigned => 105
                     | Mint32 => 97
                     | Mint64 => 121
                     | _ => 0
                     end))))) = ( match m with
                                | Mint8unsigned => 113
                                | Mint16unsigned => 105
                                | Mint32 => 97
                                | Mint64 => 121
                                | _ => 0
                                end).
Proof.
  intros.
  destruct m; 
  try (rewrite Byte.unsigned_repr; rewrite Int64.unsigned_repr; rewrite Byte.unsigned_repr;
       try ( unfold Byte.max_unsigned, Int64.max_unsigned; simpl; lia) 
  ).
Qed.

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
    + bsolver.
      rewrite bpf_ireg_nat_trans_cons.
      rewrite int_repr_int64_repr_cons.
      rewrite int_repr_int64_repr_cons.
      reflexivity.
    + fold Int64.zero.
      rewrite Int64.size_zero.
      lia.
    + unfold Int64.size.
      rewrite Int64.unsigned_repr.
      * unfold Zsize.
        lia.
      * unfold Int64.max_unsigned.
        simpl.
        lia.
    + destruct b;
      try ( simpl; unfold Int64.size, Zsize; rewrite Int64.unsigned_repr;
      [ simpl; lia | unfold Int64.max_unsigned; simpl; lia ] ).
    + rewrite Byte.unsigned_repr.
      * unfold Int64.size.
        rewrite Int64.unsigned_repr.
        -- unfold Zsize.
           simpl.
           lia.
        -- unfold Int64.max_unsigned.
           simpl.
           lia.
      * unfold Byte.max_unsigned.
        simpl.
        lia.
  - destruct nth_error as [ins |] eqn: Hnth; [| inversion HL].
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
    rewrite simple_memory_op.
    destruct m; simpl.
    + rewrite bpf_ireg_nat_trans_cons.
      rewrite bpf_ireg_nat_trans_cons.





      bsolver.
      reflexivity.
    + fold Int64.zero.
      rewrite Int64.size_zero.
      lia.
    + unfold Int64.size.
      rewrite Int64.unsigned_repr.
      * unfold Zsize.
        lia.
      * unfold Int64.max_unsigned.
        simpl.
        lia.
    + destruct b;
      try ( simpl; unfold Int64.size, Zsize; rewrite Int64.unsigned_repr;
      [ simpl; lia | unfold Int64.max_unsigned; simpl; lia ] ).
    + rewrite Byte.unsigned_repr.
      * unfold Int64.size.
        rewrite Int64.unsigned_repr.
        -- unfold Zsize.
           simpl.
           lia.
        -- unfold Int64.max_unsigned.
           simpl.
           lia.
      * unfold Byte.max_unsigned.
        simpl.
        lia.

      

 simpl; unfold Int64.size, Zsize; rewrite Int64.unsigned_repr; 
      [ lia | unfold Int64.max_unsigned; simpl; lia ].


apply Int64.bits_size_3; [lia |].
      intros n Hrange.
      rewrite Int64.testbit_repr; [| lia].
      apply Ztestbit_above with (n := (bpf_ireg_to_nat b)).
      * unfold two_power_nat; simpl.
        destruct b; simpl; lia.
      * destruct b; simpl.
        -- destruct Hrange as [Hlow Hhigh].
           try lia.
        -- 


        
      
      match goal with
      | |- context[Int64.unsigned_bitfield_extract ?p0 ?w0 (Int64.bitfield_insert ?p0 ?w0 ?i0 ?v0)] =>
           erewrite unsigned_bitfield_extract_bitfield_insert_same_1 with (pos := p0) (width := w0)
  end.

 (*
  match goal with


  | |- context[Int64.unsigned_bitfield_extract ?p0 ?w0 (Int64.bitfield_insert ?p0 ?w0 ?i0 ?v0)] =>
    erewrite unsigned_bitfield_extract_bitfield_insert_same_1 with (pos := p0) (width := w0)
  end.*)

Admitted.