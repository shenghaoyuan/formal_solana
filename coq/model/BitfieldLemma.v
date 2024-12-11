From Coq Require Import List ZArith Lia.
From compcert.lib Require Import Integers Coqlib.

Open Scope Z_scope.

Lemma zle_true_iff:
  forall (x y : Z), x <= y <-> @eq bool (@proj_sumbool (Z.le x y) (Z.gt x y) (zle x y)) true.
Proof.
  intros.
  split; intro.
  - apply zle_true; auto.
  - destruct zle.
    + assumption.
    + inversion H.
Qed.

Lemma zle_false_iff:
  forall (x y : Z), x > y <-> @eq bool (@proj_sumbool (Z.le x y) (Z.gt x y) (zle x y)) false.
Proof.
  intros.
  split; intro.
  - apply zle_false; auto.
  - destruct zle.
    + inversion H.
    + assumption.
Qed.

Lemma zlt_true_iff:
  forall (x y : Z), x < y <-> @eq bool (@proj_sumbool (Z.lt x y) (Z.ge x y) (zlt x y)) true.
Proof.
  intros.
  split; intro.
  - apply zlt_true; auto.
  - destruct zlt.
    + assumption.
    + inversion H.
Qed.

Lemma zlt_false_iff:
  forall (x y : Z), x >= y <-> @eq bool (@proj_sumbool (Z.lt x y) (Z.ge x y) (zlt x y)) false.
Proof.
  intros.
  split; intro.
  - apply zlt_false; auto.
  - destruct zlt.
    + inversion H.
    + assumption.
Qed.

Lemma same_bits_eq_iff:
  forall x y,
  (forall i, 0 <= i < Int.zwordsize -> Int.testbit x i = Int.testbit y i) <-> x = y.
Proof.
  intros.
  split; intros.
  - apply Int.same_bits_eq; auto.
  - subst x. auto.
Qed.

(**r basic *)

Lemma unsigned_bitfield_extract_bitfield_insert_same_1:
  forall pos width v i
    (Hrange: 0 <= pos /\ 0 < width /\ pos+width <= Int.zwordsize)
    (HLOW: Int.size v <= width),
      Int.unsigned_bitfield_extract pos width (Int.bitfield_insert pos width i v) = v.
Proof.
  intros.
  apply Int.same_bits_eq; intros.
  rewrite Int.bits_unsigned_bitfield_extract; try lia.
  destruct zlt eqn: Hlt.
  2:{ rewrite Int.bits_size_2; try lia. }
  rewrite Int.bits_bitfield_insert; try lia.
  replace (i0 + pos - pos) with i0 by lia.
  assert (Heq: (if zle pos (i0 + pos) then true else false) = true). {
    apply zle_true.
    lia.
  }
  rewrite andb_if with (b := zle pos (i0 + pos)).
  unfold proj_sumbool.
  rewrite Heq; clear Heq.
  assert (Heq: (if zlt (i0 + pos) (pos + width) then true else false) = true). {
    apply zlt_true.
    lia.
  }
  rewrite Heq; clear Heq.
  f_equal.
Qed.

Lemma unsigned_bitfield_extract_bitfield_insert_same_2:
  forall i v pos0 pos1 width0 width1
    (Hrange: pos0+width0 <= pos1 \/ pos1+width1 <= pos0)
    (Hrange0: 0 <= pos0 /\ 0 < width0 /\ pos0+width0 <= Int.zwordsize /\
              0 <= pos1 /\ 0 < width1 /\ pos1+width1 <= Int.zwordsize),
      Int.unsigned_bitfield_extract pos1 width1 (Int.bitfield_insert pos0 width0 i v) =
      Int.unsigned_bitfield_extract pos1 width1 i.
Proof.
  intros.
  apply Int.same_bits_eq; intros.
  repeat rewrite Int.bits_unsigned_bitfield_extract; try lia.
  destruct zlt; [| reflexivity].
  rewrite Int.bits_bitfield_insert; try lia.
  unfold proj_sumbool.
  destruct Hrange as [Hrange | Hrange].
  - (**r pos0 + width0 <= pos1 *)
    rewrite zle_true; [| lia].
    rewrite zlt_false; [| lia].
    simpl.
    reflexivity.
  - (**r pos1 + width1 <= pos0 *)
    rewrite zle_false; [| lia].
    rewrite zlt_true; [| lia].
    simpl.
    reflexivity.
Qed.


Lemma unsigned_bitfield_extract_unsigned_bitfield_extract_0:
  forall i pos0 pos1 width0 width1
    (Hrange: width0 <= pos1) (**r more generic than `pos0+width0 <= pos1' *)
    (Hrange0: 0 <= pos0 /\ 0 < width0 /\ pos0+width0 <= Int.zwordsize /\
              0 <= pos1 /\ 0 < width1 /\ pos1+width1 <= Int.zwordsize),
      Int.unsigned_bitfield_extract pos1 width1 (Int.unsigned_bitfield_extract pos0 width0 i) = Int.zero.
Proof.
  intros.
  apply Int.same_bits_eq; intros.
  rewrite Int.bits_unsigned_bitfield_extract; try lia.
  destruct zlt; [| rewrite Int.bits_zero; reflexivity].

  rewrite Int.bits_unsigned_bitfield_extract; try lia.
  destruct zlt; rewrite Int.bits_zero; [lia | reflexivity].
Qed.

Lemma unsigned_bitfield_extract_unsigned_bitfield_extract_1: (**r more generic than `unsigned_bitfield_extract_same' *)
  forall i pos0 width0
    (Hrange: 0 <= pos0 /\ 0 < width0 /\ pos0+width0 <= Int.zwordsize),
      Int.unsigned_bitfield_extract 0%Z width0 (Int.unsigned_bitfield_extract pos0 width0 i) =
      Int.unsigned_bitfield_extract pos0 width0 i.
Proof.
  intros.
  apply Int.same_bits_eq; intros.
  rewrite Int.bits_unsigned_bitfield_extract; try lia.
  rewrite Z.add_0_r.
  destruct zlt; [ f_equal |].

  rewrite Int.bits_unsigned_bitfield_extract; try lia.
  destruct zlt; [lia | reflexivity].
Qed.

(**r other *)

Lemma unsigned_bitfield_extract_extend:
  forall i pos width
    (Hrange: 0 < pos /\ 0 < width /\ pos+width <= Int.zwordsize),
    Int.bitfield_insert pos width
      (Int.unsigned_bitfield_extract 0 pos i)
      (Int.unsigned_bitfield_extract pos width i) =
    Int.unsigned_bitfield_extract 0 (pos+width) i.
Proof.
  intros.
  apply Int.same_bits_eq; intros.
  rewrite Int.bits_unsigned_bitfield_extract; try lia.
  rewrite Z.add_0_r.
  rewrite Int.bits_bitfield_insert; try lia.
  destruct (_ && _) eqn: Hc.
  - rewrite Bool.andb_true_iff in Hc.
    rewrite <- zle_true_iff in Hc.
    rewrite <- zlt_true_iff in Hc.
    rewrite Int.bits_unsigned_bitfield_extract; try lia.
    replace (i0 - pos + pos) with i0 by lia.
    destruct zlt as [Hd | Hd].
    + destruct zlt as [He | He].
      * reflexivity.
      * lia.
    + destruct zlt as [He | He].
      * lia.
      * reflexivity.
  - rewrite Bool.andb_false_iff in Hc.
    rewrite <- zle_false_iff in Hc.
    rewrite <- zlt_false_iff in Hc.
    rewrite Int.bits_unsigned_bitfield_extract; try lia.
    rewrite Z.add_0_r.
    destruct zlt as [Hd | Hd].
    + destruct zlt as [He | He].
      * reflexivity.
      * lia.
    + destruct zlt as [He | He].
      * lia.
      * reflexivity.
Qed.

Lemma bitfield_insert_over_size_zero:
  forall i x pos width
    (Hrange: 0 <= pos /\ 0 < width /\ pos+width <= Int.zwordsize)
    (HZ: Int.size i <= x)
    (HZR: x <= pos),
      Int.bitfield_insert pos width i Int.zero = i.
Proof.
  intros.
  apply Int.same_bits_eq; intros.
  rewrite Int.bits_bitfield_insert; try lia.
  destruct (zle pos i0 && zlt i0 (pos + width)) eqn: Hc.
  2:{ reflexivity. }
  rewrite Int.bits_zero.
  symmetry.
  apply Int.bits_size_2.
  rewrite andb_true_iff in Hc.
  destruct Hc as (Hc1 & Hc2).

  rewrite <- zle_true_iff in Hc1.
  rewrite <- zlt_true_iff in Hc2.
  lia.
Qed.

Lemma unsigned_bitfield_extract_over_size:
  forall i x pos width
    (Hrange: 0 <= pos /\ 0 < width /\ pos+width <= Int.zwordsize)
    (HZ: Int.size i <= x)
    (HZR: x <= pos),
      Int.unsigned_bitfield_extract pos width i = Int.zero.
Proof.
  intros.
  apply Int.same_bits_eq; intros.
  rewrite Int.bits_zero.
  rewrite Int.bits_unsigned_bitfield_extract; try lia.
  destruct zlt as [Hlt | Hlt].
  2:{ reflexivity. }
  apply Int.bits_size_2. lia.
Qed.

Lemma size_bitfield_insert:
  forall pos width k i v
    (Hrange: 0 <= pos /\ 0 < width /\ pos+width <= k)
    (HI: Int.size i <= k)
    (HS: Int.size v <= width),
    Int.size (Int.bitfield_insert pos width i v) <= k.
Proof.
  intros.
  eapply Int.bits_size_3; eauto.
  lia.
  intros.
  rewrite Int.bits_bitfield_insert; try lia.
  destruct zle as [Hle | Hle]; [| lia].
  destruct zlt as [Hlt | Hlt]; [lia |].
  simpl.
  apply Int.bits_size_2. lia.
Qed.

Lemma size_unsigned_bitfield_extract:
  forall pos width k i
    (Hrange: 0 <= pos /\ 0 < width /\ width <= k /\ pos + width <= Int.zwordsize),
    Int.size (Int.unsigned_bitfield_extract pos width i) <= k.
Proof.
  intros.
  eapply Int.bits_size_3; eauto.
  lia.
  intros.
  rewrite Int.bits_unsigned_bitfield_extract; try lia.
  destruct zlt as [Hlt | Hlt]; [lia |].
  reflexivity.
Qed.

Lemma unsigned_bitfield_extract_low_same:
  forall width v
    (Hrange: 0 < width /\ width <= Int.zwordsize)
    (HLOW: Int.size v <= width),
    Int.unsigned_bitfield_extract 0 width v = v.
Proof.
  intros.
  apply Int.same_bits_eq; intros.
  repeat rewrite Int.bits_unsigned_bitfield_extract; try lia.
  destruct Coqlib.zlt eqn: Hlt.
  2:{ rewrite Int.bits_size_2; try lia. }
  rewrite Z.add_0_r.
  f_equal.
Qed.

Lemma unsigned_bitfield_extract_same_2:
  forall pos0 width0 width1 pos2 width2 n v
    (Hrange: 0 <= pos0 /\ 0 < width0 /\ pos0+width0 <= Int.zwordsize /\
             0 < width1 /\ width1 <= Int.zwordsize /\
             0 <= pos2 /\ 0 < width2 /\ pos2+width2 <= Int.zwordsize)
    (Hin: pos2 + width2 <= width1 /\ pos0 + width0 <= width1)
    (Hout: pos0+width0 <= pos2 \/ pos2+width2 <= pos0),
      (Int.unsigned_bitfield_extract pos0 width0 (Int.unsigned_bitfield_extract 0 width1 (Int.bitfield_insert pos2 width2 n v))) =
      Int.unsigned_bitfield_extract pos0 width0 n.
Proof.
  intros.
  apply Int.same_bits_eq; intros.
  rewrite Int.bits_unsigned_bitfield_extract; try lia.
  destruct zlt as [Hlt0 | Hlt0].
  2:{ erewrite Int.bits_size_2; eauto.
    eapply size_unsigned_bitfield_extract; eauto.
    lia.
  }

  rewrite Int.bits_unsigned_bitfield_extract; try lia.
  destruct zlt as [Hlt1 | Hlt1].
  2:{ erewrite Int.bits_size_2; eauto.
    eapply size_unsigned_bitfield_extract; eauto.
    lia.
  }
  rewrite Z.add_0_r.
  rewrite Int.bits_unsigned_bitfield_extract; try lia.
  rewrite Int.bits_bitfield_insert; try lia.
  destruct (zlt i width0) as [Hlt2 | Hlt2]; [ clear Hlt2 | lia].
  destruct zle as [Hle | Hle].
  - destruct zlt as [Hlt3 | Hlt3]; try lia.
    simpl.
    f_equal.
  - destruct zlt as [Hlt3 | Hlt3]; try lia.
    simpl.
    f_equal.
Qed.

Lemma unsigned_bitfield_extract_same_3:
  forall pos0 width0 width1 n v
    (Hrange: 0 <= pos0 /\ 0 < width0 /\ pos0+width0 <= Int.zwordsize /\
             0 < width1 /\ width1 <= Int.zwordsize)
    (Hin: pos0 + width0 <= width1),
      (Int.unsigned_bitfield_extract pos0 width0 (Int.unsigned_bitfield_extract 0 width1 (Int.bitfield_insert pos0 width0 n v))) =
      (Int.unsigned_bitfield_extract pos0 width0 (Int.bitfield_insert pos0 width0 n v)).
Proof.
  intros.
  apply Int.same_bits_eq; intros.
  rewrite Int.bits_unsigned_bitfield_extract; try lia.
  destruct zlt as [Hlt0 | Hlt0].
  2:{ erewrite Int.bits_size_2; eauto.
    eapply size_unsigned_bitfield_extract; eauto.
    lia.
  }

  rewrite Int.bits_unsigned_bitfield_extract; try lia.
  destruct zlt as [Hlt1 | Hlt1].
  2:{ erewrite Int.bits_size_2; eauto.
    eapply size_unsigned_bitfield_extract; eauto.
    lia.
  }
  rewrite Z.add_0_r.
  rewrite Int.bits_unsigned_bitfield_extract; try lia.
  rewrite Int.bits_bitfield_insert; try lia.
  destruct (zlt i width0) as [Hlt2 | Hlt2]; [ clear Hlt2 | lia].
  destruct zle as [Hle | Hle].
  - destruct zlt as [Hlt3 | Hlt3]; try lia.
    simpl.
    f_equal.
  - reflexivity.
Qed.