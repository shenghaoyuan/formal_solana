From Coq Require Import ZArith List.
From compcert.lib Require Import Integers Coqlib Zbits.
Import ListNotations.

(*--------------16-Word------------------*)
Module Wordsize_16.
  Definition wordsize := 16%nat.
  Remark wordsize_not_zero: wordsize <> 0%nat.
Proof.
unfold wordsize; congruence. Qed.
End Wordsize_16.

Strategy opaque [Wordsize_16.wordsize].

Module Word := Make(Wordsize_16).

Strategy 0 [Wordsize_16.wordsize].

Notation word := Word.int.
(*----------------16-Word----------------*)

(*-----------------128-Int-----------------*)
Module Wordsize_128.
  Definition wordsize := 128%nat.
  Remark wordsize_not_zero: wordsize <> 0%nat.
Proof.
unfold wordsize; congruence. Qed.
End Wordsize_128.

Strategy opaque [Wordsize_128.wordsize].

Module Int128 := Make(Wordsize_128).

Strategy 0 [Wordsize_128.wordsize].

Notation int128 := Int128.int.
(*-----------------128-Int-----------------*)

Definition usize := int64.

Record ebpf_binary := {
  bpf_opc : byte;
  bpf_dst : nat;
  bpf_src : nat;
  bpf_off : word;
  bpf_imm : int
}.

Definition ebpf_abin := list ebpf_binary.

Definition bit_left_shift_byte (x: byte) (n: nat) : byte := 
      Byte.shl x (Byte.repr (Z.of_nat n)).

Definition bit_right_shift_byte (x: byte) (n: nat) : byte := 
      Byte.shru x (Byte.repr (Z.of_nat n)).

Definition bit_left_shift_word (x: word) (n: nat) : word := 
      Word.shl x (Word.repr (Z.of_nat n)).

Definition bit_right_shift_word (x: word) (n: nat) : word := 
      Word.shru x (Word.repr (Z.of_nat n)).

Definition bit_left_shift_int (x: int) (n: nat) : int := 
      Int.shl x (Int.repr (Z.of_nat n)).

Definition bit_right_shift_int (x: int) (n: nat) : int := 
      Int.shru x (Int.repr (Z.of_nat n)).

Definition bit_left_shift_int64 (x: int64) (n: nat) : int64 := 
      Int64.shl x (Int64.repr (Z.of_nat n)).

Definition bit_right_shift_int64 (x: int64) (n: nat) : int64 := 
      Int64.shru x (Int64.repr (Z.of_nat n)).

Definition arsh32 (x : int) (n : nat) : int :=
  Int.shr x (Int.repr (Z.of_nat n)).

Definition arsh64 (x : int64) (n : nat) : int64 :=
  Int64.shr x (Int64.repr (Z.of_nat n)).

Definition bitfield_extract_byte (pos width: nat) (n : byte) : byte :=
  Byte.unsigned_bitfield_extract (Z.of_nat pos) (Z.of_nat width) n.

Definition bitfield_insert_byte (pos width: nat) (n p : byte) : byte :=
  Byte.bitfield_insert (Z.of_nat pos) (Z.of_nat width) n p.

Definition byte_of_bool (b : bool) : byte :=
  match b with 
    | true  => Byte.repr 1
    | false => Byte.repr 0
  end.

Definition nat_of_bool (b : bool) : nat :=
  match b with 
    | true  => S O
    | false => O
  end.

Definition byte_list_of_word (x: word) : list byte :=
   [Byte.repr (Word.unsigned (Word.and x (Word.repr 0xff)));
    Byte.repr (Word.unsigned (Word.and (bit_right_shift_word x (8)) (Word.repr 0xff)))
   ].

Definition byte_list_of_int (x: int) : list byte :=
   [Byte.repr (Int.unsigned (Int.and x (Int.repr 0xff)));
    Byte.repr (Int.unsigned (Int.and (bit_right_shift_int x (8)) (Int.repr 0xff)));
    Byte.repr (Int.unsigned (Int.and (bit_right_shift_int x (16)) (Int.repr 0xff)));
    Byte.repr (Int.unsigned (Int.and (bit_right_shift_int x (24)) (Int.repr 0xff)))
   ].

Definition byte_list_of_int64 (x: int64) : list byte :=
   [Byte.repr (Int64.unsigned (Int64.and x (Int64.repr 0xff)));
    Byte.repr (Int64.unsigned (Int64.and (bit_right_shift_int64 x (8)) (Int64.repr 0xff)));
    Byte.repr (Int64.unsigned (Int64.and (bit_right_shift_int64 x (16)) (Int64.repr 0xff)));
    Byte.repr (Int64.unsigned (Int64.and (bit_right_shift_int64 x (24)) (Int64.repr 0xff)));
    Byte.repr (Int64.unsigned (Int64.and (bit_right_shift_int64 x (32)) (Int64.repr 0xff)));
    Byte.repr (Int64.unsigned (Int64.and (bit_right_shift_int64 x (40)) (Int64.repr 0xff)));
    Byte.repr (Int64.unsigned (Int64.and (bit_right_shift_int64 x (48)) (Int64.repr 0xff)));
    Byte.repr (Int64.unsigned (Int64.and (bit_right_shift_int64 x (56)) (Int64.repr 0xff)))
   ].

Definition int64_of_byte_list (l : list byte) : option int64 :=
  if (Z.eqb (Z.of_nat (List.length l)) 8) then
    Some (Int64.or (bit_left_shift_int64 (Int64.repr (Byte.unsigned (List.nth 7 l Byte.zero))) 56)
      (Int64.or (bit_left_shift_int64 (Int64.repr (Byte.unsigned (List.nth 6 l Byte.zero))) 48)
      (Int64.or (bit_left_shift_int64 (Int64.repr (Byte.unsigned (List.nth 5 l Byte.zero))) 40)
      (Int64.or (bit_left_shift_int64 (Int64.repr (Byte.unsigned (List.nth 4 l Byte.zero))) 32)
      (Int64.or (bit_left_shift_int64 (Int64.repr (Byte.unsigned (List.nth 3 l Byte.zero))) 24)
      (Int64.or (bit_left_shift_int64 (Int64.repr (Byte.unsigned (List.nth 2 l Byte.zero))) 16)
      (Int64.or (bit_left_shift_int64 (Int64.repr (Byte.unsigned (List.nth 1 l Byte.zero))) 8)
                (Int64.repr (Byte.unsigned (List.nth 0 l Byte.zero))))))))))
  else
    None.

Definition int_of_byte_list (l : list byte) : option int :=
  if (Z.eqb (Z.of_nat (List.length l)) 4) then
    Some (Int.or (bit_left_shift_int (Int.repr (Byte.unsigned (List.nth 3 l Byte.zero))) 24)
      (Int.or (bit_left_shift_int (Int.repr (Byte.unsigned (List.nth 2 l Byte.zero))) 16)
      (Int.or (bit_left_shift_int (Int.repr (Byte.unsigned (List.nth 1 l Byte.zero))) 8)
                (Int.repr (Byte.unsigned (List.nth 0 l Byte.zero))))))
  else
    None.

Definition word_of_byte_list (l : list byte) : option word :=
  if (Z.eqb (Z.of_nat (List.length l)) 2) then
    Some (Word.or (bit_left_shift_word (Word.repr (Byte.unsigned (List.nth 1 l Byte.zero))) 8)
                (Word.repr (Byte.unsigned (List.nth 0 l Byte.zero))))
  else
    None.

Lemma byte_of_bool_false : byte_of_bool false = Byte.zero.
Proof.
  unfold byte_of_bool.
  reflexivity.
Qed.

Lemma byte_of_bool_true : byte_of_bool true = Byte.one.
Proof.
  unfold byte_of_bool.
  reflexivity.
Qed.

(*
Lemma Ztestbit_above:
  forall n x i,
  0 <= x < two_power_nat n ->
  i >= Z.of_nat n ->
  Z.testbit x i = false.
Proof.
  induction n; intros.
  - change (two_power_nat 0) with 1 in H.
    replace x with 0 by lia.
    apply Z.testbit_0_l.
  - rewrite Nat2Z.inj_succ in H0. rewrite Ztestbit_eq. rewrite zeq_false.
    apply IHn. rewrite two_power_nat_S in H. rewrite (Zdecomp x) in H.
    rewrite Zshiftin_spec in H. destruct (Z.odd x); lia.
    lia. lia. lia.
Qed.
*)

Lemma byte_ge_8_bit_false : forall (n : Z) (v : byte),
  n >= 8 -> (Z.testbit (Byte.unsigned v) n = false).
Proof.
  intros n v H. 
  apply Ztestbit_above with (n := (Z.to_nat 8)).
  - unfold two_power_nat.
    simpl. 
    apply Byte.unsigned_range.
  - unfold Z.to_nat,Z.of_nat.
    simpl. 
    apply H.
Qed.

Lemma byte_bit_true_ge_8 : forall (n : Z) (v : byte),
  (Byte.testbit v n = true) -> n < 8.
Proof.
  intros n v H.
  unfold Byte.testbit, Byte.unsigned, Z.testbit in H.
  destruct n as [|n'|n''] eqn:E.
  - reflexivity.
  - destruct (Byte.intval v) eqn:Hv.
    + discriminate H.
    + 
Abort.

Lemma bit_power_k_minus_1_le: forall (k n : Z), 
  Z.testbit (Z.pred (2 ^ k)) n = true <-> n < k.
Proof.
  intros k n.
  split.
  - intros H.
    unfold Z.pred,Z.pow in H.
    destruct k as [|k'|k''] eqn:K.
    + simpl in H. 
      rewrite Ztestbit_0 in H. 
      inversion H.
    + 
Abort.

Lemma bit_power_k_add_m_ge: forall k m n: Z,
  Z.testbit (Z.pow 2 (k + m) - Z.pow 2 k) n = true ->
  (k <= n /\ n < k + m).
Proof.
  intros k m n H.
  
Abort.

Lemma bit_power_k_add_m_lt : forall k m n : Z,
  n < k + m -> Z.testbit (Z.pow 2 (k + m) - Z.pow 2 k) n = false -> n < k.
Proof.
  intros.
  
Abort.






