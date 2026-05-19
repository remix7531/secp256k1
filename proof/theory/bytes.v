(** * theory.bytes: big-endian byte-string <-> Z conversion *)
(** Copyright (C) 2026 remix7531
    SPDX-License-Identifier: MIT *)

(** Pure [Z] model of the big-endian byte (de)serialization performed by
    [secp256k1_read_be64] / [secp256k1_write_be64] and, lifted to 32 bytes, by
    [secp256k1_scalar_set_b32] / [secp256k1_scalar_get_b32].  No VST, no word
    size: a byte list is most-significant-first.  The heavier bridge to the
    64-bit-limb evaluator ([eval4]/[limb]) is left to the proof phase. *)

From Stdlib Require Import ZArith.
From Stdlib Require Import Lia.
From Stdlib Require Import List.

Import ListNotations.
Open Scope Z_scope.

(* ================================================================= *)
(** ** Encode/decode definitions -- [Z_of_be_bytes] / [be_bytes_of_Z]. *)

(** Decode a big-endian byte list (head = most significant) to a [Z]. *)
Definition Z_of_be_bytes (bs : list Z) : Z :=
  fold_left (fun acc b => acc * 256 + b) bs 0.

(** Encode the low [n] bytes of [v], big-endian (head = most significant). *)
Fixpoint be_bytes_of_Z (v : Z) (n : nat) : list Z :=
  match n with
  | O => []
  | S k => be_bytes_of_Z (v / 256) k ++ [v mod 256]
  end.

(* ================================================================= *)
(** ** Length and range of [be_bytes_of_Z] -- [length]/[Zlength]/byte in [[0,256)]. *)

(** [be_bytes_of_Z v n] has exactly [n] bytes. *)
Lemma be_bytes_of_Z_length : forall n v, length (be_bytes_of_Z v n) = n.
Proof.
  induction n; intros v.
  - reflexivity.
  - simpl.
    rewrite length_app.
    rewrite IHn.
    simpl.
    lia.
Qed.

(** Same, as a [Zlength] fact (the form VST's [tarray] reasoning wants). *)
Lemma be_bytes_of_Z_Zlength : forall n v,
  Zlength (be_bytes_of_Z v n) = Z.of_nat n.
Proof.
  intros n v.
  rewrite Zlength_correct.
  rewrite be_bytes_of_Z_length.
  reflexivity.
Qed.

(** Every encoded byte is in [[0, 256)]. *)
Lemma be_bytes_of_Z_range : forall n v,
  Forall (fun b => 0 <= b < 256) (be_bytes_of_Z v n).
Proof.
  induction n; intros v.
  - constructor.
  - simpl.
    apply Forall_app.
    split.
    + apply IHn.
    + constructor; [| constructor].
      apply Z.mod_pos_bound.
      lia.
Qed.

(* ================================================================= *)
(** ** Decode algebra -- [Z_of_be_bytes] accumulator/append/bound lemmas. *)

(** The big-endian accumulator [fold_left] started at an arbitrary [a]
    factors as [a * 256^len + (fold from 0)].  This is the workhorse for
    the append and bound lemmas below. *)
Lemma be_fold_left_acc : forall (bs : list Z) (a : Z),
  fold_left (fun acc b => acc * 256 + b) bs a
  = a * 256 ^ Z.of_nat (length bs)
    + fold_left (fun acc b => acc * 256 + b) bs 0.
Proof.
  induction bs as [|b bs IH]; intros a.
  - simpl.
    lia.
  - simpl length.
    rewrite Nat2Z.inj_succ.
    rewrite Z.pow_succ_r by lia.
    cbn [fold_left].
    rewrite (IH (a * 256 + b)).
    rewrite (IH (0 * 256 + b)).
    lia.
Qed.

(** Big-endian decode distributes over append (head = most significant):
    the prefix is scaled by [256^(length of the suffix)]. *)
Lemma Z_of_be_bytes_app : forall (bs1 bs2 : list Z),
  Z_of_be_bytes (bs1 ++ bs2)
  = Z_of_be_bytes bs1 * 256 ^ Z.of_nat (length bs2) + Z_of_be_bytes bs2.
Proof.
  intros bs1 bs2.
  unfold Z_of_be_bytes.
  rewrite fold_left_app.
  rewrite (be_fold_left_acc bs2 (fold_left (fun acc b => acc * 256 + b) bs1 0)).
  reflexivity.
Qed.

(** A big-endian byte list of length [n] (all bytes in [[0,256)]) decodes
    to a value in [[0, 256^n)]. *)
Lemma Z_of_be_bytes_bound : forall (l : list Z),
  Forall (fun b => 0 <= b < 256) l ->
  0 <= Z_of_be_bytes l < 256 ^ Z.of_nat (length l).
Proof.
  intros l Hl.
  unfold Z_of_be_bytes.
  induction l as [|x l IH].
  - simpl.
    lia.
  - inversion Hl as [|y ys Hx Hys]; subst.
    specialize (IH Hys).
    simpl length.
    rewrite Nat2Z.inj_succ, Z.pow_succ_r by lia.
    cbn [fold_left].
    rewrite (be_fold_left_acc l (0 * 256 + x)).
    assert (0 <= 256 ^ Z.of_nat (length l)) by (apply Z.pow_nonneg; lia).
    nia.
Qed.

(** A big-endian decode of nonnegative bytes is nonnegative -- the
    nonnegative half of [Z_of_be_bytes_bound], kept as its own lemma
    for the [scalar_set_b32_seckey] use site. *)
Lemma Z_of_be_bytes_nonneg : forall bs,
  Forall (fun b => 0 <= b < 256) bs ->
  0 <= Z_of_be_bytes bs.
Proof.
  intros bs Hall.
  exact (proj1 (Z_of_be_bytes_bound bs Hall)).
Qed.
