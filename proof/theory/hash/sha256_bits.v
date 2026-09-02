(** * theory.hash.sha256_bits: 32-bit word bit-operations for the SHA-256 model. *)
(** Copyright (C) 2026 remix7531
    SPDX-License-Identifier: MIT *)

(** Pure-[Z] 32-bit word math for [model/hash.v]: the bitwise operations
    ([xor32] / [and32] / [or32] / [not32]) SHA-256's [Ch] / [Maj] / [Sigma0] /
    [Sigma1] round macros compose (`src/hash_impl.h:16-21`), the
    right-rotate / right-shift operations its [sigma0] / [sigma1] message
    schedule needs ([rotr32] / [shr32]), and the range lemmas that keep every
    SHA-256 intermediate provably a 32-bit word.  [not32] is proved for
    completeness of the bitwise vocabulary; the retained round macros never
    call it (the [Ch]/[Maj] forms in [hash_impl.h] are deliberately written to
    avoid a bitwise complement).  No VST, no struct ids: this is theory, not
    model, and never mentions a hash state. *)

From Stdlib Require Import ZArith Lia.

Open Scope Z_scope.

(* ================================================================= *)
(** ** Bounding bitwise results -- [log2_lt_32_of_range] / [pow2_32_bound_of_log2]. *)

(** A 32-bit value's highest set bit is below 32.  The forward half of the
    [0 <= x < 2^32] <-> [log2] correspondence the bitwise range lemmas below
    both need. *)
Lemma log2_lt_32_of_range : forall x, 0 <= x < 2^32 -> Z.log2 x < 32.
Proof.
  intros x [Hx0 Hx1].
  destruct (Z.eq_dec x 0) as [->|Hx0'].
  - rewrite Z.log2_nonpos by lia. lia.
  - apply (Z.log2_lt_pow2 x 32); lia.
Qed.

(** The reverse half: a nonnegative value whose highest set bit is below 32
    is itself below [2^32]. *)
Lemma pow2_32_bound_of_log2 : forall x, 0 <= x -> Z.log2 x < 32 -> x < 2^32.
Proof.
  intros x Hx Hlog.
  destruct (Z.eq_dec x 0) as [->|Hx0].
  - apply Z.pow_pos_nonneg; lia.
  - apply (Z.log2_lt_pow2 x 32); lia.
Qed.

(* ================================================================= *)
(** ** Bitwise word operations -- [xor32] / [and32] / [or32] / [not32]. *)

(** 32-bit bitwise XOR. *)
Definition xor32 (x y : Z) : Z := Z.lxor x y.

(** 32-bit bitwise AND. *)
Definition and32 (x y : Z) : Z := Z.land x y.

(** 32-bit bitwise OR. *)
Definition or32 (x y : Z) : Z := Z.lor x y.

(** 32-bit bitwise complement (XOR against the all-ones mask -- NOT [Z.lnot],
    which is the two's-complement [-x-1], unusable at a fixed width). *)
Definition not32 (x : Z) : Z := Z.lxor x (2^32 - 1).

(** [xor32] of two 32-bit words is a 32-bit word. *)
Lemma xor32_range : forall x y, 0 <= x < 2^32 -> 0 <= y < 2^32 -> 0 <= xor32 x y < 2^32.
Proof.
  intros x y Hx Hy. unfold xor32.
  split.
  - apply Z.lxor_nonneg. split; lia.
  - apply pow2_32_bound_of_log2.
    + apply Z.lxor_nonneg. split; lia.
    + eapply Z.le_lt_trans; [apply Z.log2_lxor; lia|].
      apply Z.max_lub_lt; apply log2_lt_32_of_range; lia.
Qed.

(** [and32] of two 32-bit words is a 32-bit word. *)
Lemma and32_range : forall x y, 0 <= x < 2^32 -> 0 <= y < 2^32 -> 0 <= and32 x y < 2^32.
Proof.
  intros x y Hx Hy. unfold and32.
  split.
  - apply Z.land_nonneg. left; lia.
  - apply pow2_32_bound_of_log2.
    + apply Z.land_nonneg. left; lia.
    + eapply Z.le_lt_trans; [apply Z.log2_land; lia|].
      apply Z.le_lt_trans with (Z.log2 x); [apply Z.le_min_l|].
      apply log2_lt_32_of_range; lia.
Qed.

(** [or32] of two 32-bit words is a 32-bit word. *)
Lemma or32_range : forall x y, 0 <= x < 2^32 -> 0 <= y < 2^32 -> 0 <= or32 x y < 2^32.
Proof.
  intros x y Hx Hy. unfold or32.
  split.
  - apply Z.lor_nonneg. split; lia.
  - apply pow2_32_bound_of_log2.
    + apply Z.lor_nonneg. split; lia.
    + rewrite Z.log2_lor by lia.
      apply Z.max_lub_lt; apply log2_lt_32_of_range; lia.
Qed.

(** [not32] of a 32-bit word is a 32-bit word (a direct corollary of
    [xor32_range] against the constant mask [2^32 - 1]). *)
Lemma not32_range : forall x, 0 <= x < 2^32 -> 0 <= not32 x < 2^32.
Proof.
  intros x Hx. unfold not32.
  change (Z.lxor x (2^32 - 1)) with (xor32 x (2^32 - 1)).
  apply xor32_range; lia.
Qed.

(** [xor32] is commutative -- a thin wrapper so a [model/hash.v] proof can
    rewrite with the project name rather than reaching past it to
    [Z.lxor_comm]. *)
Lemma xor32_comm : forall x y, xor32 x y = xor32 y x.
Proof. intros x y. apply Z.lxor_comm. Qed.

(** [and32] is commutative (a [Z.land_comm] wrapper, see [xor32_comm]). *)
Lemma and32_comm : forall x y, and32 x y = and32 y x.
Proof. intros x y. apply Z.land_comm. Qed.

(** [or32] is commutative (a [Z.lor_comm] wrapper, see [xor32_comm]). *)
Lemma or32_comm : forall x y, or32 x y = or32 y x.
Proof. intros x y. apply Z.lor_comm. Qed.

(* ================================================================= *)
(** ** Rotate / shift -- [rotr32] / [shr32]. *)

(** 32-bit right-rotate by [n] bits ([0 <= n < 32}]): the low [n] bits of [x]
    move to the top, the rest shift down.  Written as plain arithmetic (a
    division/multiplication split, not [Z.lor]) so [rotr32_range] closes by
    ordinary interval reasoning; [model/hash.v] never needs the bitwise form. *)
Definition rotr32 (x n : Z) : Z := x / 2^n + (x mod 2^n) * 2^(32 - n).

(** Right-shift by [n] bits ([0 <= n]), as plain division. *)
Definition shr32 (x n : Z) : Z := x / 2^n.

(** [rotr32] of a 32-bit word is a 32-bit word. *)
Lemma rotr32_range : forall x n, 0 <= x < 2^32 -> 0 <= n < 32 -> 0 <= rotr32 x n < 2^32.
Proof.
  intros x n [Hx0 Hx1] [Hn0 Hn1]. unfold rotr32.
  assert (Hp : 2^32 = 2^n * 2^(32-n)) by (rewrite <- Z.pow_add_r by lia; f_equal; lia).
  assert (H2n : 0 < 2^n) by (apply Z.pow_pos_nonneg; lia).
  assert (H2nn : 0 < 2^(32-n)) by (apply Z.pow_pos_nonneg; lia).
  assert (Hdiv : 0 <= x / 2^n <= 2^(32-n) - 1).
  { split.
    - apply Z.div_pos; lia.
    - assert (x / 2^n < 2^(32-n)) by (apply Z.div_lt_upper_bound; [lia | rewrite <- Hp; lia]).
      lia. }
  assert (Hmod : 0 <= x mod 2^n <= 2^n - 1) by (assert (H := Z.mod_pos_bound x (2^n) H2n); lia).
  assert (Hmul : (x mod 2^n) * 2^(32-n) <= (2^n - 1) * 2^(32-n))
    by (apply Z.mul_le_mono_nonneg_r; lia).
  assert (Heq : (2^n - 1) * 2^(32-n) = 2^n * 2^(32-n) - 2^(32-n)) by ring.
  assert (Hmulpos : 0 <= (x mod 2^n) * 2^(32-n)) by (apply Z.mul_nonneg_nonneg; lia).
  lia.
Qed.

(** [shr32] of a 32-bit word is a 32-bit word. *)
Lemma shr32_range : forall x n, 0 <= x < 2^32 -> 0 <= n -> 0 <= shr32 x n < 2^32.
Proof.
  intros x n [Hx0 Hx1] Hn. unfold shr32.
  assert (H2n : 1 <= 2^n) by (change 1 with (2^0); apply Z.pow_le_mono_r; lia).
  split.
  - apply Z.div_pos; lia.
  - assert (Hle : x / 2^n <= x) by (apply Z.div_le_upper_bound; nia).
    lia.
Qed.

(** Degenerate-rotate identity: rotating by 0 bits is the identity, the
    boundary sanity check for [rotr32]'s arithmetic definition. *)
Lemma rotr32_0 : forall x, rotr32 x 0 = x.
Proof.
  intros x. unfold rotr32.
  rewrite Z.pow_0_r, Z.div_1_r, Z.mod_1_r.
  ring.
Qed.

(** Degenerate-shift identity: shifting by 0 bits is the identity. *)
Lemma shr32_0 : forall x, shr32 x 0 = x.
Proof.
  intros x. unfold shr32.
  rewrite Z.pow_0_r, Z.div_1_r.
  reflexivity.
Qed.
