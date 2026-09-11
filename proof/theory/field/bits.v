(** * field_bits: bit-width + magnitude bounds for the 5x52 field representation. *)
(** Copyright (C) 2026 remix7531
    SPDX-License-Identifier: MIT *)

(** Pure-Z support for the field subsystem's lazy-reduction discipline.  Two
    parts:

    - A generic [bits x k] ("[x] fits in [k] bits") family ([bits_add] /
      [bits_mul] / [bits_shiftr] / [bits_and_mask]) -- the lemmas a [normalize] /
      [mul] reduction needs to track limb growth across [+], [*], [>> 52], [& M].

    - The concrete 5x52 magnitude bound ([fe_limb_mag_bound]) and the
      no-overflow fact for [fe_add] ([fe_add_limb_no_overflow]).

    Magnitude bounds describe the C representation. [Math.field.Fe] stores
    only a reduced field value. *)

From Stdlib Require Import ZArith.
From Stdlib Require Import Lia.
Local Open Scope Z_scope.

(* ================================================================= *)
(** ** The [bits] predicate and its closure lemmas. *)

(** [bits x k] : [x] is a non-negative integer representable in [k] bits. *)
Definition bits (x k : Z) : Prop := 0 <= x < 2 ^ k.

(** Addition costs at most one extra bit. *)
Lemma bits_add : forall x y j k,
  0 <= j -> 0 <= k -> bits x j -> bits y k -> bits (x + y) (Z.max j k + 1).
Proof.
  intros x y j k Hj Hk [Hx0 Hx1] [Hy0 Hy1]. unfold bits. split; [lia|].
  assert (Hjm : 2 ^ j <= 2 ^ Z.max j k) by (apply Z.pow_le_mono_r; lia).
  assert (Hkm : 2 ^ k <= 2 ^ Z.max j k) by (apply Z.pow_le_mono_r; lia).
  assert (Hp : 2 ^ (Z.max j k + 1) = 2 * 2 ^ Z.max j k)
    by (rewrite Z.pow_add_r by lia; rewrite Z.pow_1_r; ring).
  lia.
Qed.

(** Multiplication adds bit-widths. *)
Lemma bits_mul : forall x y j k,
  0 <= j -> 0 <= k -> bits x j -> bits y k -> bits (x * y) (j + k).
Proof.
  intros x y j k Hj Hk [Hx0 Hx1] [Hy0 Hy1]. unfold bits.
  assert (0 < 2 ^ j) by (apply Z.pow_pos_nonneg; lia).
  assert (0 < 2 ^ k) by (apply Z.pow_pos_nonneg; lia).
  split; [nia|].
  rewrite Z.pow_add_r by lia. nia.
Qed.

(** Right shift by [s] drops [s] bits (clamped at 0). *)
Lemma bits_shiftr : forall x k s,
  0 <= s -> bits x k -> bits (Z.shiftr x s) (Z.max 0 (k - s)).
Proof.
  intros x k s Hs [Hx0 Hx1]. unfold bits.
  rewrite Z.shiftr_div_pow2 by lia.
  assert (0 < 2 ^ s) by (apply Z.pow_pos_nonneg; lia).
  split; [apply Z.div_pos; lia|].
  destruct (Z_le_gt_dec s k).
  - rewrite Z.max_r by lia.
    apply Z.div_lt_upper_bound; [lia|].
    rewrite <- Z.pow_add_r by lia.
    replace (s + (k - s)) with k by lia. lia.
  - rewrite Z.max_l by lia. rewrite Z.pow_0_r.
    assert (x < 2 ^ s).
    { apply Z.lt_le_trans with (2 ^ k); [lia|]. apply Z.pow_le_mono_r; lia. }
    rewrite Z.div_small by lia. lia.
Qed.

(** Masking with [2^s - 1] yields an [s]-bit result. *)
Lemma bits_and_mask : forall x s,
  0 <= s -> bits (Z.land x (2 ^ s - 1)) s.
Proof.
  intros x s Hs. unfold bits.
  replace (2 ^ s - 1) with (Z.ones s) by (rewrite Z.ones_equiv; lia).
  rewrite Z.land_ones by lia.
  apply Z.mod_pos_bound. apply Z.pow_pos_nonneg; lia.
Qed.

(* ================================================================= *)
(** ** Concrete 5x52 magnitude bound. *)

(** Per-limb bound for a magnitude-[m] field element (from src/field_5x52.h):
    limbs 0..3 are bounded by [2*m*(2^52-1)], limb 4 by [2*m*(2^48-1)]. *)
Definition fe_limb_mag_bound (m : Z) (i : nat) : Z :=
  if (i <? 4)%nat then 2 * m * (2 ^ 52 - 1) else 2 * m * (2 ^ 48 - 1).

(** [secp256k1_fe_add]'s limb-wise [r->n[i] += a->n[i]] never wraps uint64: with
    the (VERIFY-only) precondition [mr + ma <= 32], each magnitude-bounded limb
    sum stays below [2^64].  Worst case is [2*32*(2^52-1) = 2^58 - 64 < 2^64]. *)
Lemma fe_add_limb_no_overflow : forall (mr ma lr la : Z) (i : nat),
  0 <= mr -> 0 <= ma -> mr + ma <= 32 ->
  0 <= lr <= fe_limb_mag_bound mr i ->
  0 <= la <= fe_limb_mag_bound ma i ->
  0 <= lr + la < 2 ^ 64.
Proof.
  intros mr ma lr la i Hmr Hma Hsum [Hlr0 Hlr1] [Hla0 Hla1].
  unfold fe_limb_mag_bound in Hlr1, Hla1.
  assert (E64 : (2:Z) ^ 64 = 18446744073709551616) by reflexivity.
  destruct (i <? 4)%nat;
    [ assert (E : (2:Z) ^ 52 = 4503599627370496) by reflexivity
    | assert (E : (2:Z) ^ 48 = 281474976710656) by reflexivity ];
    rewrite E in Hlr1, Hla1; lia.
Qed.

(* ================================================================= *)
(** ** Multiplication / squaring bound -- [fe_mul_limb_no_overflow].

    [secp256k1_fe_mul_inner] / [secp256k1_fe_sqr_inner] (the u128-accumulator
    driver behind [fe_mul] / [fe_sqr]) require both inputs' magnitude to be at
    most 8; every partial product it accumulates is one pair of magnitude-8
    limbs.  This is the per-pair no-overflow fact the accumulator bound proof
    needs at every step, mirroring [fe_add_limb_no_overflow] above. *)

(** Every [fe_limb_mag_bound m i] is at most the (larger) limb-0..3 form
    [2*m*(2^52-1)], regardless of [i] -- the limb-4 form is strictly smaller. *)
Lemma fe_limb_mag_bound_le52 : forall m i,
  0 <= m -> fe_limb_mag_bound m i <= 2 * m * (2 ^ 52 - 1).
Proof.
  intros m i Hm.
  unfold fe_limb_mag_bound.
  destruct (i <? 4)%nat; [lia|].
  assert (H48 : (2:Z) ^ 48 <= 2 ^ 52) by (apply Z.pow_le_mono_r; lia).
  nia.
Qed.

(** Two magnitude-8 limbs multiply to well under [2^128]: the concrete bound
    a [u128] accumulator needs. *)
Lemma fe_mul_limb_no_overflow : forall (i j : nat) (li lj : Z),
  0 <= li <= fe_limb_mag_bound 8 i ->
  0 <= lj <= fe_limb_mag_bound 8 j ->
  0 <= li * lj < 2 ^ 128.
Proof.
  intros i j li lj [Hli0 Hli1] [Hlj0 Hlj1].
  pose proof (fe_limb_mag_bound_le52 8 i ltac:(lia)) as Hi.
  pose proof (fe_limb_mag_bound_le52 8 j ltac:(lia)) as Hj.
  assert (Hc : 2 * 8 * (2 ^ 52 - 1) = 72057594037927920) by reflexivity.
  assert (H128 : (2:Z) ^ 128 = 340282366920938463463374607431768211456) by reflexivity.
  nia.
Qed.

(* ================================================================= *)
(** ** Normalized-form bound -- [fe_limb_norm_bound] ties [normalize]'s output
    to the [fe_limb_mag_bound] family it starts from. *)

(** The per-limb cap [secp256k1_fe_impl_normalize] leaves once carry
    propagation is complete (the C's own "Normalized requires: n\[i\] <=
    (2^52 - 1)..." comment): limbs 0..3 fit 52 bits, limb 4 fits 48. *)
Definition fe_limb_norm_bound (i : nat) : Z :=
  if (i <? 4)%nat then 2 ^ 52 - 1 else 2 ^ 48 - 1.

(** Magnitude 1 is exactly twice the normalized bound, per limb -- the
    identity that lets a magnitude-1 bound bridge to a normalized one (and
    vice versa) without a separate proof for each limb index. *)
Lemma fe_limb_norm_bound_half_mag1 : forall i,
  2 * fe_limb_norm_bound i = fe_limb_mag_bound 1 i.
Proof.
  intros i.
  unfold fe_limb_norm_bound, fe_limb_mag_bound.
  destruct (i <? 4)%nat; lia.
Qed.
