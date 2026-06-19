(** * theory.modinv.bounds: pure interval arithmetic for the safegcd C-loop bounds. *)
(** Copyright (C) 2026 remix7531
    Ported from BlockstreamResearch/simplicity Coq/C/progressC.v
    (commit c1dddedd), Copyright (c) 2018 Blockstream, originally MIT.
    Upstream notice reproduced in proof/README.md.
    SPDX-License-Identifier: MIT *)

(** The pure-[Z] interval facts behind the safegcd bounds automation: how a
    product or an accumulation of machine-word-ranged operands is bracketed.
    They carry no machine-integer content at all -- the [Int64]/[Int] wrappers
    are stripped by the caller before these apply -- so they live in [theory/]
    and stay VST-free.  Verif proofs apply them one obligation at a time
    ([apply umul_bounds_tight; lia] and the like); nothing searches over them. *)

Require Import ZArith.
Require Import Lia.
Require Import secp256k1.theory.extra_math.

Local Open Scope Z.

(* ================================================================= *)
(** ** Product bounds -- [umul_bounds_tight] / [smul_bounds_tight] and their word specializations. *)

(** Tight unsigned product bound: [x], [y] in [[0, a]] give [x * y] in [[0, a^2]]. *)
Lemma umul_bounds_tight a x y : 0 <= x <= a -> 0 <= y <= a ->
  0 <= x * y <= a * a.
Proof.
intros Hx Hy.
split;[lia|].
transitivity (x * a);[apply Zmult_le_compat_l|apply Zmult_le_compat_r]; try tauto.
lia.
Qed.

(** [umul_bounds_tight] specialized to a [32 x 32 -> 64] unsigned multiply. *)
Lemma umul64_bounds_tight x y : 0 <= x <= 2^32 - 1 -> 0 <= y <= 2^32-1 ->
  0 <= x * y <= 2^64 - 2^33 + 1.
Proof.
apply (umul_bounds_tight (2^32-1)).
Qed.

(** Tight signed product bound: [x], [y] in [[-b, a]] give [x * y] in [[-(a*b), b^2]]. *)
Lemma smul_bounds_tight a b x y : 0 <= a <= b ->
  -b <= x <= a -> -b <= y <= a ->
  -(a * b) <= x * y <= b * b.
Proof.
intros Hab.
destruct (Z.neg_nonneg_cases y).
 split.
  rewrite <- Z.mul_opp_r.
  etransitivity;[apply Z.mul_le_mono_nonneg_l|apply Z.mul_le_mono_nonpos_r];lia.
 etransitivity;[apply (Z.mul_le_mono_nonpos_r (-b))
               |rewrite Z.mul_opp_comm;apply Z.mul_le_mono_nonneg_l];lia.
split.
 rewrite Z.mul_comm, <- Z.mul_opp_l.
 etransitivity;[apply Z.mul_le_mono_nonpos_l|apply Z.mul_le_mono_nonneg_r];lia.
etransitivity;[apply (Z.mul_le_mono_nonneg_r _ b)|apply Z.mul_le_mono_nonneg_l];lia.
Qed.

(** [smul_bounds_tight] specialized to a signed [32 x 32 -> 64] multiply. *)
Lemma smul64_bounds_tight x y : -2^31 <= x <= 2^31 - 1 -> -2^31 <= y <= 2^31 - 1 ->
  -2^62+2^31 <= x * y <= 2^62.
Proof.
assert (H := smul_bounds_tight (2^31 - 1) (2^31) x y).
lia.
Qed.

(** [smul_bounds_tight] specialized to a signed [64 x 64 -> 128] multiply. *)
Lemma smul128_bounds_tight x y : -2^63 <= x <= 2^63 - 1 -> -2^63 <= y <= 2^63 - 1 ->
  -2^126+2^63 <= x * y <= 2^126.
Proof.
assert (H := smul_bounds_tight (2^63 - 1) (2^63) x y).
lia.
Qed.

(** Signed-times-unsigned [32 x 32 -> 64] product stays in the signed [64]-bit range. *)
Lemma sumul64_bounds x y : -2^31 <= x <= 2^31 - 1 -> 0 <= y <= 2^32-1 ->
  -2^63 <= x * y <= 2^63 - 1.
Proof.
intros Hx Hy.
change (2^63) with (2^31 * 2^32).
split.
 rewrite <- Z.mul_opp_l.
 transitivity (-2^31 * y);[|apply Z.mul_le_mono_nonneg_r];lia.
transitivity ((2^31 - 1)*(2^32));[|lia].
transitivity ((2^31 - 1) * y);[apply Z.mul_le_mono_nonneg_r|];lia.
Qed.

(** [sumul64_bounds] with the operands swapped (unsigned times signed). *)
Lemma usmul64_bounds x y : -2^31 <= y <= 2^31 - 1 -> 0 <= x <= 2^32-1 ->
  -2^63 <= x * y <= 2^63 - 1.
Proof.
rewrite Z.mul_comm.
auto using sumul64_bounds.
Qed.

(* ================================================================= *)
(** ** Accumulator bounds -- the [unadd_bounds_*] family. *)

(** Adding an unsigned [32]-bit [b] keeps [ay + b] within [[ax, az]]. *)
Lemma unadd_bounds_unsigned_32 ax ay az b : 0 <= b <= 2^32-1 -> ax <= ay <= az - 2^32 + 1 ->
  ax <= ay + b <= az.
Proof.
lia.
Qed.

(** Adding a signed [32]-bit [b] keeps [ay + b] within [[ax, az]]. *)
Lemma unadd_bounds_signed_32 ax ay az b : -2^31 <= b <= 2^31-1 -> ax + 2^31 <= ay <= az - 2^31 + 1 ->
  ax <= ay + b <= az.
Proof.
lia.
Qed.

(** Adding an unsigned [62]-bit [b] keeps [ay + b] within [[ax, az]]. *)
Lemma unadd_bounds_unsigned_62 ax ay az b : 0 <= b <= 2^62-1 -> ax <= ay <= az - 2^62 + 1 ->
  ax <= ay + b <= az.
Proof.
lia.
Qed.

(** Adding [b >> 62] (which lies in [[-2, 1]]) keeps [ay + (b >> 62)] within [[ax, az]]. *)
Lemma unadd_bounds_shiftr_62 ax ay az b : -2^63 <= b <= 2^63 - 1 -> ax + 2 <= ay <= az - 1 ->
  ax <= ay + (Z.shiftr b 62) <= az.
Proof.
intros Hay Hb.
assert (-2 <= Z.shiftr b 62 < 2) by (apply shiftr_bounds;lia).
lia.
Qed.

(** Adding a boolean's [0]/[1] value keeps [ay + b2z b] within [[ax, az]]. *)
Lemma unadd_bounds_b2z ax ay az b : ax <= ay <= az - 1 ->
  ax <= ay + Z.b2z b <= az.
Proof.
destruct b;simpl;lia.
Qed.

(* ================================================================= *)
(** ** Matrix-row accumulation -- [accum_bound_62]. *)

(** The top-limb bound of [update_fg_62] / [update_fg_62_var]: a row [(c, d)]
    of the divstep transition matrix, applied to two [(e+1)]-bit signed values
    [f], [g], accumulates into [2^63 * 2^e].  The row bound is the safegcd
    invariant [|c| + |d| <= 2^62], plus [c + d > -2^62] to exclude the boundary
    case [c + d = -2^62] where the strict upper bound would fail.  Instantiated
    at [e = 62 * len] by both [update_fg_62] bodies (project-authored; hoisted
    out of those two proofs). *)
Lemma accum_bound_62 : forall (e f g : Z), 0 <= e ->
  -2^(e + 1) <= f <= 2^(e + 1) - 1 ->
  -2^(e + 1) <= g <= 2^(e + 1) - 1 ->
  forall c d, Z.abs c + Z.abs d <= 2^62 -> -2^62 < c + d ->
    -(2^63 * 2^e) <= c * f + d * g < 2^63 * 2^e.
Proof.
  intros e f g He Hf Hg c d Hcd0 Hcd1.
  rewrite <- Z.pow_add_r by lia.
  replace (63 + e) with (62 + (e + 1)) by ring.
  rewrite Z.pow_add_r by lia.
  split.

  - (* lower bound: |c*f| + |d*g| <= 2^62 * 2^(e+1) *)
    assert (Habs : Z.abs (c * f) + Z.abs (d * g) <= 2 ^ 62 * 2 ^ (e + 1)).
    { rewrite !Z.abs_mul.
      apply Z.le_trans with (Z.abs c * Z.max (Z.abs f) (Z.abs g) + Z.abs d * Z.max (Z.abs f) (Z.abs g)).
      + apply Z.add_le_mono; apply Zmult_le_compat_l; lia.
      + rewrite <- Z.mul_add_distr_r.
        apply Zmult_le_compat; lia. }

    lia.

  - (* upper bound: case on the signs of c and d *)
    destruct (Z_le_gt_dec c 0); destruct (Z_le_gt_dec d 0).
    + (* branch: c <= 0 and d <= 0 *)
      apply Z.le_lt_trans with (c * (-2 ^ (e + 1)) + d * (-2 ^ (e + 1))).
      * apply Z.add_le_mono; apply Z.mul_le_mono_nonpos_l; lia.
      * replace (c * -2 ^ (e + 1) + d * -2 ^ (e + 1))
         with (-(c + d) * 2 ^ (e + 1)) by ring.
        apply Zmult_lt_compat_r; lia.

    + (* branch: c <= 0 and d > 0 *)
      apply Z.le_lt_trans with (c * (-2 ^ (e + 1)) + d * (2 ^ (e + 1) - 1)).
      * apply Z.add_le_mono.
        { apply Z.mul_le_mono_nonpos_l; lia. }
        { apply Z.mul_le_mono_nonneg_l; lia. }
      * replace (c * -2 ^ (e + 1) + d * (2 ^ (e + 1) - 1))
         with ((d - c) * (2 ^ (e + 1)) - d) by ring.
        apply Z.le_lt_trans with (2^62 * (2 ^ (e + 1)) - d).
        { apply Z.add_le_mono_r.
          apply Zmult_le_compat_r; lia. }
        { lia. }

    + (* branch: c > 0 and d <= 0 *)
      apply Z.le_lt_trans with (c * (2 ^ (e + 1) - 1) + d * (-2 ^ (e + 1))).
      * apply Z.add_le_mono.
        { apply Z.mul_le_mono_nonneg_l; lia. }
        { apply Z.mul_le_mono_nonpos_l; lia. }
      * replace (c * (2 ^ (e + 1) - 1) + d * (-2 ^ (e + 1)))
         with ((c - d) * (2 ^ (e + 1)) - c) by ring.
        apply Z.le_lt_trans with (2^62 * (2 ^ (e + 1)) - c).
        { apply Z.add_le_mono_r.
          apply Zmult_le_compat_r; lia. }
        { lia. }

    + (* branch: c > 0 and d > 0 *)
      apply Z.le_lt_trans with (c * (2 ^ (e + 1) - 1) + d * (2 ^ (e + 1) - 1)).
      * apply Z.add_le_mono; apply Z.mul_le_mono_nonneg_l; lia.
      * replace (c * (2 ^ (e + 1) - 1) + d * (2 ^ (e + 1) - 1))
         with ((c + d) * (2 ^ (e + 1) - 1)) by ring.
        apply Z.le_lt_trans with (2^62 * (2 ^ (e + 1) - 1)).
        { apply Zmult_le_compat_r; lia. }
        { lia. }
Qed.
