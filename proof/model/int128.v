(** * model.int128: pure functional model of the 64/128/192/256/512-bit integers *)
(** Copyright (C) 2026 remix7531
    SPDX-License-Identifier: MIT *)

Require Import ZArith.
Require Import Lia.
Require Import secp256k1.theory.arithmetic.
Require Export secp256k1.model.types.

Open Scope Z_scope.

(** Deterministic obligation preprocessing: just [intros].  The default
    [program_simpl] auto-solver spins on the [(N - a) mod N] obligation
    shapes now that floyd (which used to override it) is no longer loaded. *)
Local Obligation Tactic := intros.

(* ================================================================= *)
(** ** Unsigned operations -- [mul_64] / [u128_lo] / [u256_limb].
    (The word types [UInt64] .. [UInt512] live in [model.types]; the
    accumulator [Acc] in [model.acc].) *)

(** 64 x 64 -> 128-bit multiplication. *)
Program Definition mul_64 (a b : UInt64) : UInt128 :=
  mkUInt128 (u64_val a * u64_val b) _.
Next Obligation.
  destruct a as [av [Ha0 Ha1]], b as [bv [Hb0 Hb1]].
  simpl.
  split.
  - apply Z.mul_nonneg_nonneg; lia.
  - change (Z.pow_pos 2 128) with (2^64 * 2^64).
    apply Z.mul_lt_mono_nonneg; lia.
Qed.

(** 256 x 256 -> 512-bit multiplication. *)
Program Definition mul_256 (a b : UInt256) : UInt512 :=
  mkUInt512 (u256_val a * u256_val b) _.
Next Obligation.
  destruct a as [av [Ha0 Ha1]], b as [bv [Hb0 Hb1]].
  simpl.
  split.
  - apply Z.mul_nonneg_nonneg; lia.
  - change (Z.pow_pos 2 512) with (2^256 * 2^256).
    apply Z.mul_lt_mono_nonneg; lia.
Qed.

(** Low 64 bits of a [UInt128]. *)
Program Definition u128_lo (x : UInt128) : UInt64 :=
  mkUInt64 (u128_val x mod 2^64) _.
Next Obligation.
  apply Z.mod_pos_bound.
  lia.
Qed.

(** High 64 bits of a [UInt128]. *)
Program Definition u128_hi (x : UInt128) : UInt64 :=
  mkUInt64 ((u128_val x / 2^64) mod 2^64) _.
Next Obligation.
  apply Z.mod_pos_bound.
  lia.
Qed.

(** Extract the [i]-th 64-bit limb of a [UInt256] as a [UInt64]. *)
Program Definition u256_limb (x : UInt256) (i : nat) : UInt64 :=
  mkUInt64 (limb (2^64) (u256_val x) i) _.
Next Obligation.
  apply Z.mod_pos_bound.
  lia.
Qed.

(* ================================================================= *)
(** ** Signed operations -- [mul_i64] / [i128_det] / [i128_hi].
    ([Int64] / [Int128] live in [model.types].) *)

(** Sign-extend an [Int64] to [Int128]. *)
Program Definition i64_to_i128 (a : Int64) : Int128 :=
  mkInt128 (i64_val a) _.
Next Obligation.
  destruct a as [av [Ha0 Ha1]].
  simpl.
  split; lia.
Qed.

(** 64 x 64 -> 128-bit signed multiplication. *)
Program Definition mul_i64 (a b : Int64) : Int128 :=
  mkInt128 (i64_val a * i64_val b) _.
Next Obligation.
  destruct a as [av [Ha0 Ha1]], b as [bv [Hb0 Hb1]].
  simpl.
  assert (Hav : Z.abs av <= 2^63) by (rewrite Z.abs_le; lia).
  assert (Hbv : Z.abs bv <= 2^63) by (rewrite Z.abs_le; lia).
  assert (Hab : Z.abs (av * bv) <= 2^63 * 2^63).
  { rewrite Z.abs_mul.
    apply Z.mul_le_mono_nonneg;
    [apply Z.abs_nonneg | exact Hav | apply Z.abs_nonneg | exact Hbv]. }
  rewrite Z.abs_le in Hab.
  split; [lia | change (2^127) with (2^63 * 2^63 * 2); lia].
Qed.

(** Determinant: a*d - b*c, from four [Int64] inputs. *)
Program Definition i128_det (a b c d : Int64) : Int128 :=
  mkInt128 (i64_val a * i64_val d - i64_val b * i64_val c) _.
Next Obligation.
  destruct a as [av Ha], b as [bv Hb], c as [cv Hc], d as [dv Hd].
  simpl.
  nia.
Qed.

(** Low 64 bits of an [Int128] (unsigned interpretation). *)
Program Definition i128_lo (x : Int128) : UInt64 :=
  mkUInt64 (i128_val x mod 2^64) _.
Next Obligation.
  apply Z.mod_pos_bound.
  lia.
Qed.

(** High 64 bits of an [Int128] (signed interpretation). *)
Program Definition i128_hi (x : Int128) : Int64 :=
  mkInt64 (i128_val x / 2^64) _.
Next Obligation.
  destruct x as [v [Hv0 Hv1]].
  simpl.
  split.
  - apply Z.le_trans with (-2^127 / 2^64).
    + reflexivity.
    + apply Z.div_le_mono; lia.
  - apply Z.div_lt_upper_bound; lia.
Qed.

