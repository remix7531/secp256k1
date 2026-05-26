(** * Verif_u128_load: Proof of body_secp256k1_u128_load *)
(** Copyright (C) 2026 remix7531
    SPDX-License-Identifier: MIT *)

Require Import secp256k1.vst.base.
Require Import secp256k1.contract.helper.notations.
Require Import secp256k1.contract.gprog.int128.
Require Import secp256k1.tactics.core.
Require Import secp256k1.tactics.int128.

(* ================================================================= *)
(** ** secp256k1_u128_load -- [r = lo + hi * 2^64]. *)

(** The loaded value [lo + hi * 2^64] fits in [UInt128]: both [lo] and
    [hi] lie in [0, 2^64). *)
Lemma u128_load_range (hi : UInt64) (lo : UInt64) :
  0 <= u64_val lo + u64_val hi * 2^64 < 2^128.
Proof.
  pose proof (u64_range lo).
  pose proof (u64_range hi).
  assert (0 < 2^64) by (apply Z.pow_pos_nonneg; lia).
  change (2^128) with (2^64 * 2^64).
  nia.
Qed.

(** The struct left by the two field writes (low word [lo], high word
    [hi]) is exactly [uint128_to_val] of the loaded value. Routes through
    the [uint128_to_val_limb] bridge; unlike the signed case both limbs
    carry an outer [mod 2^64]. *)
Lemma u128_load_repr (hi : UInt64) (lo : UInt64) :
  uint128_to_val (mkUInt128 (u64_val lo + u64_val hi * 2^64) (u128_load_range hi lo)) =
  (uint64_to_val lo, uint64_to_val hi).
Proof.
  rewrite uint128_to_val_limb.
  cbn [u128_val].
  unfold limb, uint64_to_val.
  f_equal.
  - (* low word: (lo + hi * 2^64) mod 2^64 = lo *)
    do 2 f_equal.
    change ((2^64)^Z.of_nat 0) with 1.
    rewrite Z.div_1_r.
    rewrite Z.mod_add by lia.
    apply Z.mod_small.
    apply u64_range.
  - (* high word: ((lo + hi * 2^64) / 2^64) mod 2^64 = hi *)
    do 2 f_equal.
    change ((2^64)^Z.of_nat 1) with (2^64).
    rewrite Z.div_add by lia.
    rewrite Z.div_small by (apply u64_range).
    rewrite Z.add_0_l.
    apply Z.mod_small.
    apply u64_range.
Qed.

Lemma body_secp256k1_u128_load :
  semax_body Vprog Gprog
    f_secp256k1_u128_load spec_secp256k1_u128_load.
Proof.
  start_function.

  forward. (* r->hi = hi *)
  forward. (* r->lo = lo *)
  Exists (mkUInt128 (u64_val lo + u64_val hi * 2^64) (u128_load_range hi lo)).
  rewrite u128_load_repr.
  entailer!.
Qed.
