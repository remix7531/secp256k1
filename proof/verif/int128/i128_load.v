(** * Verif_i128_load: Proof of body_secp256k1_i128_load *)
(** Copyright (C) 2026 remix7531
    SPDX-License-Identifier: MIT *)

Require Import secp256k1.vst.base.
Require Import secp256k1.contract.helper.notations.
Require Import secp256k1.contract.gprog.int128.
Require Import secp256k1.tactics.core.
Require Import secp256k1.tactics.int128.

(* ================================================================= *)
(** ** secp256k1_i128_load -- [r = lo + hi * 2^64]. *)

(** The loaded value [lo + hi * 2^64] fits in [Int128]: [lo] in [0, 2^64),
    [hi] in [-2^63, 2^63). *)
Lemma i128_load_range (hi : Int64) (lo : UInt64) :
  -2^127 <= u64_val lo + i64_val hi * 2^64 < 2^127.
Proof.
  pose proof (u64_range lo).
  pose proof (i64_range hi).
  assert (0 < 2^64) by (apply Z.pow_pos_nonneg; lia).
  change (2^127) with (2^63 * 2^64).
  nia.
Qed.

(** The struct left by the two field writes (low word [lo], high word the
    sign-extended [hi]) is exactly [int128_to_val] of the loaded value.
    Routes through the [int128_to_val_limb] bridge and the [i128_val_mk]
    projection -- the two signed-automation additions. *)
Lemma i128_load_repr (hi : Int64) (lo : UInt64) :
  int128_to_val (mkInt128 (u64_val lo + i64_val hi * 2^64) (i128_load_range hi lo)) =
  (uint64_to_val lo, int64_to_val hi).
Proof.
  pose proof (u64_range lo).
  assert (0 < 2^64) by (apply Z.pow_pos_nonneg; lia).
  rewrite int128_to_val_limb.
  rewrite i128_val_mk.
  rewrite <- limb_fold0.
  unfold uint64_to_val, int64_to_val.
  f_equal.
  - (* low word: (lo + hi * 2^64) mod 2^64 = lo *)
    do 2 f_equal.
    rewrite Z.mod_add by lia.
    apply Z.mod_small.
    lia.
  - (* high word: (lo + hi * 2^64) / 2^64 = hi *)
    do 2 f_equal.
    rewrite Z.div_add by lia.
    rewrite Z.div_small by lia.
    lia.
Qed.

Lemma body_secp256k1_i128_load:
  semax_body Vprog Gprog
    f_secp256k1_i128_load spec_secp256k1_i128_load.
Proof.
  start_function.

  (* r->hi = hi *)
  forward.
  (* r->lo = lo *)
  forward.

  (* reassembled struct is int128_to_val of the loaded value *)
  Exists (mkInt128 (u64_val lo + i64_val hi * 2^64) (i128_load_range hi lo)).
  rewrite i128_load_repr.
  entailer!.
Qed.
