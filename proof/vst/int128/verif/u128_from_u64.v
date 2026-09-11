(** * Verif_u128_from_u64: Proof of body_secp256k1_u128_from_u64 *)
(** Copyright (C) 2026 remix7531
    SPDX-License-Identifier: MIT *)

Require Import secp256k1.vst.base.
Require Import secp256k1.vst.helper.notations.
Require Import secp256k1.vst.gprog.
Require Import secp256k1.vst.tactics.core.
Require Import secp256k1.vst.tactics.int128.

(* ================================================================= *)
(** ** secp256k1_u128_from_u64 -- [r = a] (zero-extend to 128 bits). *)

Lemma u64_lt_u128 (a : UInt64) : 0 <= u64_val a < 2^128.
Proof. rep_lia. Qed.

Lemma u64_uint128_repr (a : UInt64) :
  uint128_to_val (mkUInt128 (u64_val a) (u64_lt_u128 a)) =
  (uint64_to_val a, Vlong (Int64.repr 0)).
Proof.
  unfold uint128_to_val, uint64_to_val.
  simpl u128_val.
  do 4 f_equal.
  - apply Z.mod_small; rep_lia.
  - rewrite Z.div_small by rep_lia.
    reflexivity.
Qed.

Lemma body_secp256k1_u128_from_u64:
  semax_body Vprog Gprog
    f_secp256k1_u128_from_u64 spec_secp256k1_u128_from_u64.
Proof.
  start_function.

  forward. (* r->lo = a *)
  forward. (* r->hi = 0 *)

  Exists (mkUInt128 (u64_val a) (u64_lt_u128 a)).
  rewrite u64_uint128_repr.
  entailer!.
Qed.
