(** * u128_rshift: Proof of body_secp256k1_u128_rshift *)
(** Copyright (C) 2026 remix7531
    SPDX-License-Identifier: MIT *)

Require Import secp256k1.vst.base.
Require Import secp256k1.contract.helper.notations.
Require Import secp256k1.contract.gprog.int128.
Require Import secp256k1.tactics.core.
Require Import secp256k1.tactics.int128.

(* ================================================================= *)
(** ** secp256k1_u128_rshift -- [*r >>= 64]. *)

(** This proves the library's real, general right-shift, specialized to the
    contract's [n = 64] (the only shift amount the scalar code uses). The body
    is [if (n >= 64) { lo = hi >> (n-64); hi = 0; } else ...]; with n = 64 the
    [n >= 64] branch runs (shifting [hi] by 0), and the [n < 64] branch is
    unreachable. *)

Lemma body_secp256k1_u128_rshift:
  semax_body Vprog Gprog
    f_secp256k1_u128_rshift spec_secp256k1_u128_rshift.
Proof.
  start_function.
  subst n.
  (* if (n >= 64) *)
  forward_if.
  (* branch: n = 64 >= 64 -- lo = hi >> 0, hi = 0 *)
  -
    forward. (* _t'4 = r->hi *)
    forward. (* r->lo = _t'4 >> (64 - 64) *)
    forward. (* r->hi = 0 *)
    assert (Hshift : 0 <= u128_val r / 2 ^ 64 < 2 ^ 128).
    { split; [apply Z.div_pos; rep_lia | apply Z.div_lt_upper_bound; rep_lia]. }
    Exists (mkUInt128 (u128_val r / 2 ^ 64) Hshift).
    entailer!.
    apply derives_refl'.
    f_equal.
    unfold uint128_to_val.
    cbn [u128_val].
    f_equal.
    + (* lo limb: hi >>u 0 = (v / 2^64) mod 2^64 *)
      f_equal.
      replace (Int64.repr (Int.unsigned (Int.repr (64 - 64)))) with Int64.zero
        by reflexivity.
      apply Int64.shru_zero.
    + (* hi limb: 0 = ((v / 2^64) / 2^64) mod 2^64, and v / 2^64 < 2^64 *)
      assert (Hzero : u128_val r / 2 ^ 64 / 2 ^ 64 = 0).
      { apply Z.div_small; split;
          [apply Z.div_pos; rep_lia | apply Z.div_lt_upper_bound; rep_lia]. }
      do 2 f_equal.
      rewrite Hzero.
      reflexivity.
  (* branch: n = 64 < 64 -- impossible *)
  -
    rep_lia.
Qed.
