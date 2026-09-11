(** * Verif_i128_from_i64: Proof of body_secp256k1_i128_from_i64 *)
(** Copyright (C) 2026 remix7531
    SPDX-License-Identifier: MIT *)

Require Import secp256k1.vst.base.
Require Import secp256k1.vst.helper.notations.
Require Import secp256k1.vst.gprog.
Require Import secp256k1.vst.tactics.core.
Require Import secp256k1.vst.tactics.int128.

(* ================================================================= *)
(** ** secp256k1_i128_from_i64 -- [r = (i128)a]. *)

(** Sign extension via division: for [a] in [Int64] range, the high word is
    the same whether we shift by 63 (the C code) or divide by [2^64] (the
    [int128_to_val] high word).  Both equal [-1] when [a < 0] and [0]
    otherwise. *)
Lemma i128_from_i64_div_eq (a : Int64) :
  i64_val a / 2^63 = i64_val a / 2^64.
Proof.
  pose proof (i64_range a) as Hr.
  destruct (Z_lt_dec (i64_val a) 0) as [Hneg | Hpos].
  - (* a < 0: both quotients are -1 *)
    assert (E1 : i64_val a / 2^63 = -1).
    { symmetry.
      apply (Z.div_unique (i64_val a) (2^63) (-1) (i64_val a + 2^63)); lia. }
    assert (E2 : i64_val a / 2^64 = -1).
    { symmetry.
      apply (Z.div_unique (i64_val a) (2^64) (-1) (i64_val a + 2^64)); lia. }
    lia.
  - (* a >= 0: both quotients are 0 *)
    rewrite Z.div_small by lia.
    rewrite Z.div_small by lia.
    reflexivity.
Qed.

(** The C arithmetic shift [(uint64_t)(a >> 63)] reproduces the high word
    [i64_val a / 2^64] stored by [int128_to_val].  Routes through
    [Int64.shr_div_two_p] and the sign-extension fact above. *)
Lemma i128_from_i64_shr (a : Int64) :
  Int64.shr (Int64.repr (i64_val a)) (Int64.repr 63) =
  Int64.repr (i64_val a / 2^64).
Proof.
  pose proof (i64_range a) as Hr.
  rewrite (Int64_shr_div (i64_val a) 63) by lia.
  rewrite i128_from_i64_div_eq.
  reflexivity.
Qed.

(** The struct left by the two field writes (low word [a], high word the
    arithmetic shift) is exactly [int128_to_val] of the sign-extended value.
    The low word matches because [Int64.repr] is invariant under [mod 2^64];
    the high word matches by [i128_from_i64_shr]. *)
Lemma i128_from_i64_repr (a : Int64) :
  (int64_to_val a, Vlong (Int64.repr (i64_val a / 2^64))) =
  int128_to_val (i64_to_i128 a).
Proof.
  unfold i64_to_i128, int128_to_val, int64_to_val.
  simpl.
  f_equal.
  (* low word: Int64.repr (i64_val a) = Int64.repr (i64_val a mod 2^64) *)
  f_equal.
  apply Int64.eqm_samerepr.
  change (Z.pow_pos 2 64) with Int64.modulus.
  apply Zbits.eqmod_mod.
  reflexivity.
Qed.

Lemma body_secp256k1_i128_from_i64:
  semax_body Vprog Gprog
    f_secp256k1_i128_from_i64 spec_secp256k1_i128_from_i64.
Proof.
  start_function.
  forward. (* r->hi = (uint64_t)(a >> 63) *)
  forward. (* r->lo = (uint64_t)a *)
  Exists (i64_to_i128 a).
  change (Int.unsigned (Int.repr 63)) with 63.
  rewrite i128_from_i64_shr.
  rewrite i128_from_i64_repr.
  entailer!.
Qed.
