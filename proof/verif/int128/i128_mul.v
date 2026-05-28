(** * Verif_i128_mul: Proof of body_secp256k1_i128_mul *)
(** Copyright (C) 2026 remix7531
    SPDX-License-Identifier: MIT *)

Require Import secp256k1.vst.base.
Require Import secp256k1.contract.helper.notations.
Require Import secp256k1.contract.gprog.int128.
Require Import secp256k1.tactics.core.
Require Import secp256k1.tactics.int128.

(* ================================================================= *)
(** ** secp256k1_i128_mul -- [r = a * b]. *)

(** The struct left by the two field writes is exactly [int128_to_val]
    of [mul_i64 a b].  The low word stored is [Int64.repr (a*b)], which
    matches the [int128_to_val] low limb [Int64.repr ((a*b) mod 2^64)]
    by [Int64.repr] congruence modulo [2^64] ([eqm_of_mod_eq]); the high
    word is the sign-extended [(a*b)/2^64], matching directly. *)
Lemma i128_mul_repr (a b : Int64) :
  (Vlong (Int64.repr (i64_val a * i64_val b)),
   int64_to_val (i128_hi (mul_i64 a b))) =
  int128_to_val (mul_i64 a b).
Proof.
  unfold int128_to_val, int64_to_val, i128_hi, mul_i64.
  simpl.
  f_equal.
  f_equal.
  (* low word: Int64.repr (a*b) = Int64.repr ((a*b) mod 2^64) *)
  apply Int64.eqm_samerepr.
  apply eqm_of_mod_eq.
  reflexivity.
Qed.

Lemma body_secp256k1_i128_mul :
  semax_body Vprog Gprog
    f_secp256k1_i128_mul spec_secp256k1_i128_mul.
Proof.
  start_function.

  (* _t'1 = secp256k1_mul128(a, b, &hi) -- writes hi to the local &hi *)
  forward_call (a, b, v_hi, Tsh).
  (* r->lo = (uint64_t)_t'1 *)
  forward.
  (* _t'2 = hi *)
  forward.
  (* r->hi = (uint64_t)_t'2 *)
  forward.

  (* reassembled struct is int128_to_val (mul_i64 a b) *)
  rewrite i128_mul_repr.
  entailer!.
Qed.
