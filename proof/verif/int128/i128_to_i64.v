(** * Verif_i128_to_i64: Proof of body_secp256k1_i128_to_i64 *)
(** Copyright (C) 2026 remix7531
    SPDX-License-Identifier: MIT *)

Require Import secp256k1.vst.base.
Require Import secp256k1.contract.helper.notations.
Require Import secp256k1.contract.gprog.int128.
Require Import secp256k1.tactics.core.
Require Import secp256k1.tactics.int128.

(* ================================================================= *)
(** ** secp256k1_i128_to_i64 -- [r = (int64)a]. *)

(** The C body's [VERIFY_CHECK] expands to nothing without [VERIFY], so
    the function is just [return (int64_t)secp256k1_i128_to_u64(a)]. The
    call returns [i128_val a mod 2^64]; the [(int64_t)] cast reinterprets
    that bit pattern signed.

    Under the precondition [-2^63 <= i128_val a < 2^63] the value already
    fits [Int64], so the signed reinterpretation recovers [i128_val a].
    The two C values agree because [Int64.repr] is invariant modulo
    [2^64]: [Int64.repr (i128_val a mod 2^64) = Int64.repr (i128_val a)].
    Routes through the [eqm_of_mod_eq] bridge in [tactics/core]. *)
Lemma i128_to_i64_repr (a : Int128) (vret : UInt64)
  (Hlo : -2^63 <= i128_val a) (Hhi : i128_val a < 2^63)
  (Hvret : u64_val vret = i128_val a mod 2^64) :
  uint64_to_val vret = int64_to_val (mkInt64 (i128_val a) (conj Hlo Hhi)).
Proof.
  unfold uint64_to_val, int64_to_val.
  rewrite Hvret.
  f_equal.
  apply Int64.eqm_samerepr.
  apply Int64.eqm_sym.
  apply eqm_of_mod_eq.
  reflexivity.
Qed.

Lemma body_secp256k1_i128_to_i64 :
  semax_body Vprog Gprog
    f_secp256k1_i128_to_i64 spec_secp256k1_i128_to_i64.
Proof.
  start_function.

  (* _t'1 = secp256k1_i128_to_u64(a) *)
  forward_call (a_ptr, a, sh).
  Intros vret.
  rename H1 into Hvret.

  (* return (int64_t)_t'1 *)
  forward.

  (* the signed reinterpretation recovers [i128_val a] in range *)
  Exists (mkInt64 (i128_val a) (conj H H0)).
  entailer!.
  apply i128_to_i64_repr.
  exact Hvret.
Qed.
