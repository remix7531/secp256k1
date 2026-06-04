(** * Verif_extract: Proof of body_secp256k1_scalar_extract *)
(** Copyright (C) 2026 remix7531
    SPDX-License-Identifier: MIT *)

Require Import secp256k1.vst.base.
Require Import secp256k1.contract.helper.notations.
Require Import secp256k1.contract.gprog.scalar.
Require Import secp256k1.contract.impl.scalar.
Require Import secp256k1.tactics.core.
Require Import secp256k1.tactics.int128.
Require Import secp256k1.tactics.scalar.

(* ================================================================= *)
(** ** extract -- [n = acc.c0; acc >>= 64]. *)

Lemma body_secp256k1_scalar_extract:
  semax_body Vprog Gprog f_secp256k1_scalar_extract spec_secp256k1_scalar_extract.
Proof.
  start_function.

  (* *n = acc->c0 *)
  forward. (* _t'3 = acc->c0 *)
  forward. (* *n = _t'3 *)

  (* acc->c0 = acc->c1 *)
  forward. (* _t'2 = acc->c1 *)
  forward. (* acc->c0 = _t'2 *)

  (* acc->c1 = acc->c2 *)
  forward. (* _t'1 = acc->c2 *)
  forward. (* acc->c1 = _t'1 *)

  (* acc->c2 = 0 *)
  forward. (* acc->c2 = 0 *)

  (* Witnesses: n = acc_lo acc, acc' = acc_shift acc *)
  Exists (acc_lo acc) (acc_shift acc).
  entailer!.

  (* ===== Postcondition: C struct = acc_to_val (acc_shift acc) ===== *)
  apply derives_refl'.
  unfold acc_to_val.
  replace (acc_val (acc_shift acc)) with (acc_val acc / 2^64)
    by (unfold acc_shift; reflexivity).
  rewrite (Zdiv.Zdiv_Zdiv (acc_val acc) (2^64) (2^64)) by lia.
  change (2^64 * 2^64) with (2^128).
  rewrite (Zdiv.Zdiv_Zdiv (acc_val acc) (2^64) (2^128)) by lia.
  change (2^64 * 2^128) with (2^192).
  rewrite (Z.div_small (acc_val acc) (2^192)) by rep_lia.
  reflexivity.
Qed.
