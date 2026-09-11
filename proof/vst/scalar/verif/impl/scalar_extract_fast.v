(** * Verif_extract_fast: Proof of body_secp256k1_scalar_extract_fast *)
(** Copyright (C) 2026 remix7531
    SPDX-License-Identifier: MIT *)

Require Import secp256k1.vst.base.
Require Import secp256k1.vst.helper.notations.
Require Import secp256k1.vst.gprog.
Require Import secp256k1.vst.scalar.impl.
Require Import secp256k1.vst.tactics.core.
Require Import secp256k1.vst.tactics.int128.
Require Import secp256k1.vst.tactics.scalar.

(* ================================================================= *)
(** ** extract_fast -- [n = acc.c0; acc >>= 64] (acc < 2^128). *)

Lemma body_secp256k1_scalar_extract_fast:
  semax_body Vprog Gprog f_secp256k1_scalar_extract_fast spec_secp256k1_scalar_extract_fast.
Proof.
  start_function.

  (* *n = acc->c0 *)
  forward. (* _t'2 = acc->c0 *)
  forward. (* *n = _t'2 *)

  (* acc->c0 = acc->c1 *)
  forward. (* _t'1 = acc->c1 *)
  forward. (* acc->c0 = _t'1 *)

  (* acc->c1 = 0 *)
  forward. (* acc->c1 = 0 *)

  (* Witnesses: n = acc_lo acc, acc' = acc_shift acc *)
  Exists (acc_lo acc) (acc_shift acc).
  entailer!.

  (* ===== Postcondition: C struct = acc_to_val (acc_shift acc) ===== *)
  apply derives_refl'.
  unfold acc_to_val.
  replace (acc_val (acc_shift acc)) with (acc_val acc / 2^64)
    by (unfold acc_shift; reflexivity).
  (* limb 1 of shifted = 0 (acc < 2^128) *)
  rewrite (Zdiv.Zdiv_Zdiv (acc_val acc) (2^64) (2^64)) by lia.
  change (2^64 * 2^64) with (2^128).
  (* limb 2 of shifted = 0 (acc < 2^192) *)
  rewrite (Zdiv.Zdiv_Zdiv (acc_val acc) (2^64) (2^128)) by lia.
  change (2^64 * 2^128) with (2^192).
  rewrite (Z.div_small (acc_val acc) (2^192)) by rep_lia.
  rewrite (Z.div_small (acc_val acc) (2^128)) by rep_lia.
  reflexivity.
Qed.
