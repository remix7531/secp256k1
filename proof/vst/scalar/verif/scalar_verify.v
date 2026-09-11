(** * Verif_scalar_verify: Proof of body_secp256k1_scalar_verify *)
(** Copyright (C) 2026 remix7531
    SPDX-License-Identifier: MIT *)

Require Import secp256k1.vst.base.
Require Import secp256k1.vst.helper.notations.
Require Import secp256k1.vst.gprog.
Require Import secp256k1.vst.tactics.core.
Require Import secp256k1.vst.tactics.int128.
Require Import secp256k1.vst.tactics.scalar.

(* ================================================================= *)
(** ** secp256k1_scalar_verify -- [no-op; a unchanged]. *)

(** [SECP256K1_SCALAR_VERIFY] is neutralized to empty in the extraction
    unit, so the body is [Sskip]: the function leaves its argument
    unchanged.  The proof is a single symbolic step. *)
Lemma body_secp256k1_scalar_verify:
  semax_body Vprog Gprog
    f_secp256k1_scalar_verify spec_secp256k1_scalar_verify.
Proof.
  start_function.

  (* return (Sskip-neutralized body) *)
  forward.
  entailer!.
Qed.
