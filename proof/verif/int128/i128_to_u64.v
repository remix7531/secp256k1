(** * Verif_i128_to_u64: Proof of body_secp256k1_i128_to_u64 *)
(** Copyright (C) 2026 remix7531
    SPDX-License-Identifier: MIT *)

Require Import secp256k1.vst.base.
Require Import secp256k1.contract.helper.notations.
Require Import secp256k1.contract.gprog.int128.
Require Import secp256k1.tactics.core.
Require Import secp256k1.tactics.int128.

(* ================================================================= *)
(** ** secp256k1_i128_to_u64 -- [r = a mod 2^64]. *)

(** The function body dereferences the struct pointer, reads the [lo]
    field, and returns it.  The [lo] field of [int128_to_val a] is
    [Vlong (Int64.repr (i128_val a mod 2^64))], which is exactly
    [uint64_to_val (i128_lo a)], so [i128_lo a] is the postcondition
    witness.  That is two [forward] steps. *)

Lemma body_secp256k1_i128_to_u64 :
  semax_body Vprog Gprog
    f_secp256k1_i128_to_u64 spec_secp256k1_i128_to_u64.
Proof.
  start_function.

  (* _t'1 = a->lo *)
  forward.
  (* return _t'1 *)
  forward.

  (* the [lo] field is exactly [uint64_to_val (i128_lo a)] *)
  Exists (i128_lo a).
  entailer!.
Qed.
