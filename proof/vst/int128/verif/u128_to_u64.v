(** * Verif_u128_to_u64: Proof of body_secp256k1_u128_to_u64 *)
(** Copyright (C) 2026 remix7531
    SPDX-License-Identifier: MIT *)

Require Import secp256k1.vst.base.
Require Import secp256k1.vst.helper.notations.
Require Import secp256k1.vst.gprog.
Require Import secp256k1.vst.tactics.core.
Require Import secp256k1.vst.tactics.int128.

(* ================================================================= *)
(** ** secp256k1_u128_to_u64 -- [low 64 bits of *a]. *)

(** The function body dereferences the struct pointer, reads the [lo]
    field, and returns it.  That is two [forward] steps. *)

Lemma body_secp256k1_u128_to_u64:
  semax_body Vprog Gprog
    f_secp256k1_u128_to_u64 spec_secp256k1_u128_to_u64.
Proof.
  start_function.
  forward. (* _t'1 = a->lo *)
  forward. (* return _t'1 *)
  Exists (u128_lo x).
  unfold u128_lo, uint64_to_val.
  simpl.
  entailer!.
Qed.
