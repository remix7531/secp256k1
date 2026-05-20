(** * verif.util.memclear_explicit: body proof for secp256k1_memclear_explicit *)
(** Copyright (C) 2026 remix7531
    SPDX-License-Identifier: MIT *)

Require Import secp256k1.vst.base.
Require Import secp256k1.contract.helper.notations.
Require Import secp256k1.contract.gprog.util.
Require Import secp256k1.contract.util.
Require Import secp256k1.tactics.core.

(* ================================================================= *)
(** ** secp256k1_memclear_explicit -- cleanse [n] bytes (delegates to memzero). *)

Lemma body_secp256k1_memclear_explicit:
  semax_body Vprog Gprog
    f_secp256k1_memclear_explicit spec_secp256k1_memclear_explicit.
Proof.
  start_function.

  (* ===== Delegate: cleanse [n] bytes via memzero_explicit ===== *)
  (* secp256k1_memzero_explicit(p, n) *)
  forward_call (sh, p, n).
  entailer!.
Qed.
