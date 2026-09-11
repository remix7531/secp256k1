(** * vst.hash.verif.sha256_write: body proof for secp256k1_sha256_write. *)
(** Copyright (C) 2026 remix7531
    SPDX-License-Identifier: MIT *)

(** The compression step is called through the hash context's function
    pointer. *)

Require Import secp256k1.vst.base.
Require Import secp256k1.vst.gprog.
Require secp256k1.specification.
Import specification.Math.
Import specification.Math.sha256.
Require Import secp256k1.vst.hash.contract.
Require Import secp256k1.vst.scaffold.

Lemma body_secp256k1_sha256_write : Pending spec_secp256k1_sha256_write.
Proof.
Admitted.
