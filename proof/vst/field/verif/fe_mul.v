(** * vst.field.verif.fe_mul: body proof for secp256k1_fe_impl_mul. *)
(** Copyright (C) 2026 remix7531
    SPDX-License-Identifier: MIT *)

(** Multiplication accepts input magnitudes up to 8 and returns magnitude 1.
    The limb bounds keep [fe_mul_inner]'s 128-bit accumulators in range. *)

Require Import secp256k1.vst.base.
Require Import secp256k1.vst.gprog.
Require secp256k1.specification.
Import specification.Math.
Import specification.Math.field.
Require Import secp256k1.vst.field.contract.
Require Import secp256k1.vst.scaffold.

Lemma body_secp256k1_fe_mul : Pending spec_secp256k1_fe_mul.
Proof.
Admitted.
