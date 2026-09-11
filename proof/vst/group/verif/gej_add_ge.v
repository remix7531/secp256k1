(** * vst.group.verif.gej_add_ge: body proof for secp256k1_gej_add_ge. *)
(** Copyright (C) 2026 remix7531
    SPDX-License-Identifier: MIT *)

(** The [rr_alt] and [m_alt] substitutions handle point doubling within
    the addition formula. The model distinguishes doubling from the chord
    case through [group.padd]. *)

Require Import secp256k1.vst.base.
Require Import secp256k1.vst.gprog.
Require secp256k1.specification.
Import specification.Math.
Import specification.Math.raw.
Require Import secp256k1.vst.group.contract.
Require Import secp256k1.vst.scaffold.

Lemma body_secp256k1_gej_add_ge : Pending spec_secp256k1_gej_add_ge.
Proof.
Admitted.
