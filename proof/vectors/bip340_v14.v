(** * vectors.bip340_v14: BIP-340 test vector 14. *)
(** Copyright (C) 2026 remix7531
    SPDX-License-Identifier: MIT *)

(** Verification result FALSE, verify only. The BIP's comment: public
    key is not a valid X coordinate because it exceeds the field size.
    The lemma is a parse failure and runs in seconds; the file is here
    so that every vector has one file. The literals are transcribed from
    the C arrays in [src/modules/schnorrsig/tests_impl.h] and were
    cross-checked against the BIP's own test-vectors.csv.
    [vm_cast_no_check] hands each equation to the kernel once, where
    [vm_compute] followed by [reflexivity] would evaluate it twice. *)

From Stdlib Require Import Lia.
From Stdlib Require Import List.
From Stdlib Require Import ZArith.
Import ListNotations.

Require secp256k1.specification.
Import specification.Math.
Import specification.Math.bytes.
Import specification.Math.field.
Import specification.Math.group.
Import specification.Math.scalar.
Import specification.Math.schnorr.
Import specification.Math.sha256.

Open Scope Z_scope.
Local Obligation Tactic := (repeat constructor; lia).

Program Definition v14_pk : Array (Word 8) 32 :=
  bytes_of_Z 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEFFFFFC30 32 _.

Lemma bip340_v14_pubkey_parse_fails : xonly_decode v14_pk = None.
Proof.
  vm_cast_no_check (eq_refl (@None Fe)).
Qed.
