(** * vectors.bip340_v00: BIP-340 test vector 0. *)
(** Copyright (C) 2026 remix7531
    SPDX-License-Identifier: MIT *)

(** Verification result TRUE, sign and verify. The BIP's comment column
    is empty. Built by [make vectors] only: [sign] costs one
    [vm_compute] scalar multiplication and [verify] two, about 25
    minutes each on this host, and the two lemmas run in sequence in
    this file. The literals are transcribed from the C arrays in
    [src/modules/schnorrsig/tests_impl.h] and were cross-checked against
    the BIP's own test-vectors.csv. [vm_cast_no_check] hands each
    equation to the kernel once, where [vm_compute] followed by
    [reflexivity] would evaluate it twice. *)

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

Program Definition v0_sk : Array (Word 8) 32 :=
  bytes_of_Z 0x0000000000000000000000000000000000000000000000000000000000000003 32 _.
Program Definition v0_pk : Array (Word 8) 32 :=
  bytes_of_Z 0xF9308A019258C31049344F85F89D5229B531C845836F99B08601F113BCE036F9 32 _.
Program Definition v0_aux : Array (Word 8) 32 :=
  bytes_of_Z 0x0000000000000000000000000000000000000000000000000000000000000000 32 _.
Program Definition v0_msg : Array (Word 8) 32 := @words 8 [
    0x00; 0x00; 0x00; 0x00; 0x00; 0x00; 0x00; 0x00;
    0x00; 0x00; 0x00; 0x00; 0x00; 0x00; 0x00; 0x00;
    0x00; 0x00; 0x00; 0x00; 0x00; 0x00; 0x00; 0x00;
    0x00; 0x00; 0x00; 0x00; 0x00; 0x00; 0x00; 0x00
  ] _.
Program Definition v0_sig : Array (Word 8) 64 :=
  bytes_of_Z
    0xE907831F80848D1069A5371B402410364BDF1C5F8307B0084C55F1CE2DCA821525F66A4A85EA8B71E482A74F382D2CE5EBEEE8FDB2172F477DF4900D310536C0
    64 _.

(** The secret key is [3], so the public key costs two group
    operations. *)
Lemma bip340_v0_keygen :
  (let* d := decode v0_sk in
   let* (_, px) := keygen d in
   Some (fe_val px)) = Some (Z_of_bytes v0_pk).
Proof.
  vm_cast_no_check (eq_refl (Some (Z_of_bytes v0_pk))).
Qed.

Lemma bip340_v0_sign :
  (let* d := decode v0_sk in
   let* sig := sign d v0_msg v0_aux
       (ltac:(unfold message_length_valid; cbn; lia)) in
   Some (bytes_Z (encode sig))) = Some (bytes_Z v0_sig).
Proof.
  vm_cast_no_check (eq_refl (Some (bytes_Z v0_sig))).
Qed.

Lemma bip340_v0_verify :
  (let* px := xonly_decode v0_pk in
   let* sig := decode v0_sig in
   Some (verify px v0_msg sig
           (ltac:(unfold message_length_valid; cbn; lia)))) = Some true.
Proof.
  vm_cast_no_check (eq_refl (Some true)).
Qed.
