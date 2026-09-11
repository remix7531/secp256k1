(** * vectors.bip340_v17: BIP-340 test vector 17. *)
(** Copyright (C) 2026 remix7531
    SPDX-License-Identifier: MIT *)

(** Verification result TRUE, sign and verify. The BIP's comment:
    message of size 17 (added 2022-12). Built by [make vectors] only:
    [sign] costs two [vm_compute] scalar multiplications and [verify]
    two, about 25 minutes each on this host, and the two lemmas run in
    sequence in this file. The literals are transcribed from the C
    arrays in [src/modules/schnorrsig/tests_impl.h] and were
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

Program Definition v17_sk : Array (Word 8) 32 :=
  bytes_of_Z 0x0340034003400340034003400340034003400340034003400340034003400340 32 _.
Program Definition v17_pk : Array (Word 8) 32 :=
  bytes_of_Z 0x778CAA53B4393AC467774D09497A87224BF9FAB6F6E68B23086497324D6FD117 32 _.
Program Definition v17_aux : Array (Word 8) 32 :=
  bytes_of_Z 0x0000000000000000000000000000000000000000000000000000000000000000 32 _.
Program Definition v17_msg : Array (Word 8) 17 := @words 8 [
    0x01; 0x02; 0x03; 0x04; 0x05; 0x06; 0x07; 0x08;
    0x09; 0x0a; 0x0b; 0x0c; 0x0d; 0x0e; 0x0f; 0x10;
    0x11
  ] _.
Program Definition v17_sig : Array (Word 8) 64 :=
  bytes_of_Z
    0x5130F39A4059B43BC7CAC09A19ECE52B5D8699D1A71E3C52DA9AFDB6B50AC370C4A482B77BF960F8681540E25B6771ECE1E5A37FD80E5A51897C5566A97EA5A5
    64 _.

Lemma bip340_v17_sign :
  (let* d := decode v17_sk in
   let* sig := sign d v17_msg v17_aux
       (ltac:(unfold message_length_valid; cbn; lia)) in
   Some (bytes_Z (encode sig))) = Some (bytes_Z v17_sig).
Proof.
  vm_cast_no_check (eq_refl (Some (bytes_Z v17_sig))).
Qed.

Lemma bip340_v17_verify :
  (let* px := xonly_decode v17_pk in
   let* sig := decode v17_sig in
   Some (verify px v17_msg sig
           (ltac:(unfold message_length_valid; cbn; lia)))) = Some true.
Proof.
  vm_cast_no_check (eq_refl (Some true)).
Qed.
