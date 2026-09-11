(** * vectors.bip340_v16: BIP-340 test vector 16. *)
(** Copyright (C) 2026 remix7531
    SPDX-License-Identifier: MIT *)

(** Verification result TRUE, sign and verify. The BIP's comment:
    message of size 1 (added 2022-12). Built by [make vectors] only:
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

Program Definition v16_sk : Array (Word 8) 32 :=
  bytes_of_Z 0x0340034003400340034003400340034003400340034003400340034003400340 32 _.
Program Definition v16_pk : Array (Word 8) 32 :=
  bytes_of_Z 0x778CAA53B4393AC467774D09497A87224BF9FAB6F6E68B23086497324D6FD117 32 _.
Program Definition v16_aux : Array (Word 8) 32 :=
  bytes_of_Z 0x0000000000000000000000000000000000000000000000000000000000000000 32 _.
Program Definition v16_msg : Array (Word 8) 1 := @words 8 [ 0x11 ] _.
Program Definition v16_sig : Array (Word 8) 64 :=
  bytes_of_Z
    0x08A20A0AFEF64124649232E0693C583AB1B9934AE63B4C3511F3AE1134C6A303EA3173BFEA6683BD101FA5AA5DBC1996FE7CACFC5A577D33EC14564CEC2BACBF
    64 _.

Lemma bip340_v16_sign :
  (let* d := decode v16_sk in
   let* sig := sign d v16_msg v16_aux
       (ltac:(unfold message_length_valid; cbn; lia)) in
   Some (bytes_Z (encode sig))) = Some (bytes_Z v16_sig).
Proof.
  vm_cast_no_check (eq_refl (Some (bytes_Z v16_sig))).
Qed.

Lemma bip340_v16_verify :
  (let* px := xonly_decode v16_pk in
   let* sig := decode v16_sig in
   Some (verify px v16_msg sig
           (ltac:(unfold message_length_valid; cbn; lia)))) = Some true.
Proof.
  vm_cast_no_check (eq_refl (Some true)).
Qed.
