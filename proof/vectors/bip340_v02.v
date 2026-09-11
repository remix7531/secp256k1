(** * vectors.bip340_v02: BIP-340 test vector 2. *)
(** Copyright (C) 2026 remix7531
    SPDX-License-Identifier: MIT *)

(** Verification result TRUE, sign and verify. The BIP's comment column
    is empty. Built by [make vectors] only: [sign] costs two
    [vm_compute] scalar multiplications and [verify] two, about 25
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

Program Definition v2_sk : Array (Word 8) 32 :=
  bytes_of_Z 0xC90FDAA22168C234C4C6628B80DC1CD129024E088A67CC74020BBEA63B14E5C9 32 _.
Program Definition v2_pk : Array (Word 8) 32 :=
  bytes_of_Z 0xDD308AFEC5777E13121FA72B9CC1B7CC0139715309B086C960E18FD969774EB8 32 _.
Program Definition v2_aux : Array (Word 8) 32 :=
  bytes_of_Z 0xC87AA53824B4D7AE2EB035A2B5BBBCCC080E76CDC6D1692C4B0B62D798E6D906 32 _.
Program Definition v2_msg : Array (Word 8) 32 := @words 8 [
    0x7e; 0x2d; 0x58; 0xd8; 0xb3; 0xbc; 0xdf; 0x1a;
    0xba; 0xde; 0xc7; 0x82; 0x90; 0x54; 0xf9; 0x0d;
    0xda; 0x98; 0x05; 0xaa; 0xb5; 0x6c; 0x77; 0x33;
    0x30; 0x24; 0xb9; 0xd0; 0xa5; 0x08; 0xb7; 0x5c
  ] _.
Program Definition v2_sig : Array (Word 8) 64 :=
  bytes_of_Z
    0x5831AAEED7B44BB74E5EAB94BA9D4294C49BCF2A60728D8B4C200F50DD313C1BAB745879A5AD954A72C45A91C3A51D3C7ADEA98D82F8481E0E1E03674A6F3FB7
    64 _.

Lemma bip340_v2_sign :
  (let* d := decode v2_sk in
   let* sig := sign d v2_msg v2_aux
       (ltac:(unfold message_length_valid; cbn; lia)) in
   Some (bytes_Z (encode sig))) = Some (bytes_Z v2_sig).
Proof.
  vm_cast_no_check (eq_refl (Some (bytes_Z v2_sig))).
Qed.

Lemma bip340_v2_verify :
  (let* px := xonly_decode v2_pk in
   let* sig := decode v2_sig in
   Some (verify px v2_msg sig
           (ltac:(unfold message_length_valid; cbn; lia)))) = Some true.
Proof.
  vm_cast_no_check (eq_refl (Some true)).
Qed.
