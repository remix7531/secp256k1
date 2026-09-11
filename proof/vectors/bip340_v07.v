(** * vectors.bip340_v07: BIP-340 test vector 7. *)
(** Copyright (C) 2026 remix7531
    SPDX-License-Identifier: MIT *)

(** Verification result FALSE, verify only. The BIP's comment: negated
    message. Built by [make vectors] only: [verify] costs two
    [vm_compute] scalar multiplications, about 25 minutes each on this
    host. The literals are transcribed from the C arrays in
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

Program Definition v7_pk : Array (Word 8) 32 :=
  bytes_of_Z 0xDFF1D77F2A671C5F36183726DB2341BE58FEAE1DA2DECED843240F7B502BA659 32 _.
Program Definition v7_msg : Array (Word 8) 32 := @words 8 [
    0x24; 0x3f; 0x6a; 0x88; 0x85; 0xa3; 0x08; 0xd3;
    0x13; 0x19; 0x8a; 0x2e; 0x03; 0x70; 0x73; 0x44;
    0xa4; 0x09; 0x38; 0x22; 0x29; 0x9f; 0x31; 0xd0;
    0x08; 0x2e; 0xfa; 0x98; 0xec; 0x4e; 0x6c; 0x89
  ] _.
Program Definition v7_sig : Array (Word 8) 64 :=
  bytes_of_Z
    0x1FA62E331EDBC21C394792D2AB1100A7B432B013DF3F6FF4F99FCB33E0E1515F28890B3EDB6E7189B630448B515CE4F8622A954CFE545735AAEA5134FCCDB2BD
    64 _.

Lemma bip340_v7_verify :
  (let* px := xonly_decode v7_pk in
   let* sig := decode v7_sig in
   Some (verify px v7_msg sig
           (ltac:(unfold message_length_valid; cbn; lia)))) = Some false.
Proof.
  vm_cast_no_check (eq_refl (Some false)).
Qed.
