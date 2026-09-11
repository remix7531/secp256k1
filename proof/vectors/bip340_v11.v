(** * vectors.bip340_v11: BIP-340 test vector 11. *)
(** Copyright (C) 2026 remix7531
    SPDX-License-Identifier: MIT *)

(** Verification result FALSE, verify only. The BIP's comment: sig[0:32]
    is not an X coordinate on the curve. Built by [make vectors] only:
    [verify] costs two [vm_compute] scalar multiplications, about 25
    minutes each on this host. The literals are transcribed from the C
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

Program Definition v11_pk : Array (Word 8) 32 :=
  bytes_of_Z 0xDFF1D77F2A671C5F36183726DB2341BE58FEAE1DA2DECED843240F7B502BA659 32 _.
Program Definition v11_msg : Array (Word 8) 32 := @words 8 [
    0x24; 0x3f; 0x6a; 0x88; 0x85; 0xa3; 0x08; 0xd3;
    0x13; 0x19; 0x8a; 0x2e; 0x03; 0x70; 0x73; 0x44;
    0xa4; 0x09; 0x38; 0x22; 0x29; 0x9f; 0x31; 0xd0;
    0x08; 0x2e; 0xfa; 0x98; 0xec; 0x4e; 0x6c; 0x89
  ] _.
Program Definition v11_sig : Array (Word 8) 64 :=
  bytes_of_Z
    0x4A298DACAE57395A15D0795DDBFD1DCB564DA82B0F269BC70A74F8220429BA1D69E89B4C5564D00349106B8497785DD7D1D713A8AE82B32FA79D5F7FC407D39B
    64 _.

Lemma bip340_v11_verify :
  (let* px := xonly_decode v11_pk in
   let* sig := decode v11_sig in
   Some (verify px v11_msg sig
           (ltac:(unfold message_length_valid; cbn; lia)))) = Some false.
Proof.
  vm_cast_no_check (eq_refl (Some false)).
Qed.
