(** * vectors.bip340_v01: BIP-340 test vector 1. *)
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

Program Definition v1_sk : Array (Word 8) 32 :=
  bytes_of_Z 0xB7E151628AED2A6ABF7158809CF4F3C762E7160F38B4DA56A784D9045190CFEF 32 _.
Program Definition v1_pk : Array (Word 8) 32 :=
  bytes_of_Z 0xDFF1D77F2A671C5F36183726DB2341BE58FEAE1DA2DECED843240F7B502BA659 32 _.
Program Definition v1_aux : Array (Word 8) 32 :=
  bytes_of_Z 0x0000000000000000000000000000000000000000000000000000000000000001 32 _.
Program Definition v1_msg : Array (Word 8) 32 := @words 8 [
    0x24; 0x3f; 0x6a; 0x88; 0x85; 0xa3; 0x08; 0xd3;
    0x13; 0x19; 0x8a; 0x2e; 0x03; 0x70; 0x73; 0x44;
    0xa4; 0x09; 0x38; 0x22; 0x29; 0x9f; 0x31; 0xd0;
    0x08; 0x2e; 0xfa; 0x98; 0xec; 0x4e; 0x6c; 0x89
  ] _.
Program Definition v1_sig : Array (Word 8) 64 :=
  bytes_of_Z
    0x6896BD60EEAE296DB48A229FF71DFE071BDE413E6D43F917DC8DCF8C78DE33418906D11AC976ABCCB20B091292BFF4EA897EFCB639EA871CFA95F6DE339E4B0A
    64 _.

Lemma bip340_v1_sign :
  (let* d := decode v1_sk in
   let* sig := sign d v1_msg v1_aux
       (ltac:(unfold message_length_valid; cbn; lia)) in
   Some (bytes_Z (encode sig))) = Some (bytes_Z v1_sig).
Proof.
  vm_cast_no_check (eq_refl (Some (bytes_Z v1_sig))).
Qed.

Lemma bip340_v1_verify :
  (let* px := xonly_decode v1_pk in
   let* sig := decode v1_sig in
   Some (verify px v1_msg sig
           (ltac:(unfold message_length_valid; cbn; lia)))) = Some true.
Proof.
  vm_cast_no_check (eq_refl (Some true)).
Qed.
