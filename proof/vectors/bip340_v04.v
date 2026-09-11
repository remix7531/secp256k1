(** * vectors.bip340_v04: BIP-340 test vector 4. *)
(** Copyright (C) 2026 remix7531
    SPDX-License-Identifier: MIT *)

(** Verification result TRUE, verify only. The BIP's comment column is
    empty. Built by [make vectors] only: [verify] costs two [vm_compute]
    scalar multiplications, about 25 minutes each on this host. The
    literals are transcribed from the C arrays in
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

Program Definition v4_pk : Array (Word 8) 32 :=
  bytes_of_Z 0xD69C3509BB99E412E68B0FE8544E72837DFA30746D8BE2AA65975F29D22DC7B9 32 _.
Program Definition v4_msg : Array (Word 8) 32 := @words 8 [
    0x4d; 0xf3; 0xc3; 0xf6; 0x8f; 0xcc; 0x83; 0xb2;
    0x7e; 0x9d; 0x42; 0xc9; 0x04; 0x31; 0xa7; 0x24;
    0x99; 0xf1; 0x78; 0x75; 0xc8; 0x1a; 0x59; 0x9b;
    0x56; 0x6c; 0x98; 0x89; 0xb9; 0x69; 0x67; 0x03
  ] _.
Program Definition v4_sig : Array (Word 8) 64 :=
  bytes_of_Z
    0x00000000000000000000003B78CE563F89A0ED9414F5AA28AD0D96D6795F9C6376AFB1548AF603B3EB45C9F8207DEE1060CB71C04E80F593060B07D28308D7F4
    64 _.

Lemma bip340_v4_verify :
  (let* px := xonly_decode v4_pk in
   let* sig := decode v4_sig in
   Some (verify px v4_msg sig
           (ltac:(unfold message_length_valid; cbn; lia)))) = Some true.
Proof.
  vm_cast_no_check (eq_refl (Some true)).
Qed.
