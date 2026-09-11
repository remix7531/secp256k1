(** * vectors.bip340_v03: BIP-340 test vector 3. *)
(** Copyright (C) 2026 remix7531
    SPDX-License-Identifier: MIT *)

(** Verification result TRUE, sign and verify. The BIP's comment: test
    fails if msg is reduced modulo p or n. Built by [make vectors] only:
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

Program Definition v3_sk : Array (Word 8) 32 :=
  bytes_of_Z 0x0B432B2677937381AEF05BB02A66ECD012773062CF3FA2549E44F58ED2401710 32 _.
Program Definition v3_pk : Array (Word 8) 32 :=
  bytes_of_Z 0x25D1DFF95105F5253C4022F628A996AD3A0D95FBF21D468A1B33F8C160D8F517 32 _.
Program Definition v3_aux : Array (Word 8) 32 :=
  bytes_of_Z 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF 32 _.
Program Definition v3_msg : Array (Word 8) 32 := @words 8 [
    0xff; 0xff; 0xff; 0xff; 0xff; 0xff; 0xff; 0xff;
    0xff; 0xff; 0xff; 0xff; 0xff; 0xff; 0xff; 0xff;
    0xff; 0xff; 0xff; 0xff; 0xff; 0xff; 0xff; 0xff;
    0xff; 0xff; 0xff; 0xff; 0xff; 0xff; 0xff; 0xff
  ] _.
Program Definition v3_sig : Array (Word 8) 64 :=
  bytes_of_Z
    0x7EB0509757E246F19449885651611CB965ECC1A187DD51B64FDA1EDC9637D5EC97582B9CB13DB3933705B32BA982AF5AF25FD78881EBB32771FC5922EFC66EA3
    64 _.

Lemma bip340_v3_sign :
  (let* d := decode v3_sk in
   let* sig := sign d v3_msg v3_aux
       (ltac:(unfold message_length_valid; cbn; lia)) in
   Some (bytes_Z (encode sig))) = Some (bytes_Z v3_sig).
Proof.
  vm_cast_no_check (eq_refl (Some (bytes_Z v3_sig))).
Qed.

Lemma bip340_v3_verify :
  (let* px := xonly_decode v3_pk in
   let* sig := decode v3_sig in
   Some (verify px v3_msg sig
           (ltac:(unfold message_length_valid; cbn; lia)))) = Some true.
Proof.
  vm_cast_no_check (eq_refl (Some true)).
Qed.
