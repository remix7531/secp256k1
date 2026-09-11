(** * vectors.bip340_v15: BIP-340 test vector 15. *)
(** Copyright (C) 2026 remix7531
    SPDX-License-Identifier: MIT *)

(** Verification result TRUE, sign and verify. The BIP's comment:
    message of size 0 (added 2022-12). Built by [make vectors] only:
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

Program Definition v15_sk : Array (Word 8) 32 :=
  bytes_of_Z 0x0340034003400340034003400340034003400340034003400340034003400340 32 _.
Program Definition v15_pk : Array (Word 8) 32 :=
  bytes_of_Z 0x778CAA53B4393AC467774D09497A87224BF9FAB6F6E68B23086497324D6FD117 32 _.
Program Definition v15_aux : Array (Word 8) 32 :=
  bytes_of_Z 0x0000000000000000000000000000000000000000000000000000000000000000 32 _.
Program Definition v15_msg : Array (Word 8) 0 := @words 8 [] _.
Program Definition v15_sig : Array (Word 8) 64 :=
  bytes_of_Z
    0x71535DB165ECD9FBBC046E5FFAEA61186BB6AD436732FCCC25291A55895464CF6069CE26BF03466228F19A3A62DB8A649F2D560FAC652827D1AF0574E427AB63
    64 _.

Lemma bip340_v15_sign :
  (let* d := decode v15_sk in
   let* sig := sign d v15_msg v15_aux
       (ltac:(unfold message_length_valid; cbn; lia)) in
   Some (bytes_Z (encode sig))) = Some (bytes_Z v15_sig).
Proof.
  vm_cast_no_check (eq_refl (Some (bytes_Z v15_sig))).
Qed.

Lemma bip340_v15_verify :
  (let* px := xonly_decode v15_pk in
   let* sig := decode v15_sig in
   Some (verify px v15_msg sig
           (ltac:(unfold message_length_valid; cbn; lia)))) = Some true.
Proof.
  vm_cast_no_check (eq_refl (Some true)).
Qed.
