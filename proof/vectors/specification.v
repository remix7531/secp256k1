(** * vectors.specification: focused public boundary checks. *)
(** Copyright (C) 2026 remix7531
    SPDX-License-Identifier: MIT *)

From Stdlib Require Import Lia.
From Stdlib Require Import ZArith.

Require secp256k1.specification.
Import specification.Math.
Import specification.Math.algebra.
Import specification.Math.bytes.
Import specification.Math.integer_bytes.
Import specification.Math.field.
Import specification.Math.scalar.
Import specification.Math.raw.
Import specification.Math.group.
Import specification.Math.roots.
Import specification.Math.sha256.
Import specification.Math.schnorr.

Open Scope Z_scope.
Local Open Scope word_scope.

Definition boundary_byte : Word 8 :=
  word_of_Z 8 255 (ltac:(lia)).

Definition boundary_word32 : Word 32 :=
  word_of_Z 32 0xffffffff (ltac:(lia)).

Example word8_codec_roundtrip :
  @decode (Word 8) 1 (Word_decode 1)
    (@encode (Word 8) 1 (Word_encode 1) boundary_byte) =
  Some boundary_byte.
Proof.
  change (Some (@word_of_bytes 1 (@word_to_bytes 1 boundary_byte)) =
    Some boundary_byte).
  rewrite word_of_bytes_to_bytes.
  reflexivity.
Qed.

Example word32_codec_roundtrip :
  @decode (Word 32) 4 (Word_decode 4)
    (@encode (Word 32) 4 (Word_encode 4) boundary_word32) =
  Some boundary_word32.
Proof.
  change (Some (@word_of_bytes 4 (@word_to_bytes 4 boundary_word32)) =
    Some boundary_word32).
  rewrite word_of_bytes_to_bytes.
  reflexivity.
Qed.

Definition field_modulus_bytes : Array (Word 8) 32 :=
  bytes_of_Z secp256k1_P 32 (ltac:(unfold secp256k1_P; lia)).

Definition scalar_modulus_bytes : Array (Word 8) 32 :=
  bytes_of_Z secp256k1_N 32 (ltac:(unfold secp256k1_N; lia)).

Example field_decode_rejects_modulus :
  @decode Fe 32 Fe_decode field_modulus_bytes = None.
Proof. vm_compute. reflexivity. Qed.

Example scalar_decode_rejects_modulus :
  @decode Scalar 32 Scalar_decode scalar_modulus_bytes = None.
Proof. vm_compute. reflexivity. Qed.

Example field_reduce_zero : fe_val (fe_reduce 0) = 0.
Proof. vm_compute. reflexivity. Qed.

Example field_reduce_last_canonical :
  fe_val (fe_reduce (secp256k1_P - 1)) = secp256k1_P - 1.
Proof. vm_compute. reflexivity. Qed.

Example field_reduce_modulus : fe_val (fe_reduce secp256k1_P) = 0.
Proof. vm_compute. reflexivity. Qed.

Example scalar_reduce_zero : scalar_val (scalar_reduce 0) = 0.
Proof. vm_compute. reflexivity. Qed.

Example scalar_reduce_last_canonical :
  scalar_val (scalar_reduce (secp256k1_N - 1)) = secp256k1_N - 1.
Proof. vm_compute. reflexivity. Qed.

Example scalar_reduce_modulus :
  scalar_val (scalar_reduce secp256k1_N) = 0.
Proof. vm_compute. reflexivity. Qed.

Example checked_point_accepts_infinity :
  point_of_coordinates_checked raw.PInf = Some group.PInf.
Proof. reflexivity. Qed.

Example checked_point_rejects_invalid_coordinates :
  point_of_coordinates_checked (raw.PAff fe_zero fe_zero) = None.
Proof. vm_compute. reflexivity. Qed.

Example square_root_rejects_nonresidue :
  fe_sqrt (fe_reduce 3) = None.
Proof. vm_compute. reflexivity. Qed.

Example lifted_point_has_even_ordinate :
  match lift_x_even (fe_reduce 2) with
  | Some (group.PAff _ y _) => fe_is_odd y = false
  | _ => False
  end.
Proof. vm_compute. reflexivity. Qed.

Lemma sha256_length_valid_exact_bound (n : nat) :
  sha256_length_valid n <-> Z.of_nat n <= 2 ^ 61 - 1.
Proof.
  unfold sha256_length_valid.
  lia.
Qed.

Lemma message_length_valid_exact_bound (n : nat) :
  message_length_valid n <-> Z.of_nat n <= 2 ^ 61 - 129.
Proof.
  unfold message_length_valid, sha256_length_valid.
  rewrite Nat2Z.inj_add.
  cbn.
  lia.
Qed.

(** Both exponent representations select field powers through [Power]. *)
Example field_power_unary :
  fe_val ((fe_reduce 2 ^ 5%nat)%M) = 32.
Proof. vm_compute. reflexivity. Qed.

Example field_power_binary_zero :
  fe_val ((fe_zero ^ 0%N)%M) = 1.
Proof. vm_compute. reflexivity. Qed.

Example field_power_binary_reduces :
  fe_val ((fe_reduce 2 ^ 256%N)%M) = 2 ^ 32 + 977.
Proof. vm_compute. reflexivity. Qed.

Example scalar_power_binary_odd :
  scalar_val ((scalar_reduce (secp256k1_N - 1) ^ 5%N)%M) =
  secp256k1_N - 1.
Proof. vm_compute. reflexivity. Qed.
