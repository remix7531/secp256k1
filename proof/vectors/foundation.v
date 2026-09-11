(** * vectors.foundation: checked words, arrays and encodings. *)
(** Copyright (C) 2026 remix7531
    SPDX-License-Identifier: MIT *)

From Stdlib Require Import Lia.
From Stdlib Require Import List.
From Stdlib Require Import ZArith.

Require secp256k1.specification.
Import specification.Math.
Import specification.Math.bytes.

Import ListNotations.
Open Scope Z_scope.
Local Open Scope word_scope.

(** Construction preserves literals and rejects values outside the type. *)
Definition highest_byte : (Word 8) := (word_of_Z 8) 255 (ltac:(lia)).

Example highest_byte_preserved : word_val highest_byte = 255.
Proof. reflexivity. Qed.

Fail Definition negative_byte : (Word 8) := (word_of_Z 8) (-1) (ltac:(lia)).
Fail Definition overflowing_byte : (Word 8) := (word_of_Z 8) 256 (ltac:(lia)).
Fail Definition overflowing_word : (Word 32) :=
  word_of_Z 32 (2^32) (ltac:(lia)).
Fail Definition overflowing_byte_array :=
  @words 8 [0; 256] (ltac:(repeat constructor; lia)).
Fail Definition negative_word_array :=
  @words 32 [-1] (ltac:(repeat constructor; lia)).
Fail Definition truncated_encoding : Array (Word 8) 1 :=
  bytes_of_Z 256 1 (ltac:(lia)).
Fail Definition negative_encoding : Array (Word 8) 1 :=
  bytes_of_Z (-1) 1 (ltac:(lia)).

(** Array construction and lookup enforce exact lengths and valid indices. *)
Fail Definition wrong_array_length : Array Z 2 := array_of_list [0].
Fail Definition out_of_bounds :=
  array_get (array_of_list [0]) 1 (ltac:(lia)).
Fail Definition mismatched_zip :=
  array_zip (array_of_list [0]) (array_of_list [0; 1]).
Fail Definition oversized_shift : (Word 8) :=
  word_shr highest_byte 8 (ltac:(lia)).

(** Arithmetic wraps where the operation explicitly calls for reduction. *)
Example byte_add_wraps :
  word_val (word_add highest_byte ((word_of_Z 8) 1 (ltac:(lia)))) = 0.
Proof.
  vm_compute.
  reflexivity.
Qed.

Example byte_rotation :
  word_val (word_rotr ((word_of_Z 8) 0x81 (ltac:(lia))) 1 (ltac:(lia))) = 0xc0.
Proof.
  vm_compute.
  reflexivity.
Qed.

Example byte_shift :
  word_val (word_shr ((word_of_Z 8) 0x81 (ltac:(lia))) 1 (ltac:(lia))) = 0x40.
Proof.
  vm_compute.
  reflexivity.
Qed.

Example byte_complement :
  word_val (not ((word_of_Z 8) 0x81 (ltac:(lia)))) = 0x7e.
Proof.
  vm_compute.
  reflexivity.
Qed.

(** The first byte is the most significant, including leading zero bytes. *)
Example zero_length_encoding :
  bytes_Z (bytes_of_Z 0 0 (ltac:(cbn; lia))) = [].
Proof.
  reflexivity.
Qed.

Example encoding_preserves_leading_zero :
  bytes_Z (bytes_of_Z 0x010203 4 (ltac:(lia))) = [0; 1; 2; 3].
Proof.
  vm_compute.
  reflexivity.
Qed.

Example word32_encoding_order :
  bytes_Z ((@word_to_bytes 4) (word_of_Z 32 0x01234567 (ltac:(lia)))) =
  [0x01; 0x23; 0x45; 0x67].
Proof.
  vm_compute.
  reflexivity.
Qed.
