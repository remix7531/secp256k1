(** * model.tests_field: known-answer checks for the NEW [model.field] operations. *)
(** Copyright (C) 2026 remix7531
    SPDX-License-Identifier: MIT *)

(** Executable sanity checks of [model/field.v]'s field-element operations
    against independently known values, so a reviewer can see what the model
    means before reading any VST proof.  Every check is a closed equation
    discharged by [vm_compute; reflexivity]; each names where its expected
    value comes from.  This file is VST-free (imports only [model.constants]
    and [model.field]) and carries no axioms.

    [secp256k1_P] itself (decimal / hex / [2^256 - 2^32 - 977]) is already
    checked in [model/tests.v:29-38]; this file covers only the operations
    [model/field.v] adds on top of that constant.  A residue's proof
    component is intentionally never compared directly (two different
    [Program Definition] obligations for the same value are not
    [vm_compute]-convertible without an explicit proof-irrelevance step): every
    check below goes through [fe_val] (or, for byte lists / booleans / [Z],
    compares values that carry no such component at all). *)

From Stdlib Require Import ZArith.
From Stdlib Require Import List.
From Stdlib Require Import Lia.
Import ListNotations.

Require Import secp256k1.model.constants.
Require Import secp256k1.model.field.

Open Scope Z_scope.

(* ================================================================= *)
(** ** Concrete field elements used below. *)

Definition t_fe_12345 : Fe := mkFe 12345 (ltac:(unfold secp256k1_P; lia)).
Definition t_fe_Pm1 : Fe := mkFe (secp256k1_P - 1) (ltac:(pose proof secp256k1_P_range; lia)).
Definition t_fe_five : Fe := mkFe 5 (ltac:(unfold secp256k1_P; lia)).
Definition t_fe_seven : Fe := mkFe 7 (ltac:(unfold secp256k1_P; lia)).
Definition t_fe_ten : Fe := mkFe 10 (ltac:(unfold secp256k1_P; lia)).
Definition t_fe_eleven : Fe := mkFe 11 (ltac:(unfold secp256k1_P; lia)).
Definition t_fe_hundred : Fe := mkFe 100 (ltac:(unfold secp256k1_P; lia)).
Definition t_fe_three : Fe := mkFe 3 (ltac:(unfold secp256k1_P; lia)).

(* ================================================================= *)
(** ** Byte conversions -- [fe_of_bytes] / [fe_to_bytes] round trips.

    Three 32-byte big-endian patterns, each obviously representing a value
    far below [p] (which sits only [2^32 + 977] below [2^256]): 32 zero
    bytes, 31 zero bytes then a trailing [1], and the byte sequence
    [1..32]. *)

Definition b_zero : list Z := repeat 0 32.
Definition b_one : list Z := repeat 0 31 ++ [1].
Definition b_pattern : list Z :=
  [ 1; 2; 3; 4; 5; 6; 7; 8; 9; 10; 11; 12; 13; 14; 15; 16;
    17; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31; 32 ].

(** [fe_to_bytes (fe_of_bytes b) = b] for each pattern (no reduction happens
    since every value is already [< p]). *)
Lemma chk_fe_bytes_roundtrip_zero : fe_to_bytes (fe_of_bytes b_zero) = b_zero.
Proof. vm_compute. reflexivity. Qed.

Lemma chk_fe_bytes_roundtrip_one : fe_to_bytes (fe_of_bytes b_one) = b_one.
Proof. vm_compute. reflexivity. Qed.

Lemma chk_fe_bytes_roundtrip_pattern : fe_to_bytes (fe_of_bytes b_pattern) = b_pattern.
Proof. vm_compute. reflexivity. Qed.

(** [fe_of_bytes (fe_to_bytes x) = x] (compared via [fe_val], per the file
    header) on a small element and on the top boundary [p-1]. *)
Lemma chk_fe_roundtrip_bytes_12345 :
  fe_val (fe_of_bytes (fe_to_bytes t_fe_12345)) = fe_val t_fe_12345.
Proof. vm_compute. reflexivity. Qed.

Lemma chk_fe_roundtrip_bytes_Pm1 :
  fe_val (fe_of_bytes (fe_to_bytes t_fe_Pm1)) = fe_val t_fe_Pm1.
Proof. vm_compute. reflexivity. Qed.

(* ================================================================= *)
(** ** Modular inverse -- [fe_inv], via Fermat's little theorem
    ([secp256k1_P_prime]). *)

(** [fe_inv 12345 * 12345 = 1 mod p] (Python: [pow(12345, p-2, p) * 12345 %
    p == 1]). *)
Lemma chk_fe_inv_12345 :
  fe_val (fe_mul (fe_inv t_fe_12345) t_fe_12345) = 1.
Proof. vm_compute. reflexivity. Qed.

(** [-1] is its own inverse: [(p-1) * (p-1) = 1 mod p] is the algebraic
    identity [(-1)*(-1) = 1], needing no external cross-check. *)
Lemma chk_fe_inv_Pm1_self :
  fe_val (fe_inv t_fe_Pm1) = secp256k1_P - 1.
Proof. vm_compute. reflexivity. Qed.

(* ================================================================= *)
(** ** Square root -- [fe_sqrt], the [(p+1)/4]-power formula ([p = 3 mod 4]). *)

(** [fe_sqr 7 = 49] is a perfect square by construction, so [fe_sqrt] must
    return [Some] on it.  Python: [pow(49, (p+1)//4, p) == p - 7] -- the
    addition-chain formula returns the *other* root ([-7 mod p]), not [7]
    itself, for this input; [(p-7)^2 mod p == 49] confirms it is a genuine
    square root. *)
Lemma chk_fe_sqrt_residue :
  match fe_sqrt (fe_sqr t_fe_seven) with
  | Some r => fe_val r = fe_val (fe_negate t_fe_seven)
  | None => False
  end.
Proof. vm_compute. reflexivity. Qed.

(** [3] is a quadratic non-residue mod [p] (Python, Euler's criterion:
    [pow(3, (p-1)//2, p) == p - 1]), so [fe_sqrt 3] must return [None]. *)
Lemma chk_fe_sqrt_nonresidue : fe_sqrt t_fe_three = None.
Proof. vm_compute. reflexivity. Qed.

(* ================================================================= *)
(** ** [fe_half] / [fe_negate] / [fe_add_int] / [fe_mul_int] on concrete
    values. *)

(** Halving an even residue is exact division: [10 / 2 = 5]. *)
Lemma chk_fe_half_even : fe_val (fe_half t_fe_ten) = 5.
Proof. vm_compute. reflexivity. Qed.

(** Halving an odd residue [a] uses [(a + p) / 2] (exact, since [p] is odd so
    [a + p] is even) -- the standard "add the modulus to make it even" trick,
    stated symbolically so no 78-digit literal is needed. *)
Lemma chk_fe_half_odd : fe_val (fe_half t_fe_eleven) = (secp256k1_P + 11) / 2.
Proof. vm_compute. reflexivity. Qed.

(** [fe_negate a = p - a] for [0 < a < p], by definition -- stated
    symbolically against [secp256k1_P] rather than its decimal value. *)
Lemma chk_fe_negate : fe_val (fe_negate t_fe_five) = secp256k1_P - 5.
Proof. vm_compute. reflexivity. Qed.

(** [fe_add_int 100 50 = 150], well below [p]: no reduction occurs. *)
Lemma chk_fe_add_int : fe_val (fe_add_int t_fe_hundred 50) = 150.
Proof. vm_compute. reflexivity. Qed.

(** [fe_mul_int 7 6 = 42], well below [p]: no reduction occurs. *)
Lemma chk_fe_mul_int : fe_val (fe_mul_int t_fe_seven 6) = 42.
Proof. vm_compute. reflexivity. Qed.

(* ================================================================= *)
(** ** [fe_is_zero] / [fe_is_odd] / [fe_cmp] on the boundary values [0], [1],
    [p-1]. *)

Lemma chk_fe_is_zero_zero : fe_is_zero fe_zero = true.
Proof. vm_compute. reflexivity. Qed.

Lemma chk_fe_is_zero_one : fe_is_zero fe_one = false.
Proof. vm_compute. reflexivity. Qed.

Lemma chk_fe_is_zero_Pm1 : fe_is_zero t_fe_Pm1 = false.
Proof. vm_compute. reflexivity. Qed.

Lemma chk_fe_is_odd_zero : fe_is_odd fe_zero = false.
Proof. vm_compute. reflexivity. Qed.

Lemma chk_fe_is_odd_one : fe_is_odd fe_one = true.
Proof. vm_compute. reflexivity. Qed.

(** [p] is odd (it is [2^256 - 2^32 - 977], even minus even minus odd), so
    [p-1] is even. *)
Lemma chk_fe_is_odd_Pm1 : fe_is_odd t_fe_Pm1 = false.
Proof. vm_compute. reflexivity. Qed.

Lemma chk_fe_cmp_0_1 : fe_cmp fe_zero fe_one = -1.
Proof. vm_compute. reflexivity. Qed.

Lemma chk_fe_cmp_1_0 : fe_cmp fe_one fe_zero = 1.
Proof. vm_compute. reflexivity. Qed.

Lemma chk_fe_cmp_0_Pm1 : fe_cmp fe_zero t_fe_Pm1 = -1.
Proof. vm_compute. reflexivity. Qed.

Lemma chk_fe_cmp_Pm1_0 : fe_cmp t_fe_Pm1 fe_zero = 1.
Proof. vm_compute. reflexivity. Qed.

Lemma chk_fe_cmp_Pm1_refl : fe_cmp t_fe_Pm1 t_fe_Pm1 = 0.
Proof. vm_compute. reflexivity. Qed.
