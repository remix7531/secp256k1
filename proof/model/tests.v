(** * model.tests: known-answer checks for the model. *)
(** Copyright (C) 2026 remix7531
    SPDX-License-Identifier: MIT *)

(** Executable sanity checks of [model/] against independently known values,
    so a reviewer can see what the model means before reading any VST proof.
    Every check is a closed equation discharged by [vm_compute; reflexivity]
    (a handful of the [is_modular_inverse] checks need a few extra steps,
    since that predicate is a conjunction of an implication, not a single
    equation).  Each check names where its expected value comes from.  This
    file is intentionally VST-free (imports only other [model/] files) and
    carries no axioms. *)

Require Import ZArith.
Require Import Coq.ZArith.Znumtheory.
Require Import Lia.
Require Import secp256k1.model.constants.
Require Import secp256k1.model.field.
Require Import secp256k1.model.scalar.
Require Import secp256k1.model.modinv.
Require Import secp256k1.model.int128.

Open Scope Z_scope.

(* ================================================================= *)
(** ** Field prime and group order -- against SEC2 / [src/scalar_4x64_impl.h]. *)

(** [p], decimal (SEC2 "secp256k1", field size). *)
Lemma chk_P_dec :
  secp256k1_P = 115792089237316195423570985008687907853269984665640564039457584007908834671663.
Proof. vm_compute. reflexivity. Qed.

(** [p], hex (SEC2: [FFFFFFFF FFFFFFFF FFFFFFFF FFFFFFFF FFFFFFFF FFFFFFFF
    FFFFFFFE FFFFFC2F]), independent of the [2^256 - 2^32 - 977] definition. *)
Lemma chk_P_hex :
  secp256k1_P = 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEFFFFFC2F.
Proof. vm_compute. reflexivity. Qed.

(** [n], decimal (SEC2 "secp256k1", group order). *)
Lemma chk_N_dec :
  secp256k1_N = 115792089237316195423570985008687907852837564279074904382605163141518161494337.
Proof. vm_compute. reflexivity. Qed.

(** [n]'s four 64-bit limbs recombine to [n] ([SECP256K1_N_0..3] of
    [src/scalar_4x64_impl.h]). *)
Lemma chk_N_limbs : secp256k1_N = N_0 + N_1 * 2^64 + N_2 * 2^128 + N_3 * 2^192.
Proof. vm_compute. reflexivity. Qed.

(** [2^256 - n]'s limbs ([SECP256K1_N_C_0..2]). *)
Lemma chk_N_C_limbs : 2^256 - secp256k1_N = N_C_0 + N_C_1 * 2^64 + N_C_2 * 2^128.
Proof. vm_compute. reflexivity. Qed.

(** [n] is odd: [n_h = floor((n-1)/2)] and [2*n_h + 1 = n]
    ([SECP256K1_N_H_0..3]). *)
Lemma chk_N_H_formula : secp256k1_N_H = (secp256k1_N - 1) / 2.
Proof. vm_compute. reflexivity. Qed.

Lemma chk_N_as_2H : 2 * secp256k1_N_H + 1 = secp256k1_N.
Proof. vm_compute. reflexivity. Qed.

(* ================================================================= *)
(** ** GLV endomorphism -- identities documented in [src/scalar_impl.h]. *)

(** "lambda and beta are primitive cube roots of unity" ([scalar_impl.h],
    the comment above [secp256k1_scalar_split_lambda]): [lambda^3 = 1 mod n]
    and [lambda <> 1]. *)
Lemma chk_lambda_cube :
  (secp256k1_lambda * secp256k1_lambda * secp256k1_lambda) mod secp256k1_N = 1.
Proof. vm_compute. reflexivity. Qed.

Lemma chk_lambda_ne_1 : secp256k1_lambda <> 1.
Proof. unfold secp256k1_lambda. lia. Qed.

(** "lambda^2 + lambda == -1 mod n" (same comment: lambda is a root of
    [X^2 + X + 1]), i.e. [lambda^2 + lambda + 1 = 0 mod n]. *)
Lemma chk_lambda_min_poly :
  (secp256k1_lambda * secp256k1_lambda + secp256k1_lambda + 1) mod secp256k1_N = 0.
Proof. vm_compute. reflexivity. Qed.

(** The reduced GLV basis vector [(a1, b1)] lies in the kernel of
    [phi(a + b*l) = a + b*lambda mod n] ([scalar_impl.h] comment above
    [secp256k1_scalar_split_lambda]): [a1 + b1*lambda = 0 mod n].  The header
    also records [a1 = b2] byte-for-byte (same 16-byte constant is printed
    for both), and the model stores [minus_b1_z = -b1] / [minus_b2_z = -b2
    mod n] directly, so substituting [a1 = b2 = n - minus_b2_z] and
    [b1 = -minus_b1_z] turns the kernel condition into an equation over just
    the model's own constants: [minus_b2_z + minus_b1_z*lambda = 0 mod n]
    (checked independently in Python: [(minus_b2 + minus_b1*lambda) % n ==
    0]). *)
Lemma chk_glv_kernel :
  (minus_b2_z + minus_b1_z * secp256k1_lambda) mod secp256k1_N = 0.
Proof. vm_compute. reflexivity. Qed.

(** [g1 = round(2^384 * b2 / n)] and [g2 = round(2^384 * (-b1) / n)]
    ([scalar_impl.h]: "g1, g2 are precomputed constants used to replace
    division with a rounded multiplication", with [d = n]).  Using
    [b2 = n - minus_b2_z] and [-b1 = minus_b1_z], and the standard
    round-to-nearest identity [round(x/y) = (2*x + y) / (2*y)] for positive
    [x, y] (checked in Python against the literal [g1_z] / [g2_z] hex
    values first). *)
Lemma chk_glv_g1 :
  g1_z = (2 * (2^384 * (secp256k1_N - minus_b2_z)) + secp256k1_N) / (2 * secp256k1_N).
Proof. vm_compute. reflexivity. Qed.

Lemma chk_glv_g2 :
  g2_z = (2 * (2^384 * minus_b1_z) + secp256k1_N) / (2 * secp256k1_N).
Proof. vm_compute. reflexivity. Qed.

(* ================================================================= *)
(** ** Scalar arithmetic -- small hand-checkable values. *)

Definition t_Nm1 : Scalar := mkScalar (secp256k1_N - 1) (ltac:(pose proof secp256k1_N_range; lia)).
Definition t_two : Scalar := mkScalar 2 (ltac:(unfold secp256k1_N; lia)).
Definition t_three : Scalar := mkScalar 3 (ltac:(unfold secp256k1_N; lia)).
Definition t_five : Scalar := mkScalar 5 (ltac:(unfold secp256k1_N; lia)).
Definition t_NH : Scalar := mkScalar secp256k1_N_H (ltac:(pose proof secp256k1_N_H_range; lia)).

(** [(n-1) + 1 = 0 mod n]. *)
Lemma chk_scalar_add : scalar_val (scalar_add t_Nm1 scalar_one) = 0.
Proof. vm_compute. reflexivity. Qed.

(** [2 * n_h = n - 1] (since [n = 2*n_h + 1]). *)
Lemma chk_scalar_mul : scalar_val (scalar_mul t_two t_NH) = secp256k1_N - 1.
Proof. vm_compute. reflexivity. Qed.

(** [-1 = n - 1 mod n]. *)
Lemma chk_scalar_negate : scalar_val (scalar_negate scalar_one) = secp256k1_N - 1.
Proof. vm_compute. reflexivity. Qed.

(** [(n-1)/2 = n_h] (halving the even residue [n-1]). *)
Lemma chk_scalar_half : scalar_val (scalar_half t_Nm1) = secp256k1_N_H.
Proof. vm_compute. reflexivity. Qed.

(** [mul_shift_var(3, 5, 2)]: round [3*5 / 2^2] to nearest; [15/4 = 3.75],
    which rounds (half-up) to [4] (Python: [15//4 + (15//2) % 2 == 4]). *)
Lemma chk_scalar_mulshift : scalar_mul_shift t_three t_five 2 = 4.
Proof. vm_compute. reflexivity. Qed.

(** [(p-1) + 1 = 0 mod p], the field analogue of [chk_scalar_add]. *)
Definition t_Pm1 : Fe := mkFe (secp256k1_P - 1) (ltac:(pose proof secp256k1_P_range; lia)).
Definition t_fe_one : Fe := mkFe 1 (ltac:(unfold secp256k1_P; lia)).

Lemma chk_fe_add : fe_val (fe_add t_Pm1 t_fe_one) = 0.
Proof. vm_compute. reflexivity. Qed.

(* ================================================================= *)
(** ** Modular inverse -- [is_modular_inverse] (the spec, not the [safegcd]
    construction: [mod_inv] lives outside [model/], in
    [theory/modinv/construction], out of scope for this VST-free file). *)

(** [3 * 5 = 15 = 1 mod 7]: [5] is the inverse of [3] mod [7]. *)
Lemma chk_is_modinv_small : is_modular_inverse 3 7 5.
Proof.
  unfold is_modular_inverse.
  split; [lia|].
  split; [lia|].
  intros _. vm_compute. reflexivity.
Qed.

(** [a = 0] maps to [r = 0]; the coprimality conjunct is vacuous since
    [gcd(0,7) = 7 <> 1] (rules out [rel_prime 0 7] via gcd uniqueness). *)
Lemma chk_is_modinv_zero : is_modular_inverse 0 7 0.
Proof.
  unfold is_modular_inverse.
  split; [lia|].
  split; [lia|].
  intros H.
  assert (H7 : Zis_gcd 0 7 7) by (exact (Zis_gcd_0_abs 7)).
  destruct (Zis_gcd_uniqueness_apart_sign _ _ _ _ H H7); lia.
Qed.

(** [pow(2, -1, n)] (Python), the modular inverse of [2] against the full
    256-bit group order. *)
Lemma chk_is_modinv_2N :
  is_modular_inverse 2 secp256k1_N
    57896044618658097711785492504343953926418782139537452191302581570759080747169.
Proof.
  unfold is_modular_inverse.
  split; [unfold secp256k1_N; lia|].
  split; [lia|].
  intros _. vm_compute. reflexivity.
Qed.

(* ================================================================= *)
(** ** Jacobi symbol -- [jacobi_symbol], cross-checked against a standard
    (non-recursive-model) Python implementation of [(a | n)]. *)

Lemma chk_jacobi_2_7 : jacobi_symbol 2 7 = 1.
Proof. vm_compute. reflexivity. Qed.

Lemma chk_jacobi_3_7 : jacobi_symbol 3 7 = -1.
Proof. vm_compute. reflexivity. Qed.

(** [jacobi(5, n)], Python: a from-scratch [jacobi(a, n)] (factor-out-2s /
    quadratic-reciprocity loop), evaluated at the full group order. *)
Lemma chk_jacobi_5_N : jacobi_symbol 5 secp256k1_N = -1.
Proof. vm_compute. reflexivity. Qed.

(* ================================================================= *)
(** ** Limb round trips -- [scalar_to_u256] / [u256_limb]. *)

(** Widening [n-1] to a [UInt256] and recombining its four 64-bit limbs
    recovers the original value. *)
Lemma chk_limb_roundtrip_Nm1 :
  let w := scalar_to_u256 t_Nm1 in
  u64_val (u256_limb w 0) + u64_val (u256_limb w 1) * 2^64
  + u64_val (u256_limb w 2) * 2^128 + u64_val (u256_limb w 3) * 2^192
  = secp256k1_N - 1.
Proof. vm_compute. reflexivity. Qed.

(** Same round trip on an arbitrary (non-degenerate) 256-bit pattern. *)
Definition t_pattern : UInt256 :=
  mkUInt256 0x0123456789ABCDEF0123456789ABCDEF0123456789ABCDEF0123456789ABCD
    (ltac:(lia)).

Lemma chk_limb_roundtrip_pattern :
  u64_val (u256_limb t_pattern 0) + u64_val (u256_limb t_pattern 1) * 2^64
  + u64_val (u256_limb t_pattern 2) * 2^128 + u64_val (u256_limb t_pattern 3) * 2^192
  = u256_val t_pattern.
Proof. vm_compute. reflexivity. Qed.
