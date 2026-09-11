(** * theory.scalar.limbs: how a scalar and the group order are encoded. *)
(** Copyright (C) 2026 remix7531
    SPDX-License-Identifier: MIT *)

(** [Math.scalar] defines a scalar as a residue modulo [n]. This file
    collects the additional facts needed by the C's four-limb encoding:

    - the 64-bit limb decompositions of [n], of its complement [2^256 - n] and
      of its half [floor(n/2)], mirroring the [SECP256K1_N_*] /
      [SECP256K1_N_C_*] / [SECP256K1_N_H_*] macros of
      [src/scalar_4x64_impl.h] limb for limb;
    - the four GLV basis constants [secp256k1_scalar_split_lambda] divides by
      ([minus_b1], [minus_b2], [g1], [g2] in [src/scalar_impl.h]);
    - the machine-word views of a scalar ([scalar_to_u256], [reduce_256]) and
      the rounding helper [scalar_mul_shift] that
      [secp256k1_scalar_mul_shift_var] computes.

    Every constant here is a fact about the encoding: the value it belongs to
    is [Math.scalar]'s [secp256k1_N], and the lemmas below are what tie the two
    together.  The out-of-tree known-answer checks cross-check the literals
    against the formulas they claim to satisfy. *)

Require Import ZArith.
Require Import Lia.

Require Import secp256k1.theory.integers.machine.
Require secp256k1.specification.
Import specification.Math.
Export specification.Math.scalar.

Open Scope Z_scope.

Local Obligation Tactic := intros.

(* ================================================================= *)
(** ** The group order's limbs -- [N_0 .. N_3] (mirror [SECP256K1_N_*]). *)

Definition N_0 : Z := 0xBFD25E8CD0364141.
Definition N_1 : Z := 0xBAAEDCE6AF48A03B.
Definition N_2 : Z := 0xFFFFFFFFFFFFFFFE.
Definition N_3 : Z := 0xFFFFFFFFFFFFFFFF.

(** [n] decomposes into its four 64-bit limbs. *)
Lemma secp256k1_N_limbs :
  secp256k1_N = N_0 + N_1 * 2^64 + N_2 * 2^128 + N_3 * 2^192.
Proof. unfold secp256k1_N, N_0, N_1, N_2, N_3. lia. Qed.

(** Limbs of [2^256 - n] (the "complement"), matching the C's [~N_i (+1)]. *)
Definition N_C_0 : Z := 0x402DA1732FC9BEBF.
Definition N_C_1 : Z := 0x4551231950B75FC4.
Definition N_C_2 : Z := 1.

(** [2^256 - n] decomposes into its three 64-bit limbs. *)
Lemma secp256k1_N_C_limbs :
  2^256 - secp256k1_N = N_C_0 + N_C_1 * 2^64 + N_C_2 * 2^128.
Proof. unfold secp256k1_N, N_C_0, N_C_1, N_C_2. lia. Qed.

(** Range facts for the limb constants. *)
Lemma N_0_range : 0 <= N_0 < 2^64. Proof. unfold N_0; lia. Qed.
Lemma N_1_range : 0 <= N_1 < 2^64. Proof. unfold N_1; lia. Qed.
Lemma N_2_range : 0 <= N_2 < 2^64. Proof. unfold N_2; lia. Qed.
Lemma N_3_range : 0 <= N_3 < 2^64. Proof. unfold N_3; lia. Qed.
Lemma N_C_0_range : 0 <= N_C_0 < 2^64. Proof. unfold N_C_0; lia. Qed.
Lemma N_C_1_range : 0 <= N_C_1 < 2^64. Proof. unfold N_C_1; lia. Qed.
Lemma N_C_2_range : 0 <= N_C_2 < 2^64. Proof. unfold N_C_2; lia. Qed.

(** The GLV window bound [2^128 < n], which is what makes
    [secp256k1_scalar_split_lambda]'s two outputs fit in 128 bits. *)
Lemma N_gt_2_128 : 2 ^ 128 < secp256k1_N.
Proof. unfold secp256k1_N; lia. Qed.

(* ================================================================= *)
(** ** Half the group order -- [secp256k1_N_H] = [floor(n/2)]. *)

(** Limbs of [floor(n/2)] (the [SECP256K1_N_H_*] macros), used by
    [secp256k1_scalar_is_high] and [secp256k1_scalar_half]. *)
Definition N_H_0 : Z := 0xDFE92F46681B20A0.
Definition N_H_1 : Z := 0x5D576E7357A4501D.
Definition N_H_2 : Z := 0xFFFFFFFFFFFFFFFF.
Definition N_H_3 : Z := 0x7FFFFFFFFFFFFFFF.

(** [floor(n/2)]: the threshold above which a scalar is "high", as the sum of
    its limbs ([secp256k1_N_as_2H] ties it back to [n]). *)
Definition secp256k1_N_H : Z :=
  N_H_0 + N_H_1 * 2^64 + N_H_2 * 2^128 + N_H_3 * 2^192.

(** [n] is odd, so [n = 2*floor(n/2) + 1].  The value-level statement of the
    same fact is [Math.residues]'s [secp256k1_N_odd]. *)
Lemma secp256k1_N_as_2H : secp256k1_N = 2 * secp256k1_N_H + 1.
Proof. unfold secp256k1_N, secp256k1_N_H, N_H_0, N_H_1, N_H_2, N_H_3. lia. Qed.

Lemma secp256k1_N_H_range : 0 <= secp256k1_N_H < secp256k1_N.
Proof. unfold secp256k1_N, secp256k1_N_H, N_H_0, N_H_1, N_H_2, N_H_3. lia. Qed.

(* ================================================================= *)
(** ** The split_lambda basis -- [minus_b1_z] / [minus_b2_z] / [g1_z] /
    [g2_z].

    The [secp256k1_scalar_split_lambda] tables (the C's [minus_b1],
    [minus_b2], [g1], [g2] file-scope constants) as raw 256-bit values.  What
    they MEAN -- that they solve the GLV lattice for [secp256k1_lambda] --
    is checked out of the tree; the endomorphism itself is
    [Math.group]'s [pmul_lambda]. *)

Definition minus_b1_z : Z :=
  0x00000000000000000000000000000000E4437ED6010E88286F547FA90ABFE4C3.
Definition minus_b2_z : Z :=
  0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFE8A280AC50774346DD765CDA83DB1562C.
Definition g1_z : Z :=
  0x3086D221A7D46BCDE86C90E49284EB153DAA8A1471E8CA7FE893209A45DBB031.
Definition g2_z : Z :=
  0xE4437ED6010E88286F547FA90ABFE4C4221208AC9DF506C61571B4AE8AC47F71.

(* ================================================================= *)
(** ** Machine-word views -- [scalar_to_u256] / [reduce_256] /
    [scalar_mul_shift]. *)

(** Widen a [Scalar] ([< n < 2^256]) to a [UInt256]: the value the C's four
    limbs hold, before any modular interpretation. *)
Program Definition scalar_to_u256 (s : Scalar) : UInt256 :=
  mkUInt256 (scalar_val s) _.
Next Obligation.
  destruct s as [v [H0 H1]].
  simpl.
  split.
  - lia.
  - unfold secp256k1_N in H1.
    lia.
Qed.

(** Reduce a 256-bit unsigned integer modulo the group order: the wrapping
    half of [secp256k1_scalar_set_b32]. *)
Program Definition reduce_256 (x : UInt256) : Scalar :=
  mkScalar (u256_val x mod secp256k1_N) _.
Next Obligation.
  split; apply Z.mod_pos_bound; unfold secp256k1_N; lia.
Qed.

(** [secp256k1_scalar_mul_shift_var]: round [a*b / 2^shift] to the nearest
    integer.  The C adds bit [shift-1] of the 512-bit product [a*b] as the
    round-half-up term. *)
Definition scalar_mul_shift (a b : Scalar) (shift : Z) : Z :=
  let p := scalar_val a * scalar_val b in
  p / 2 ^ shift + (p / 2 ^ (shift - 1)) mod 2.

(* ================================================================= *)
(** ** Automation registration.

    The [rep_lia] rewrite expands [secp256k1_N] to its decimal literal for
    representation proofs. Registering it here keeps that choice beside
    the limb encoding. Importing [specification] also loads its API
    dependencies, including VST. *)

(** The value bridge [rep_lia] rewrites with: [secp256k1_N] as a literal,
    COMPUTED from the definition at proof time rather than restated in the
    source, so the group order is spelled exactly once in the tree. *)
Lemma secp256k1_N_unfold :
  secp256k1_N = ltac:(let v := eval vm_compute in secp256k1_N in exact v).
Proof. reflexivity. Qed.
#[export] Hint Rewrite secp256k1_N_unfold : rep_lia.
