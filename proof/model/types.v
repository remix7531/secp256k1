(** * model.types: the value record types (machine words + curve residues). *)
(** Copyright (C) 2026 remix7531
    SPDX-License-Identifier: MIT *)

(** Every value type of the model gathered in one place: the fixed-width machine
    words ([UInt64] .. [UInt512], [Int64], [Int128]) and the two curve residues
    ([Fe] mod p, [Scalar] mod n).  Each is a [Z] paired with its range invariant.
    The operations on them live in [model.field] / [model.int128] / [model.scalar]
    (and the 192-bit accumulator [Acc] in [model.acc]). *)

Require Import ZArith.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Logic.Eqdep_dec.
Require Export secp256k1.model.constants.

Open Scope Z_scope.

(* ================================================================= *)
(** ** Unsigned machine words -- [UInt64] / [UInt128] / [UInt256] / [UInt512]. *)

(** A 64-bit unsigned integer. *)
Record UInt64 := mkUInt64 {
  u64_val : Z;
  u64_range : 0 <= u64_val < 2^64
}.

(** A 128-bit unsigned integer. *)
Record UInt128 := mkUInt128 {
  u128_val : Z;
  u128_range : 0 <= u128_val < 2^128
}.

(** A 256-bit unsigned integer. *)
Record UInt256 := mkUInt256 {
  u256_val : Z;
  u256_range : 0 <= u256_val < 2^256
}.

(** A 512-bit unsigned integer. *)
Record UInt512 := mkUInt512 {
  u512_val : Z;
  u512_range : 0 <= u512_val < 2^512
}.

(* ================================================================= *)
(** ** Signed machine words -- [Int64] / [Int128]. *)

(** A signed 64-bit integer. *)
Record Int64 := mkInt64 {
  i64_val : Z;
  i64_range : -2^63 <= i64_val < 2^63
}.

(** A signed 128-bit integer. *)
Record Int128 := mkInt128 {
  i128_val : Z;
  i128_range : -2^127 <= i128_val < 2^127
}.

(* ================================================================= *)
(** ** Curve residues -- [Fe] (mod p) / [Scalar] (mod n). *)

(** A field element modulo p. *)
Record Fe := mkFe {
  fe_val : Z;
  fe_range : 0 <= fe_val < secp256k1_P
}.
Coercion fe_val : Fe >-> Z.

(** A scalar modulo the group order n. *)
Record Scalar := mkScalar {
  scalar_val : Z;
  scalar_range : 0 <= scalar_val < secp256k1_N
}.
Coercion scalar_val : Scalar >-> Z.

(* ================================================================= *)
(** ** Range-proof irrelevance -- [Z_range_irrel] (axiom-free).

    Any two proofs of the same [lo <= v < hi] are equal.  Derived without
    assuming proof irrelevance: a [Z.lt] proof is an equality in the decidable
    type [comparison], unique by [UIP_dec]; a [Z.le] proof is a function into
    [False], unique by functional extensionality (an axiom the toolchain
    already assumes -- see [audit/AXIOM_WHITELIST]). *)

Local Lemma Z_lt_irrel (x y : Z) (p q : x < y) : p = q.
Proof.
  unfold Z.lt in p, q.
  apply Eqdep_dec.UIP_dec.
  decide equality.
Qed.

Local Lemma Z_le_irrel (x y : Z) (p q : x <= y) : p = q.
Proof.
  unfold Z.le in p, q.
  apply functional_extensionality.
  intros h.
  destruct (p h).
Qed.

Lemma Z_range_irrel (lo v hi : Z) (p q : lo <= v < hi) : p = q.
Proof.
  destruct p as [p1 p2], q as [q1 q2].
  f_equal.
  - apply Z_le_irrel.
  - apply Z_lt_irrel.
Qed.

(* ================================================================= *)
(** ** Extensionality -- a residue is determined by its value (the range proof
    is irrelevant), so [mk]-equality goals close in one step. *)

Lemma fe_eq_ext (a b : Fe) : fe_val a = fe_val b -> a = b.
Proof.
  destruct a as [va Ha], b as [vb Hb]; simpl; intros ->.
  f_equal; apply Z_range_irrel.
Qed.

Lemma scalar_eq_ext (a b : Scalar) : scalar_val a = scalar_val b -> a = b.
Proof.
  destruct a as [va Ha], b as [vb Hb]; simpl; intros ->.
  f_equal; apply Z_range_irrel.
Qed.
