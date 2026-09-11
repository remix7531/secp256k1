(** * theory.integers.machine: the C's fixed-width machine integers, as records. *)
(** Copyright (C) 2026 remix7531
    SPDX-License-Identifier: MIT *)

(** Representation, not mathematics.  Each record below is a [Z] paired with
    the range invariant of one C integer width, and exists so that a funspec
    can say "this parameter is a [uint64_t]" without repeating the bound at
    every use.  Nothing here is part of what the library computes: the
    mathematical objects live in the story files at the proof root
    ([theory/field.v], [theory/scalar.v], [theory/group.v], [theory/sha256.v], [theory/schnorr.v]), and this file
    is what the story deliberately hides.

    The operations are in [theory/int128/int128.v] (the 128-bit helper family) and
    [theory/int128/acc.v] (the 192-bit accumulator); the C-representation bridges
    that turn one of these into a struct or a limb array are in
    [vst/helper/repr.v]. *)

Require Import ZArith.

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
