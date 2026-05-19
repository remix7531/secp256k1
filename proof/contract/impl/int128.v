(** * contract.impl.int128: INTERNAL funspecs for the 128-bit helpers. *)
(** Copyright (C) 2026 remix7531
    SPDX-License-Identifier: MIT *)

(** Mirrors [src/int128_struct_impl.h]: the funspecs here are for the [static]
    building blocks that are NOT part of the public [int128.h] surface --
    [secp256k1_umul128] (unsigned 64x64->128 multiply), [secp256k1_mul128]
    (signed 64x64->128 multiply), and [secp256k1_i128_dissip_mul] (fused
    multiply-subtract).  The public [u128_*] / [i128_*] families are specified
    in [contract/int128.v]; the proving [Gprog] composing both lives in
    [contract/gprog/int128.v]. *)

Require Import secp256k1.vst.base.
Require Import secp256k1.contract.helper.structs_int128.
Require Import secp256k1.model.int128.
Require Import secp256k1.contract.helper.notations.

(* ================================================================= *)
(** ** Internal 64x64->128 multiplies + fused multiply-subtract. *)

(** [secp256k1_umul128]: compute a*b, return lo, write hi to [*hi]. *)
Definition spec_secp256k1_umul128 : ident * funspec :=
  DECLARE _secp256k1_umul128
  WITH a : UInt64, b : UInt64, hi_ptr : val, sh : share
  PRE [ tulong, tulong, tptr tulong ]
    PROP (writable_share sh)
    PARAMS (uint64_to_val a; uint64_to_val b; hi_ptr)
    SEP (u64_at_ sh hi_ptr)
  POST [ tulong ]
    EX result : UInt128,
    PROP (result = mul_64 a b)
    RETURN (uint64_to_val (u128_lo result))
    SEP (u64_at sh hi_ptr (u128_hi result)).

(** [secp256k1_mul128]: multiply two signed 64-bit integers, returning
    the low 64 bits as [int64] and writing the high 64 bits to [*hi]. *)
Definition spec_secp256k1_mul128 : ident * funspec :=
  DECLARE _secp256k1_mul128
  WITH a : Int64, b : Int64, hi_ptr : val, sh : share
  PRE [ tlong, tlong, tptr tlong ]
    PROP (writable_share sh)
    PARAMS (int64_to_val a; int64_to_val b; hi_ptr)
    SEP (i64_at_ sh hi_ptr)
  POST [ tlong ]
    PROP ()
    RETURN (Vlong (Int64.repr (i64_val a * i64_val b)))
    SEP (i64_at sh hi_ptr (i128_hi (mul_i64 a b))).

(** [secp256k1_i128_dissip_mul]: subtract [a * b] from [*r].
    Overflow or underflow from the subtraction is undefined behaviour. *)
Definition spec_secp256k1_i128_dissip_mul : ident * funspec :=
  DECLARE _secp256k1_i128_dissip_mul
  WITH r_ptr : val, r : Int128, a : Int64, b : Int64, sh : share
  PRE [ tptr t_secp256k1_u128, tlong, tlong ]
    PROP (writable_share sh;
          (-2^127 <= i128_val r - i64_val a * i64_val b)%Z;
          (i128_val r - i64_val a * i64_val b < 2^127)%Z)
    PARAMS (r_ptr; int64_to_val a; int64_to_val b)
    SEP (i128_at sh r_ptr r)
  POST [ tvoid ]
    EX r' : Int128,
    PROP (i128_val r' = (i128_val r - i64_val a * i64_val b)%Z)
    RETURN ()
    SEP (i128_at sh r_ptr r').
