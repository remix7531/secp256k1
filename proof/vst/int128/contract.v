(** * vst.int128.contract: funspecs for the 128-bit arithmetic helpers. *)
(** Copyright (C) 2026 remix7531
    SPDX-License-Identifier: MIT *)

(** Mirrors the PUBLIC [src/int128.h] surface: the unsigned [secp256k1_u128_*]
    family first, then the signed [secp256k1_i128_*] family.  The three
    [static] building blocks declared only in [src/int128_struct_impl.h]
    ([secp256k1_umul128], [secp256k1_mul128], [secp256k1_i128_dissip_mul]) are
    specified in [vst/int128/impl.v]. *)

Require Import secp256k1.vst.base.
Require Import secp256k1.vst.helper.structs_int128.
Require Import secp256k1.theory.int128.int128.
Require Import secp256k1.vst.helper.notations.

(* ================================================================= *)
(** ** Unsigned 128-bit funspecs -- [secp256k1_u128_*]. *)

(** ([secp256k1_umul128] is internal -- see [vst/int128/impl.v].) *)

(** [secp256k1_u128_load]: set [*r] to [lo + hi * 2^64]. *)
Definition spec_secp256k1_u128_load : ident * funspec :=
  DECLARE _secp256k1_u128_load
  WITH r_ptr : val, hi : UInt64, lo : UInt64, sh : share
  PRE [ tptr t_secp256k1_u128, tulong, tulong ]
    PROP (writable_share sh)
    PARAMS (r_ptr; uint64_to_val hi; uint64_to_val lo)
    SEP (u128_at_ sh r_ptr)
  POST [ tvoid ]
    EX r : UInt128,
    PROP (u128_val r = Z.add (u64_val lo) (Z.mul (u64_val hi) (2^64)))
    RETURN ()
    SEP (u128_at sh r_ptr r).

(** [secp256k1_u128_mul]: store a*b into uint128 struct [*r]. *)
Definition spec_secp256k1_u128_mul : ident * funspec :=
  DECLARE _secp256k1_u128_mul
  WITH r_ptr : val, a : UInt64, b : UInt64, sh : share
  PRE [ tptr t_secp256k1_u128, tulong, tulong ]
    PROP (writable_share sh)
    PARAMS (r_ptr; uint64_to_val a; uint64_to_val b)
    SEP (u128_at_ sh r_ptr)
  POST [ tvoid ]
    EX r : UInt128,
    PROP (r = mul_64 a b)
    RETURN ()
    SEP (u128_at sh r_ptr r).

(** [secp256k1_u128_accum_mul]: add a*b to a 128-bit accumulator. *)
Definition spec_secp256k1_u128_accum_mul : ident * funspec :=
  DECLARE _secp256k1_u128_accum_mul
  WITH r_ptr : val, r : UInt128, a : UInt64, b : UInt64, sh : share
  PRE [ tptr t_secp256k1_u128, tulong, tulong ]
    PROP (writable_share sh;
          Z.add (u128_val r) (Z.mul (u64_val a) (u64_val b)) < 2^128)
    PARAMS (r_ptr; uint64_to_val a; uint64_to_val b)
    SEP (u128_at sh r_ptr r)
  POST [ tvoid ]
    EX r' : UInt128,
    PROP (u128_val r' = Z.add (u128_val r) (Z.mul (u64_val a) (u64_val b)))
    RETURN ()
    SEP (u128_at sh r_ptr r').

(** [secp256k1_u128_accum_u64]: add a 64-bit value to a 128-bit accumulator. *)
Definition spec_secp256k1_u128_accum_u64 : ident * funspec :=
  DECLARE _secp256k1_u128_accum_u64
  WITH r_ptr : val, r : UInt128, a : UInt64, sh : share
  PRE [ tptr t_secp256k1_u128, tulong ]
    PROP (writable_share sh;
          Z.add (u128_val r) (u64_val a) < 2^128)
    PARAMS (r_ptr; uint64_to_val a)
    SEP (u128_at sh r_ptr r)
  POST [ tvoid ]
    EX r' : UInt128,
    PROP (u128_val r' = Z.add (u128_val r) (u64_val a))
    RETURN ()
    SEP (u128_at sh r_ptr r').

(** [secp256k1_u128_rshift]: right-shift by 64 bits. *)
Definition spec_secp256k1_u128_rshift : ident * funspec :=
  DECLARE _secp256k1_u128_rshift
  WITH r_ptr : val, r : UInt128, n : Z, sh : share
  PRE [ tptr t_secp256k1_u128, tuint ]
    PROP (writable_share sh;
          n = 64)
    PARAMS (r_ptr; Vint (Int.repr n))
    SEP (u128_at sh r_ptr r)
  POST [ tvoid ]
    EX r' : UInt128,
    PROP (u128_val r' = Z.div (u128_val r) (2^64))
    RETURN ()
    SEP (u128_at sh r_ptr r').

(** [secp256k1_u128_to_u64]: return the low 64 bits. *)
Definition spec_secp256k1_u128_to_u64 : ident * funspec :=
  DECLARE _secp256k1_u128_to_u64
  WITH a_ptr : val, x : UInt128, sh : share
  PRE [ tptr t_secp256k1_u128 ]
    PROP (readable_share sh)
    PARAMS (a_ptr)
    SEP (u128_at sh a_ptr x)
  POST [ tulong ]
    EX r : UInt64,
    PROP (r = u128_lo x)
    RETURN (uint64_to_val r)
    SEP (u128_at sh a_ptr x).

(** [secp256k1_u128_hi_u64]: return the high 64 bits. *)
Definition spec_secp256k1_u128_hi_u64 : ident * funspec :=
  DECLARE _secp256k1_u128_hi_u64
  WITH a_ptr : val, x : UInt128, sh : share
  PRE [ tptr t_secp256k1_u128 ]
    PROP (readable_share sh)
    PARAMS (a_ptr)
    SEP (u128_at sh a_ptr x)
  POST [ tulong ]
    EX r : UInt64,
    PROP (r = u128_hi x)
    RETURN (uint64_to_val r)
    SEP (u128_at sh a_ptr x).

(** [secp256k1_u128_from_u64]: set r to a (zero-extended to 128 bits). *)
Definition spec_secp256k1_u128_from_u64 : ident * funspec :=
  DECLARE _secp256k1_u128_from_u64
  WITH r_ptr : val, a : UInt64, sh : share
  PRE [ tptr t_secp256k1_u128, tulong ]
    PROP (writable_share sh)
    PARAMS (r_ptr; uint64_to_val a)
    SEP (u128_at_ sh r_ptr)
  POST [ tvoid ]
    EX r : UInt128,
    PROP (u128_val r = u64_val a)
    RETURN ()
    SEP (u128_at sh r_ptr r).

(** [secp256k1_u128_check_bits]: return 1 if [*r < 2^n], 0 otherwise.
    [n] must be in [0, 128). *)
Definition spec_secp256k1_u128_check_bits : ident * funspec :=
  DECLARE _secp256k1_u128_check_bits
  WITH r_ptr : val, r : UInt128, n : Z, sh : share
  PRE [ tptr t_secp256k1_u128, tuint ]
    PROP (readable_share sh;
          (0 <= n)%Z;
          (n < 128)%Z)
    PARAMS (r_ptr; Vint (Int.repr n))
    SEP (u128_at sh r_ptr r)
  POST [ tint ]
    PROP ()
    RETURN (Vint (Int.repr (if Z_lt_dec (u128_val r) (2^n)%Z then 1 else 0)))
    SEP (u128_at sh r_ptr r).

(* ================================================================= *)
(** ** Signed 128-bit funspecs -- [secp256k1_i128_*]. *)

(** The signed [secp256k1_i128_*] helpers.  In the struct backend
    [secp256k1_int128] is a typedef of [secp256k1_uint128] (the same {lo, hi}
    layout), so the specs reuse [t_secp256k1_u128] as the struct type. The
    function idents come from the Clight AST: the extraction unit
    ([proof/extraction.c]) takes their addresses to force clightgen to retain
    them.  ([secp256k1_mul128] and [secp256k1_i128_dissip_mul], also from
    [int128_struct_impl.h], are internal -- see [vst/int128/impl.v].) *)

(** [secp256k1_i128_load]: set [*r] to [lo + hi * 2^64] (hi signed). *)
Definition spec_secp256k1_i128_load : ident * funspec :=
  DECLARE _secp256k1_i128_load
  WITH r_ptr : val, hi : Int64, lo : UInt64, sh : share
  PRE [ tptr t_secp256k1_u128, tlong, tulong ]
    PROP (writable_share sh)
    PARAMS (r_ptr; int64_to_val hi; uint64_to_val lo)
    SEP (i128_at_ sh r_ptr)
  POST [ tvoid ]
    EX r : Int128,
    PROP (i128_val r = Z.add (u64_val lo) (Z.mul (i64_val hi) (2^64)))
    RETURN ()
    SEP (i128_at sh r_ptr r).

(** [secp256k1_i128_mul]: set [*r = a * b]. *)
Definition spec_secp256k1_i128_mul : ident * funspec :=
  DECLARE _secp256k1_i128_mul
  WITH r_ptr : val, a : Int64, b : Int64, sh : share
  PRE [ tptr t_secp256k1_u128, tlong, tlong ]
    PROP (writable_share sh)
    PARAMS (r_ptr; int64_to_val a; int64_to_val b)
    SEP (i128_at_ sh r_ptr)
  POST [ tvoid ]
    PROP ()
    RETURN ()
    SEP (i128_at sh r_ptr (mul_i64 a b)).

(** [secp256k1_i128_accum_mul]: add [a * b] to [*r].
    Overflow or underflow from the addition is undefined behaviour. *)
Definition spec_secp256k1_i128_accum_mul : ident * funspec :=
  DECLARE _secp256k1_i128_accum_mul
  WITH r_ptr : val, r : Int128, a : Int64, b : Int64, sh : share
  PRE [ tptr t_secp256k1_u128, tlong, tlong ]
    PROP (writable_share sh;
          (-2^127 <= i128_val r + i64_val a * i64_val b)%Z;
          (i128_val r + i64_val a * i64_val b < 2^127)%Z)
    PARAMS (r_ptr; int64_to_val a; int64_to_val b)
    SEP (i128_at sh r_ptr r)
  POST [ tvoid ]
    EX r' : Int128,
    PROP (i128_val r' = (i128_val r + i64_val a * i64_val b)%Z)
    RETURN ()
    SEP (i128_at sh r_ptr r').

(** ([secp256k1_i128_dissip_mul] is internal -- see [vst/int128/impl.v].) *)

(** [secp256k1_i128_det]: set [*r = a*d - b*c]. *)
Definition spec_secp256k1_i128_det : ident * funspec :=
  DECLARE _secp256k1_i128_det
  WITH r_ptr : val, a : Int64, b : Int64, c : Int64, d : Int64, sh : share
  PRE [ tptr t_secp256k1_u128, tlong, tlong, tlong, tlong ]
    PROP (writable_share sh)
    PARAMS (r_ptr; int64_to_val a; int64_to_val b;
            int64_to_val c; int64_to_val d)
    SEP (i128_at_ sh r_ptr)
  POST [ tvoid ]
    PROP ()
    RETURN ()
    SEP (i128_at sh r_ptr (i128_det a b c d)).

(** [secp256k1_i128_rshift]: arithmetic right shift.
    [n] must be in [0, 128); the result is [floor(val / 2^n)]. *)
Definition spec_secp256k1_i128_rshift : ident * funspec :=
  DECLARE _secp256k1_i128_rshift
  WITH r_ptr : val, r : Int128, n : Z, sh : share
  PRE [ tptr t_secp256k1_u128, tuint ]
    PROP (writable_share sh;
          (0 <= n)%Z;
          (n < 128)%Z)
    PARAMS (r_ptr; Vint (Int.repr n))
    SEP (i128_at sh r_ptr r)
  POST [ tvoid ]
    EX r' : Int128,
    PROP (i128_val r' = (i128_val r / 2^n)%Z)
    RETURN ()
    SEP (i128_at sh r_ptr r').

(** [secp256k1_i128_to_u64]: return [val mod 2^64] as an unsigned 64-bit value. *)
Definition spec_secp256k1_i128_to_u64 : ident * funspec :=
  DECLARE _secp256k1_i128_to_u64
  WITH a_ptr : val, a : Int128, sh : share
  PRE [ tptr t_secp256k1_u128 ]
    PROP (readable_share sh)
    PARAMS (a_ptr)
    SEP (i128_at sh a_ptr a)
  POST [ tulong ]
    EX r : UInt64,
    PROP (u64_val r = (i128_val a mod 2^64)%Z)
    RETURN (uint64_to_val r)
    SEP (i128_at sh a_ptr a).

(** [secp256k1_i128_to_i64]: return value as a signed 64-bit integer.
    Requires the stored value to fit in [Int64] range. *)
Definition spec_secp256k1_i128_to_i64 : ident * funspec :=
  DECLARE _secp256k1_i128_to_i64
  WITH a_ptr : val, a : Int128, sh : share
  PRE [ tptr t_secp256k1_u128 ]
    PROP (readable_share sh;
          (-2^63 <= i128_val a)%Z;
          (i128_val a < 2^63)%Z)
    PARAMS (a_ptr)
    SEP (i128_at sh a_ptr a)
  POST [ tlong ]
    EX r : Int64,
    PROP (i64_val r = i128_val a)
    RETURN (int64_to_val r)
    SEP (i128_at sh a_ptr a).

(** [secp256k1_i128_from_i64]: sign-extend [a] to [*r]. *)
Definition spec_secp256k1_i128_from_i64 : ident * funspec :=
  DECLARE _secp256k1_i128_from_i64
  WITH r_ptr : val, a : Int64, sh : share
  PRE [ tptr t_secp256k1_u128, tlong ]
    PROP (writable_share sh)
    PARAMS (r_ptr; int64_to_val a)
    SEP (i128_at_ sh r_ptr)
  POST [ tvoid ]
    EX r : Int128,
    PROP (i128_val r = i64_val a)
    RETURN ()
    SEP (i128_at sh r_ptr r).

(** [secp256k1_i128_eq_var]: return 1 if [*a = *b], 0 otherwise. *)
Definition spec_secp256k1_i128_eq_var : ident * funspec :=
  DECLARE _secp256k1_i128_eq_var
  WITH a_ptr : val, b_ptr : val, a : Int128, b : Int128,
       sh_a : share, sh_b : share
  PRE [ tptr t_secp256k1_u128, tptr t_secp256k1_u128 ]
    PROP (readable_share sh_a;
          readable_share sh_b)
    PARAMS (a_ptr; b_ptr)
    SEP (i128_at sh_a a_ptr a;
         i128_at sh_b b_ptr b)
  POST [ tint ]
    PROP ()
    RETURN (Vint (Int.repr (if Z.eq_dec (i128_val a) (i128_val b) then 1 else 0)))
    SEP (i128_at sh_a a_ptr a;
         i128_at sh_b b_ptr b).

(** [secp256k1_i128_check_pow2]: return 1 if [val = sign * 2^n], 0 otherwise.
    Requires [n < 127] and [sign = 1 or sign = -1]. *)
Definition spec_secp256k1_i128_check_pow2 : ident * funspec :=
  DECLARE _secp256k1_i128_check_pow2
  WITH r_ptr : val, r : Int128, n : Z, sign : Z, sh : share
  PRE [ tptr t_secp256k1_u128, tuint, tint ]
    PROP (readable_share sh;
          (0 <= n)%Z;
          (n < 127)%Z;
          sign = 1 \/ sign = -1)
    PARAMS (r_ptr; Vint (Int.repr n); Vint (Int.repr sign))
    SEP (i128_at sh r_ptr r)
  POST [ tint ]
    PROP ()
    RETURN (Vint (Int.repr (if Z.eq_dec (i128_val r) (sign * 2^n)%Z then 1 else 0)))
    SEP (i128_at sh r_ptr r).

(* ================================================================= *)
(** ** The module's funspec list -- [src/int128.h]'s public family.

    Every module's public specs are listed here, at the bottom of the file
    that declares them, and [vst/gprog.v] concatenates the module lists into
    the one global table.  Adding a public function to this module is
    therefore one edit to one file: the funspec above, its name below. *)

Definition Gprog_int128_public : funspecs := [
  spec_secp256k1_u128_load;
  spec_secp256k1_u128_mul;
  spec_secp256k1_u128_accum_mul;
  spec_secp256k1_u128_accum_u64;
  spec_secp256k1_u128_rshift;
  spec_secp256k1_u128_to_u64;
  spec_secp256k1_u128_hi_u64;
  spec_secp256k1_u128_from_u64;
  spec_secp256k1_u128_check_bits;
  spec_secp256k1_i128_load;
  spec_secp256k1_i128_mul;
  spec_secp256k1_i128_accum_mul;
  spec_secp256k1_i128_det;
  spec_secp256k1_i128_rshift;
  spec_secp256k1_i128_to_u64;
  spec_secp256k1_i128_to_i64;
  spec_secp256k1_i128_from_i64;
  spec_secp256k1_i128_eq_var;
  spec_secp256k1_i128_check_pow2
].
