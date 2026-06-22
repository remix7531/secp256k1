(** * contract.impl.scalar: INTERNAL funspecs for the scalar subsystem. *)
(** Copyright (C) 2026 remix7531
    SPDX-License-Identifier: MIT *)

(** Mirrors [src/scalar_4x64_impl.h]: the funspecs here are for the [static]
    helpers that are NOT part of the public [src/scalar.h] surface -- the
    accumulator primitives ([muladd] / [sumadd] / [extract], with their [_fast]
    variants), the overflow-check + reduction pipeline ([check_overflow],
    [reduce], [mul_512], [reduce_512]), the rounded-shift limb helper
    ([shift_limb]), and the scalar <-> signed62 bridge ([to_signed62] /
    [from_signed62]).  The public scalar API (including [secp256k1_scalar_mul],
    [inverse], [inverse_var]) is specified in [contract/scalar.v]; the proving
    [Gprog]s composing public + internal live in [contract/gprog/scalar.v] (and, for
    the inverse-bridge call graph, [contract/modinv.v]). *)

Require Import secp256k1.vst.base.
Require Import secp256k1.contract.helper.structs_scalar.
Require Import secp256k1.contract.helper.structs_modinv.
Require Import secp256k1.theory.arithmetic.
Require Import secp256k1.theory.bytes.
Require Import secp256k1.model.int128.
Require Import secp256k1.model.acc.
Require Import secp256k1.model.scalar.
Require Import secp256k1.contract.helper.signed62.
Require Import secp256k1.contract.helper.notations.

(* ================================================================= *)
(** ** Accumulator funspecs -- [muladd] / [sumadd] / [extract] (+ _fast variants). *)

(** [muladd]: add a*b to acc. c2 must never overflow. *)
Definition spec_secp256k1_scalar_muladd : ident * funspec :=
  DECLARE _secp256k1_scalar_muladd
  WITH acc_ptr : val, acc : Acc, a : UInt64, b : UInt64, sh : share
  PRE [ tptr t_secp256k1_acc, tulong, tulong ]
    PROP (writable_share sh;
          acc_val acc + Z.mul (u64_val a) (u64_val b) < 2^192)
    PARAMS (acc_ptr; uint64_to_val a; uint64_to_val b)
    SEP (acc_at sh acc_ptr acc)
  POST [ tvoid ]
    EX acc' : Acc,
    PROP (acc_val acc' = Z.add (acc_val acc) (Z.mul (u64_val a) (u64_val b)))
    RETURN ()
    SEP (acc_at sh acc_ptr acc').

(** [muladd_fast]: add a*b to (c0,c1). c1 must never overflow. *)
Definition spec_secp256k1_scalar_muladd_fast : ident * funspec :=
  DECLARE _secp256k1_scalar_muladd_fast
  WITH acc_ptr : val, acc : Acc, a : UInt64, b : UInt64, sh : share
  PRE [ tptr t_secp256k1_acc, tulong, tulong ]
    PROP (writable_share sh;
          acc_val acc + Z.mul (u64_val a) (u64_val b) < 2^128)
    PARAMS (acc_ptr; uint64_to_val a; uint64_to_val b)
    SEP (acc_at sh acc_ptr acc)
  POST [ tvoid ]
    EX acc' : Acc,
    PROP (acc_val acc' = Z.add (acc_val acc) (Z.mul (u64_val a) (u64_val b)))
    RETURN ()
    SEP (acc_at sh acc_ptr acc').

(** [sumadd]: add a to acc. c2 must never overflow. *)
Definition spec_secp256k1_scalar_sumadd : ident * funspec :=
  DECLARE _secp256k1_scalar_sumadd
  WITH acc_ptr : val, acc : Acc, a : UInt64, sh : share
  PRE [ tptr t_secp256k1_acc, tulong ]
    PROP (writable_share sh;
          Z.add (acc_val acc) (u64_val a) < 2^192)
    PARAMS (acc_ptr; uint64_to_val a)
    SEP (acc_at sh acc_ptr acc)
  POST [ tvoid ]
    EX acc' : Acc,
    PROP (acc_val acc' = Z.add (acc_val acc) (u64_val a))
    RETURN ()
    SEP (acc_at sh acc_ptr acc').

(** [sumadd_fast]: add a to (c0,c1). c1 must never overflow, c2 must be zero. *)
Definition spec_secp256k1_scalar_sumadd_fast : ident * funspec :=
  DECLARE _secp256k1_scalar_sumadd_fast
  WITH acc_ptr : val, acc : Acc, a : UInt64, sh : share
  PRE [ tptr t_secp256k1_acc, tulong ]
    PROP (writable_share sh;
          Z.add (acc_val acc) (u64_val a) < 2^128)
    PARAMS (acc_ptr; uint64_to_val a)
    SEP (acc_at sh acc_ptr acc)
  POST [ tvoid ]
    EX acc' : Acc,
    PROP (acc_val acc' = Z.add (acc_val acc) (u64_val a))
    RETURN ()
    SEP (acc_at sh acc_ptr acc').

(** [extract]: extract lowest 64 bits, shift acc right by 64. *)
Definition spec_secp256k1_scalar_extract : ident * funspec :=
  DECLARE _secp256k1_scalar_extract
  WITH acc_ptr : val, acc : Acc, n_ptr : val, sh : share, sh_n : share
  PRE [ tptr t_secp256k1_acc, tptr tulong ]
    PROP (writable_share sh;
          writable_share sh_n)
    PARAMS (acc_ptr; n_ptr)
    SEP (acc_at sh acc_ptr acc;
         u64_at_ sh_n n_ptr)
  POST [ tvoid ]
    EX n : UInt64, EX acc' : Acc,
    PROP (n = acc_lo acc;
          acc_val acc' = acc_val acc / 2^64)
    RETURN ()
    SEP (acc_at sh acc_ptr acc';
         u64_at sh_n n_ptr n).

(** [extract_fast]: extract lowest 64 bits, c2 required zero. *)
Definition spec_secp256k1_scalar_extract_fast : ident * funspec :=
  DECLARE _secp256k1_scalar_extract_fast
  WITH acc_ptr : val, acc : Acc, n_ptr : val, sh : share, sh_n : share
  PRE [ tptr t_secp256k1_acc, tptr tulong ]
    PROP (writable_share sh;
          writable_share sh_n;
          acc_val acc < 2^128)
    PARAMS (acc_ptr; n_ptr)
    SEP (acc_at sh acc_ptr acc;
         u64_at_ sh_n n_ptr)
  POST [ tvoid ]
    EX n : UInt64, EX acc' : Acc,
    PROP (n = acc_lo acc;
          acc_val acc' = acc_val acc / 2^64)
    RETURN ()
    SEP (acc_at sh acc_ptr acc';
         u64_at sh_n n_ptr n).

(* ================================================================= *)
(** ** Overflow check and reduction -- [check_overflow] [a >= N] / [reduce] [+ ovf*(2^256-N)]. *)

(** [secp256k1_scalar_check_overflow]: return 1 if a >= N, 0 otherwise. *)
Definition spec_secp256k1_scalar_check_overflow : ident * funspec :=
  DECLARE _secp256k1_scalar_check_overflow
  WITH a_ptr : val, a : UInt256, sh : share
  PRE [ tptr t_secp256k1_uint256 ]
    PROP (readable_share sh)
    PARAMS (a_ptr)
    SEP (u256_at sh a_ptr a)
  POST [ tint ]
    PROP ()
    RETURN (Vint (Int.repr (if Z_lt_dec (u256_val a) secp256k1_N then 0 else 1)))
    SEP (u256_at sh a_ptr a).

(** [secp256k1_scalar_reduce]: add [overflow * (2^256 - N)] to [r].
    Returns [overflow] unchanged.

    The C code simply ripple-adds [overflow * N_C_i] across the four
    limbs, discarding the final carry; the result is
    [(r + overflow * (2^256 - N)) mod 2^256]. *)
Definition spec_secp256k1_scalar_reduce : ident * funspec :=
  DECLARE _secp256k1_scalar_reduce
  WITH r_ptr : val, r : UInt256, overflow : Z, sh : share
  PRE [ tptr t_secp256k1_uint256, tuint ]
    PROP (writable_share sh;
          0 <= overflow <= 2)
    PARAMS (r_ptr; Vint (Int.repr overflow))
    SEP (u256_at sh r_ptr r)
  POST [ tint ]
    EX r' : UInt256,
    PROP (u256_val r' = (Z.add (u256_val r) (Z.mul overflow (Z.sub (2^256) secp256k1_N))) mod 2^256)
    RETURN (Vint (Int.repr overflow))
    SEP (u256_at sh r_ptr r').

(* ================================================================= *)
(** ** secp256k1_scalar_mul_512 -- [l8 = mul_256 a b] (512-bit product). *)

(** Specification for [secp256k1_scalar_mul_512] (internal).

    Postcondition: the 8-limb array at [l8_ptr], interpreted as a
    [UInt512], equals [mul_256 a b]. *)
Definition spec_secp256k1_scalar_mul_512 : ident * funspec :=
  DECLARE _secp256k1_scalar_mul_512
  WITH l8_ptr : val, a_ptr : val, b_ptr : val,
       a : UInt256, b : UInt256,
       sh_l : share, sh_a : share, sh_b : share
  PRE [ tptr tulong, tptr t_secp256k1_uint256, tptr t_secp256k1_uint256 ]
    PROP (writable_share sh_l;
          readable_share sh_a;
          readable_share sh_b)
    PARAMS (l8_ptr; a_ptr; b_ptr)
    SEP (u512_at_ sh_l l8_ptr;
         u256_at sh_a a_ptr a;
         u256_at sh_b b_ptr b)
  POST [ tvoid ]
    EX r : UInt512,
    PROP (r = mul_256 a b)
    RETURN ()
    SEP (u512_at sh_l l8_ptr r;
         u256_at sh_a a_ptr a;
         u256_at sh_b b_ptr b).

(* ================================================================= *)
(** ** secp256k1_scalar_reduce_512 -- [r = l mod N]. *)

(** Specification for [secp256k1_scalar_reduce_512] (internal).

    Postcondition: the scalar at [r_ptr] equals [l mod N]. *)
Definition spec_secp256k1_scalar_reduce_512 : ident * funspec :=
  DECLARE _secp256k1_scalar_reduce_512
  WITH r_ptr : val, l_ptr : val,
       l : UInt512,
       sh_r : share, sh_l : share
  PRE [ tptr t_secp256k1_uint256, tptr tulong ]
    PROP (writable_share sh_r;
          readable_share sh_l)
    PARAMS (r_ptr; l_ptr)
    SEP (u256_at_ sh_r r_ptr;
         u512_at sh_l l_ptr l)
  POST [ tvoid ]
    EX r : Scalar,
    PROP (scalar_val r = Z.modulo (u512_val l) secp256k1_N)
    RETURN ()
    SEP (scalar_at sh_r r_ptr r;
         u512_at sh_l l_ptr l).

(* ================================================================= *)
(** ** Rounded multiply-shift helper -- [shift_limb]. *)

(** [shift_limb]: extract limb [j] of the 512-bit value [l] shifted right by
    [shift] bits.  Internal helper for [mul_shift_var]; [shiftlimbs]/[shiftlow]/
    [shifthigh] are the precomputed [shift/64], [shift mod 64], [64-shiftlow],
    and [lo]/[hi] are the per-limb cutoffs [512-64*j] / [448-64*j].  Returns
    limb [j] of [l / 2^shift]. *)
Definition spec_secp256k1_scalar_shift_limb : ident * funspec :=
  DECLARE _secp256k1_scalar_shift_limb
  WITH l_ptr : val, l : UInt512, shift : Z, j : Z, sh : share
  PRE [ tptr tulong, tuint, tuint, tuint, tuint, tuint, tuint, tuint ]
    PROP (readable_share sh;
          (256 <= shift)%Z;
          (shift < 512)%Z;
          (0 <= j)%Z;
          (j <= 3)%Z)
    PARAMS (l_ptr;
            Vint (Int.repr shift);
            Vint (Int.repr (shift / 64)%Z);
            Vint (Int.repr (shift mod 64)%Z);
            Vint (Int.repr (64 - shift mod 64)%Z);
            Vint (Int.repr j);
            Vint (Int.repr (512 - 64 * j)%Z);
            Vint (Int.repr (448 - 64 * j)%Z))
    SEP (u512_at sh l_ptr l)
  POST [ tulong ]
    PROP ()
    RETURN (Vlong (Int64.repr (limb (2 ^ 64) (u512_val l / 2 ^ shift) (Z.to_nat j))))
    SEP (u512_at sh l_ptr l).

(* ================================================================= *)
(** ** Scalar <-> signed62 bridge -- [to_signed62] / [from_signed62]. *)

(** These reference the [Signed62] representation ([contract/helper/signed62.v]); they
    are internal helpers for the modular inverse path. *)

(** [secp256k1_scalar_to_signed62]: repack the 4-limb scalar [*a] into the
    5-limb signed62 form [*r] (little-endian 62-bit limbs).  The value is
    unchanged, so [r] is the canonical [reprn 5 (scalar_val a)]. *)
Definition spec_secp256k1_scalar_to_signed62 : ident * funspec :=
  DECLARE _secp256k1_scalar_to_signed62
  WITH r_ptr : val, a_ptr : val, a : Scalar, sh_r : share, sh_a : share
  PRE [ tptr t_secp256k1_modinv64_signed62, tptr t_secp256k1_scalar ]
    PROP (writable_share sh_r;
          readable_share sh_a)
    PARAMS (r_ptr; a_ptr)
    SEP (data_at_ sh_r t_secp256k1_modinv64_signed62 r_ptr;
         scalar_at sh_a a_ptr a)
  POST [ tvoid ]
    PROP ()
    RETURN ()
    SEP (signed62_at sh_r r_ptr (scalar_val a);
         scalar_at sh_a a_ptr a).

(** [secp256k1_scalar_from_signed62]: repack a normalized 5-limb signed62
    number [*a] (value [x] in [[0, N)]) back into the 4-limb scalar [*r].
    The result scalar holds exactly [x]. *)
Definition spec_secp256k1_scalar_from_signed62 : ident * funspec :=
  DECLARE _secp256k1_scalar_from_signed62
  WITH r_ptr : val, a_ptr : val, x : Z, sh_r : share, sh_a : share
  PRE [ tptr t_secp256k1_scalar, tptr t_secp256k1_modinv64_signed62 ]
    PROP (writable_share sh_r;
          readable_share sh_a;
          (0 <= x < secp256k1_N)%Z)
    PARAMS (r_ptr; a_ptr)
    SEP (data_at_ sh_r t_secp256k1_scalar r_ptr;
         signed62_at sh_a a_ptr x)
  POST [ tvoid ]
    EX r : Scalar,
    PROP ((scalar_val r = x)%Z)
    RETURN ()
    SEP (scalar_at sh_r r_ptr r;
         signed62_at sh_a a_ptr x).
