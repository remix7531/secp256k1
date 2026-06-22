(** * contract.scalar: funspecs for the PUBLIC scalar API ([src/scalar.h]). *)
(** Copyright (C) 2026 remix7531
    SPDX-License-Identifier: MIT *)

(** Mirrors the public [src/scalar.h] surface: [secp256k1_scalar_mul] and the
    rest of the exported API, including the modular inverse entry points
    [secp256k1_scalar_inverse] / [_var].  The [static] helpers declared only in
    [src/scalar_4x64_impl.h] (the accumulator primitives, the reduction
    pipeline, [shift_limb], and the scalar <-> signed62 bridge) are specified in
    [contract/impl/scalar.v]. *)

Require Import secp256k1.vst.base.
Require Import secp256k1.contract.helper.structs_scalar.
Require Import secp256k1.contract.helper.structs_modinv.
Require Import secp256k1.theory.arithmetic.
Require Import secp256k1.theory.bytes.
Require Import Coq.ZArith.Znumtheory.
Require Import secp256k1.model.int128.
Require Import secp256k1.model.scalar.
Require Import secp256k1.model.modinv.
Require Import secp256k1.contract.helper.signed62.
Require Import secp256k1.contract.util.
Require Import secp256k1.contract.helper.notations.

(* ================================================================= *)
(** ** secp256k1_scalar_mul -- public [(a*b) mod N]. *)

(** ([secp256k1_scalar_reduce_512] is internal -- see [contract/impl/scalar.v].) *)

(** The public specification for [secp256k1_scalar_mul].

    Postcondition: the scalar at [r_ptr] equals [scalar_mul a b],
    i.e. [a * b mod N]. *)
(** The [alias] flag covers the in-place call [mul(r, r, b)] (used by
    [split_lambda]): when [alias = true] the result and first-argument pointers
    coincide and a single writable chunk backs both, so the disjoint
    two-chunk precondition would be unsatisfiable.  When [alias = false] this is
    the ordinary non-aliasing spec. *)
Definition spec_secp256k1_scalar_mul : ident * funspec :=
  DECLARE _secp256k1_scalar_mul
  WITH r_ptr : val, a_ptr : val, b_ptr : val,
       a : Scalar, b : Scalar,
       sh_r : share, sh_a : share, sh_b : share, alias : bool
  PRE [ tptr t_secp256k1_scalar, tptr t_secp256k1_scalar, tptr t_secp256k1_scalar ]
    PROP (writable_share sh_r;
          readable_share sh_b;
          alias = true -> a_ptr = r_ptr;
          alias = false -> readable_share sh_a)
    PARAMS (r_ptr; a_ptr; b_ptr)
    SEP (if alias
         then (scalar_at sh_r r_ptr a * scalar_at sh_b b_ptr b)
         else (data_at_ sh_r t_secp256k1_scalar r_ptr *
               scalar_at sh_a a_ptr a * scalar_at sh_b b_ptr b))
  POST [ tvoid ]
    EX r : Scalar,
    PROP (r = scalar_mul a b)
    RETURN ()
    SEP (if alias
         then (scalar_at sh_r r_ptr r * scalar_at sh_b b_ptr b)
         else (scalar_at sh_r r_ptr r *
               scalar_at sh_a a_ptr a * scalar_at sh_b b_ptr b)).

(* ================================================================= *)
(** ** Init, move, verify -- [set_int] / [clear] / [cmov] / [verify]. *)

(** [set_int]: set [*r] to the small unsigned integer [v]. *)
Definition spec_secp256k1_scalar_set_int : ident * funspec :=
  DECLARE _secp256k1_scalar_set_int
  WITH r_ptr : val, v : Z, sh : share
  PRE [ tptr t_secp256k1_scalar, tuint ]
    PROP (writable_share sh;
          (0 <= v < 2 ^ 32)%Z)
    PARAMS (r_ptr; Vint (Int.repr v))
    SEP (data_at_ sh t_secp256k1_scalar r_ptr)
  POST [ tvoid ]
    EX r : Scalar,
    PROP ((scalar_val r = v)%Z)
    RETURN ()
    SEP (scalar_at sh r_ptr r).

(** [clear]: zero [*r] (via [memclear_explicit]). *)
Definition spec_secp256k1_scalar_clear : ident * funspec :=
  DECLARE _secp256k1_scalar_clear
  WITH r_ptr : val, sh : share
  PRE [ tptr t_secp256k1_scalar ]
    PROP (writable_share sh)
    PARAMS (r_ptr)
    SEP (data_at_ sh t_secp256k1_scalar r_ptr)
  POST [ tvoid ]
    EX r : Scalar,
    PROP ((scalar_val r = 0)%Z)
    RETURN ()
    SEP (scalar_at sh r_ptr r).

(** [cmov]: constant-time conditional move -- [*r := flag ? *a : *r]. *)
Definition spec_secp256k1_scalar_cmov : ident * funspec :=
  DECLARE _secp256k1_scalar_cmov
  WITH r_ptr : val, a_ptr : val, r0 : Scalar, a : Scalar, flag : Z,
       sh_r : share, sh_a : share
  PRE [ tptr t_secp256k1_scalar, tptr t_secp256k1_scalar, tint ]
    PROP (writable_share sh_r;
          readable_share sh_a;
          flag = 0 \/ flag = 1)
    PARAMS (r_ptr; a_ptr; Vint (Int.repr flag))
    SEP (scalar_at sh_r r_ptr r0;
         scalar_at sh_a a_ptr a)
  POST [ tvoid ]
    EX r : Scalar,
    PROP (r = if Z.eq_dec flag 1 then a else r0)
    RETURN ()
    SEP (scalar_at sh_r r_ptr r;
         scalar_at sh_a a_ptr a).

(** [verify]: no-op invariant check; the input is already a reduced scalar. *)
Definition spec_secp256k1_scalar_verify : ident * funspec :=
  DECLARE _secp256k1_scalar_verify
  WITH a_ptr : val, a : Scalar, sh : share
  PRE [ tptr t_secp256k1_scalar ]
    PROP (readable_share sh)
    PARAMS (a_ptr)
    SEP (scalar_at sh a_ptr a)
  POST [ tvoid ]
    PROP ()
    RETURN ()
    SEP (scalar_at sh a_ptr a).

(* ================================================================= *)
(** ** Boolean predicates -- [is_zero] / [is_one] / [is_even] / [is_high] / [eq]. *)

(** [is_zero]: return 1 iff [*a = 0]. *)
Definition spec_secp256k1_scalar_is_zero : ident * funspec :=
  DECLARE _secp256k1_scalar_is_zero
  WITH a_ptr : val, a : Scalar, sh : share
  PRE [ tptr t_secp256k1_scalar ]
    PROP (readable_share sh)
    PARAMS (a_ptr)
    SEP (scalar_at sh a_ptr a)
  POST [ tint ]
    PROP ()
    RETURN (Vint (Int.repr (if Z.eq_dec (scalar_val a) 0 then 1 else 0)))
    SEP (scalar_at sh a_ptr a).

(** [is_one]: return 1 iff [*a = 1]. *)
Definition spec_secp256k1_scalar_is_one : ident * funspec :=
  DECLARE _secp256k1_scalar_is_one
  WITH a_ptr : val, a : Scalar, sh : share
  PRE [ tptr t_secp256k1_scalar ]
    PROP (readable_share sh)
    PARAMS (a_ptr)
    SEP (scalar_at sh a_ptr a)
  POST [ tint ]
    PROP ()
    RETURN (Vint (Int.repr (if Z.eq_dec (scalar_val a) 1 then 1 else 0)))
    SEP (scalar_at sh a_ptr a).

(** [is_even]: return 1 iff [*a] is even. *)
Definition spec_secp256k1_scalar_is_even : ident * funspec :=
  DECLARE _secp256k1_scalar_is_even
  WITH a_ptr : val, a : Scalar, sh : share
  PRE [ tptr t_secp256k1_scalar ]
    PROP (readable_share sh)
    PARAMS (a_ptr)
    SEP (scalar_at sh a_ptr a)
  POST [ tint ]
    PROP ()
    RETURN (Vint (Int.repr (if Z.even (scalar_val a) then 1 else 0)))
    SEP (scalar_at sh a_ptr a).

(** [is_high]: return 1 iff [*a > floor(N/2)]. *)
Definition spec_secp256k1_scalar_is_high : ident * funspec :=
  DECLARE _secp256k1_scalar_is_high
  WITH a_ptr : val, a : Scalar, sh : share
  PRE [ tptr t_secp256k1_scalar ]
    PROP (readable_share sh)
    PARAMS (a_ptr)
    SEP (scalar_at sh a_ptr a)
  POST [ tint ]
    PROP ()
    RETURN (Vint (Int.repr (if Z_lt_dec secp256k1_N_H (scalar_val a) then 1 else 0)))
    SEP (scalar_at sh a_ptr a).

(** [eq]: return 1 iff [*a = *b]. *)
Definition spec_secp256k1_scalar_eq : ident * funspec :=
  DECLARE _secp256k1_scalar_eq
  WITH a_ptr : val, b_ptr : val, a : Scalar, b : Scalar,
       sh_a : share, sh_b : share
  PRE [ tptr t_secp256k1_scalar, tptr t_secp256k1_scalar ]
    PROP (readable_share sh_a;
          readable_share sh_b)
    PARAMS (a_ptr; b_ptr)
    SEP (scalar_at sh_a a_ptr a;
         scalar_at sh_b b_ptr b)
  POST [ tint ]
    PROP ()
    RETURN (Vint (Int.repr (if Z.eq_dec (scalar_val a) (scalar_val b) then 1 else 0)))
    SEP (scalar_at sh_a a_ptr a;
         scalar_at sh_b b_ptr b).

(* ================================================================= *)
(** ** Modular arithmetic -- [negate] / [half] / [add] / [cadd_bit] / [cond_negate]. *)

(** [negate]: set [*r] to [-a mod N].  The [alias] flag covers the in-place
    call [negate(r, r)] (used by [split_lambda]). *)
Definition spec_secp256k1_scalar_negate : ident * funspec :=
  DECLARE _secp256k1_scalar_negate
  WITH r_ptr : val, a_ptr : val, a : Scalar, sh_r : share, sh_a : share, alias : bool
  PRE [ tptr t_secp256k1_scalar, tptr t_secp256k1_scalar ]
    PROP (writable_share sh_r;
          alias = true -> a_ptr = r_ptr;
          alias = false -> readable_share sh_a)
    PARAMS (r_ptr; a_ptr)
    SEP (if alias
         then scalar_at sh_r r_ptr a
         else (data_at_ sh_r t_secp256k1_scalar r_ptr * scalar_at sh_a a_ptr a))
  POST [ tvoid ]
    EX r : Scalar,
    PROP (Z.modulo (Z.add (scalar_val a) (scalar_val r)) secp256k1_N = 0)
    RETURN ()
    SEP (if alias
         then scalar_at sh_r r_ptr r
         else (scalar_at sh_r r_ptr r * scalar_at sh_a a_ptr a)).

(** [half]: set [*r] to [a/2 mod N]. *)
Definition spec_secp256k1_scalar_half : ident * funspec :=
  DECLARE _secp256k1_scalar_half
  WITH r_ptr : val, a_ptr : val, a : Scalar, sh_r : share, sh_a : share
  PRE [ tptr t_secp256k1_scalar, tptr t_secp256k1_scalar ]
    PROP (writable_share sh_r;
          readable_share sh_a)
    PARAMS (r_ptr; a_ptr)
    SEP (data_at_ sh_r t_secp256k1_scalar r_ptr;
         scalar_at sh_a a_ptr a)
  POST [ tvoid ]
    EX r : Scalar,
    PROP (Z.modulo (Z.mul 2 (scalar_val r)) secp256k1_N = scalar_val a)
    RETURN ()
    SEP (scalar_at sh_r r_ptr r;
         scalar_at sh_a a_ptr a).

(** [add]: set [*r] to [(a+b) mod N]; return 1 iff [a+b >= N] (overflowed).
    The [alias] flag covers the in-place call [add(r, r, b)] (used by
    [split_lambda]); the second argument [b] is always a distinct pointer. *)
Definition spec_secp256k1_scalar_add : ident * funspec :=
  DECLARE _secp256k1_scalar_add
  WITH r_ptr : val, a_ptr : val, b_ptr : val, a : Scalar, b : Scalar,
       sh_r : share, sh_a : share, sh_b : share, alias : bool
  PRE [ tptr t_secp256k1_scalar, tptr t_secp256k1_scalar, tptr t_secp256k1_scalar ]
    PROP (writable_share sh_r;
          readable_share sh_b;
          alias = true -> a_ptr = r_ptr;
          alias = false -> readable_share sh_a)
    PARAMS (r_ptr; a_ptr; b_ptr)
    SEP (if alias
         then (scalar_at sh_r r_ptr a * scalar_at sh_b b_ptr b)
         else (data_at_ sh_r t_secp256k1_scalar r_ptr *
               scalar_at sh_a a_ptr a * scalar_at sh_b b_ptr b))
  POST [ tint ]
    EX r : Scalar,
    PROP (r = scalar_add a b)
    RETURN (Vint (Int.repr
             (if Z_le_dec secp256k1_N (Z.add (scalar_val a) (scalar_val b))
              then 1 else 0)))
    SEP (if alias
         then (scalar_at sh_r r_ptr r * scalar_at sh_b b_ptr b)
         else (scalar_at sh_r r_ptr r * scalar_at sh_a a_ptr a * scalar_at sh_b b_ptr b)).

(** [cadd_bit]: add [flag * 2^bit] to [*r]; the result must not overflow [N]. *)
Definition spec_secp256k1_scalar_cadd_bit : ident * funspec :=
  DECLARE _secp256k1_scalar_cadd_bit
  WITH r_ptr : val, r0 : Scalar, bit : Z, flag : Z, sh : share
  PRE [ tptr t_secp256k1_scalar, tuint, tint ]
    PROP (writable_share sh;
          (0 <= bit < 256)%Z;
          flag = 0 \/ flag = 1;
          (scalar_val r0 + flag * 2 ^ bit < secp256k1_N)%Z)
    PARAMS (r_ptr; Vint (Int.repr bit); Vint (Int.repr flag))
    SEP (scalar_at sh r_ptr r0)
  POST [ tvoid ]
    EX r : Scalar,
    PROP ((scalar_val r = scalar_val r0 + flag * 2 ^ bit)%Z)
    RETURN ()
    SEP (scalar_at sh r_ptr r).

(** [cond_negate]: if [flag], set [*r] to [-r mod N]; return [-1] if negated,
    [1] otherwise. *)
Definition spec_secp256k1_scalar_cond_negate : ident * funspec :=
  DECLARE _secp256k1_scalar_cond_negate
  WITH r_ptr : val, r0 : Scalar, flag : Z, sh : share
  PRE [ tptr t_secp256k1_scalar, tint ]
    PROP (writable_share sh;
          flag = 0 \/ flag = 1)
    PARAMS (r_ptr; Vint (Int.repr flag))
    SEP (scalar_at sh r_ptr r0)
  POST [ tint ]
    EX r : Scalar,
    PROP (r = if Z.eq_dec flag 1 then scalar_negate r0 else r0)
    RETURN (Vint (Int.repr (if Z.eq_dec flag 1 then (-1) else 1)))
    SEP (scalar_at sh r_ptr r).

(* ================================================================= *)
(** ** 128-bit split -- [split_128] [r1 = k mod 2^128] / [r2 = k / 2^128]. *)

(** [split_128]: set [*r1] to the low 128 bits of [k], [*r2] to the high. *)
Definition spec_secp256k1_scalar_split_128 : ident * funspec :=
  DECLARE _secp256k1_scalar_split_128
  WITH r1_ptr : val, r2_ptr : val, k_ptr : val, k : Scalar,
       sh1 : share, sh2 : share, shk : share
  PRE [ tptr t_secp256k1_scalar, tptr t_secp256k1_scalar, tptr t_secp256k1_scalar ]
    PROP (writable_share sh1;
          writable_share sh2;
          readable_share shk)
    PARAMS (r1_ptr; r2_ptr; k_ptr)
    SEP (data_at_ sh1 t_secp256k1_scalar r1_ptr;
         data_at_ sh2 t_secp256k1_scalar r2_ptr;
         scalar_at shk k_ptr k)
  POST [ tvoid ]
    EX r1 : Scalar, EX r2 : Scalar,
    PROP ((scalar_val r1 = scalar_val k mod 2 ^ 128)%Z;
          (scalar_val r2 = scalar_val k / 2 ^ 128)%Z)
    RETURN ()
    SEP (scalar_at sh1 r1_ptr r1;
         scalar_at sh2 r2_ptr r2;
         scalar_at shk k_ptr k).

(* ================================================================= *)
(** ** Big-endian (de)serialization -- [set_b32] / [set_b32_seckey] / [get_b32]. *)

(** [set_b32]: parse a 32-byte big-endian array, reduce mod [N], and store the
    overflow flag through [overflow] (specced for a non-NULL [overflow]). *)
Definition spec_secp256k1_scalar_set_b32 : ident * funspec :=
  DECLARE _secp256k1_scalar_set_b32
  WITH r_ptr : val, b32_ptr : val, ovf_ptr : val, bs : list Z,
       sh_r : share, sh_b : share, sh_o : share
  PRE [ tptr t_secp256k1_scalar, tptr tuchar, tptr tint ]
    PROP (writable_share sh_r;
          readable_share sh_b;
          writable_share sh_o;
          Zlength bs = 32;
          Forall (fun b => (0 <= b < 256)%Z) bs)
    PARAMS (r_ptr; b32_ptr; ovf_ptr)
    SEP (data_at_ sh_r t_secp256k1_scalar r_ptr;
         bytes32_at sh_b b32_ptr bs;
         data_at_ sh_o tint ovf_ptr)
  POST [ tvoid ]
    EX r : Scalar,
    PROP ((scalar_val r = Z_of_be_bytes bs mod secp256k1_N)%Z)
    RETURN ()
    SEP (scalar_at sh_r r_ptr r;
         bytes32_at sh_b b32_ptr bs;
         data_at sh_o tint
           (Vint (Int.repr (if Z_le_dec secp256k1_N (Z_of_be_bytes bs)
                            then 1 else 0))) ovf_ptr).

(** [set_b32_seckey]: parse a 32-byte key; return 1 iff it is a valid secret
    key (no overflow and nonzero). *)
Definition spec_secp256k1_scalar_set_b32_seckey : ident * funspec :=
  DECLARE _secp256k1_scalar_set_b32_seckey
  WITH r_ptr : val, bin_ptr : val, bs : list Z, sh_r : share, sh_b : share
  PRE [ tptr t_secp256k1_scalar, tptr tuchar ]
    PROP (writable_share sh_r;
          readable_share sh_b;
          Zlength bs = 32;
          Forall (fun b => (0 <= b < 256)%Z) bs)
    PARAMS (r_ptr; bin_ptr)
    SEP (data_at_ sh_r t_secp256k1_scalar r_ptr;
         bytes32_at sh_b bin_ptr bs)
  POST [ tint ]
    EX r : Scalar,
    PROP ((scalar_val r = Z_of_be_bytes bs mod secp256k1_N)%Z)
    RETURN (Vint (Int.repr
             (if Z_lt_dec (Z_of_be_bytes bs) secp256k1_N
              then (if Z.eq_dec (Z_of_be_bytes bs) 0 then 0 else 1)
              else 0)))
    SEP (scalar_at sh_r r_ptr r;
         bytes32_at sh_b bin_ptr bs).

(** [get_b32]: serialize [*a] as 32 big-endian bytes into [bin]. *)
Definition spec_secp256k1_scalar_get_b32 : ident * funspec :=
  DECLARE _secp256k1_scalar_get_b32
  WITH bin_ptr : val, a_ptr : val, a : Scalar, sh_bin : share, sh_a : share
  PRE [ tptr tuchar, tptr t_secp256k1_scalar ]
    PROP (writable_share sh_bin;
          readable_share sh_a)
    PARAMS (bin_ptr; a_ptr)
    SEP (bytes32_at_ sh_bin bin_ptr;
         scalar_at sh_a a_ptr a)
  POST [ tvoid ]
    PROP ()
    RETURN ()
    SEP (bytes32_at sh_bin bin_ptr (be_bytes_of_Z (scalar_val a) 32%nat);
         scalar_at sh_a a_ptr a).

(* ================================================================= *)
(** ** Rounded multiply-shift -- [mul_shift_var] [round(a*b / 2^shift)]. *)

(** ([shift_limb] is internal -- see [contract/impl/scalar.v].) *)

(** [mul_shift_var]: set [*r] to [round(a*b / 2^shift)] (shift in [[256,512))]). *)
Definition spec_secp256k1_scalar_mul_shift_var : ident * funspec :=
  DECLARE _secp256k1_scalar_mul_shift_var
  WITH r_ptr : val, a_ptr : val, b_ptr : val, shift : Z, a : Scalar, b : Scalar,
       sh_r : share, sh_a : share, sh_b : share
  PRE [ tptr t_secp256k1_scalar, tptr t_secp256k1_scalar,
        tptr t_secp256k1_scalar, tuint ]
    PROP (writable_share sh_r;
          readable_share sh_a;
          readable_share sh_b;
          (256 <= shift)%Z;
          (shift < 512)%Z)
    PARAMS (r_ptr; a_ptr; b_ptr; Vint (Int.repr shift))
    SEP (data_at_ sh_r t_secp256k1_scalar r_ptr;
         scalar_at sh_a a_ptr a;
         scalar_at sh_b b_ptr b)
  POST [ tvoid ]
    EX r : Scalar,
    PROP ((scalar_val r = scalar_mul_shift a b shift)%Z)
    RETURN ()
    SEP (scalar_at sh_r r_ptr r;
         scalar_at sh_a a_ptr a;
         scalar_at sh_b b_ptr b).

(* ================================================================= *)
(** ** Bit extraction -- [get_bits_limb32] / [get_bits_var] [(a >> offset) mod 2^count]. *)

(** [get_bits_limb32]: extract the [count] bits of [*a] starting at bit
    [offset], when the window lies within a single 64-bit limb (the caller
    guarantees [offset mod 64 + count <= 64]).  Returns the bit-slice
    [(a / 2^offset) mod 2^count]. *)
Definition spec_secp256k1_scalar_get_bits_limb32 : ident * funspec :=
  DECLARE _secp256k1_scalar_get_bits_limb32
  WITH a_ptr : val, a : Scalar, offset : Z, count : Z, sh : share
  PRE [ tptr t_secp256k1_scalar, tuint, tuint ]
    PROP (readable_share sh;
          (0 < count <= 32)%Z;
          (0 <= offset)%Z;
          (offset mod 64 + count <= 64)%Z;
          (offset + count <= 256)%Z)
    PARAMS (a_ptr; Vint (Int.repr offset); Vint (Int.repr count))
    SEP (scalar_at sh a_ptr a)
  POST [ tuint ]
    PROP ()
    RETURN (Vint (Int.repr ((scalar_val a / 2 ^ offset) mod 2 ^ count)))
    SEP (scalar_at sh a_ptr a).

(** [get_bits_var]: extract the [count] bits of [*a] starting at bit [offset]
    (variable-time; correctly handles a window straddling two adjacent limbs).
    Returns the bit-slice [(a / 2^offset) mod 2^count]. *)
Definition spec_secp256k1_scalar_get_bits_var : ident * funspec :=
  DECLARE _secp256k1_scalar_get_bits_var
  WITH a_ptr : val, a : Scalar, offset : Z, count : Z, sh : share
  PRE [ tptr t_secp256k1_scalar, tuint, tuint ]
    PROP (readable_share sh;
          (0 < count <= 32)%Z;
          (0 <= offset)%Z;
          (offset + count <= 256)%Z)
    PARAMS (a_ptr; Vint (Int.repr offset); Vint (Int.repr count))
    SEP (scalar_at sh a_ptr a)
  POST [ tuint ]
    PROP ()
    RETURN (Vint (Int.repr ((scalar_val a / 2 ^ offset) mod 2 ^ count)))
    SEP (scalar_at sh a_ptr a).

(* ================================================================= *)
(** ** Lambda endomorphism split -- [split_lambda] [r1 + lambda*r2 == k (mod N)]. *)

(** [split_lambda]: find [r1], [r2] with [r1 + lambda*r2 == k (mod N)], each
    (or its negation) at most 128 bits.  Reads the five constant global tables
    (lambda, [minus_b1], [minus_b2], [g1], [g2]) through [gv]. *)
Definition spec_secp256k1_scalar_split_lambda : ident * funspec :=
  DECLARE _secp256k1_scalar_split_lambda
  WITH r1_ptr : val, r2_ptr : val, k_ptr : val, k : Scalar, gv : globals,
       sh1 : share, sh2 : share, shk : share, sh_tab : share
  PRE [ tptr t_secp256k1_scalar, tptr t_secp256k1_scalar, tptr t_secp256k1_scalar ]
    PROP (writable_share sh1;
          writable_share sh2;
          readable_share shk;
          readable_share sh_tab)
    PARAMS (r1_ptr; r2_ptr; k_ptr)
    GLOBALS (gv)
    SEP (data_at_ sh1 t_secp256k1_scalar r1_ptr;
         data_at_ sh2 t_secp256k1_scalar r2_ptr;
         scalar_at shk k_ptr k;
         u256_at sh_tab (gv _secp256k1_const_lambda) c_lambda;
         u256_at sh_tab (gv _minus_b1) c_minus_b1;
         u256_at sh_tab (gv _minus_b2) c_minus_b2;
         u256_at sh_tab (gv _g1) c_g1;
         u256_at sh_tab (gv _g2) c_g2)
  POST [ tvoid ]
    EX r1 : Scalar, EX r2 : Scalar,
    PROP (((scalar_val r1 + secp256k1_lambda * scalar_val r2) mod secp256k1_N
             = scalar_val k)%Z;
          (scalar_val r1 < 2 ^ 128 \/ secp256k1_N - scalar_val r1 < 2 ^ 128)%Z;
          (scalar_val r2 < 2 ^ 128 \/ secp256k1_N - scalar_val r2 < 2 ^ 128)%Z)
    RETURN ()
    SEP (scalar_at sh1 r1_ptr r1;
         scalar_at sh2 r2_ptr r2;
         scalar_at shk k_ptr k;
         u256_at sh_tab (gv _secp256k1_const_lambda) c_lambda;
         u256_at sh_tab (gv _minus_b1) c_minus_b1;
         u256_at sh_tab (gv _minus_b2) c_minus_b2;
         u256_at sh_tab (gv _g1) c_g1;
         u256_at sh_tab (gv _g2) c_g2).

(* ================================================================= *)
(** ** Modular inverse -- [secp256k1_scalar_inverse] / [_var]. *)

(** Public scalar API ([src/scalar.h]).  Both reference the [Signed62] /
    [make_modinfo] glue ([contract/helper/signed62.v]) and the constant
    [secp256k1_const_modinfo_scalar] holding [make_modinfo N]; the bodies are
    proved (in [verif/scalar/scalar_inverse{,_var}.v]) against the modinv call
    graph via [to_signed62] + the safegcd driver + [from_signed62].  The POSTs
    state the model spec [is_modular_inverse (scalar_val x) N (scalar_val r)]
    ([r] reduced; [x = 0 -> r = 0]; [rel_prime x N -> x*r = 1 mod N]); there is
    NO coprimality precondition -- [N] is prime
    ([model.constants.secp256k1_N_prime]), so every scalar is invertible (or 0). *)

(** [secp256k1_scalar_inverse_var]: set [*r] to the modular inverse of [*x]
    (variable-time, reads the de Bruijn table): the result [r] satisfies
    [(scalar_val x * scalar_val r) mod N = 1] when [x <> 0] (and [r = 0] when
    [x = 0]).  Non-aliasing ([r] and [x] distinct). *)
Definition spec_secp256k1_scalar_inverse_var : ident * funspec :=
  DECLARE _secp256k1_scalar_inverse_var
  WITH r_ptr : val, x_ptr : val, x : Scalar, gv : globals,
       sh_r : share, sh_x : share, sh_modinfo : share, sh_debruijn : share
  PRE [ tptr t_secp256k1_scalar, tptr t_secp256k1_scalar ]
    PROP (writable_share sh_r;
          readable_share sh_x;
          readable_share sh_modinfo;
          readable_share sh_debruijn)
    PARAMS (r_ptr; x_ptr)
    GLOBALS (gv)
    SEP (data_at_ sh_r t_secp256k1_scalar r_ptr;
         scalar_at sh_x x_ptr x;
         modinfo_at sh_modinfo (gv _secp256k1_const_modinfo_scalar) secp256k1_N;
         debruijn64_array sh_debruijn gv)
  POST [ tvoid ]
    EX r : Scalar,
    PROP (is_modular_inverse (scalar_val x) secp256k1_N (scalar_val r))
    RETURN ()
    SEP (scalar_at sh_r r_ptr r;
         scalar_at sh_x x_ptr x;
         modinfo_at sh_modinfo (gv _secp256k1_const_modinfo_scalar) secp256k1_N;
         debruijn64_array sh_debruijn gv).

(** [secp256k1_scalar_inverse]: constant-time scalar modular inverse.  Same
    property POST as [..._inverse_var] but through the constant-time driver, so
    the spec drops the debruijn-table SEP.  Non-aliasing. *)
Definition spec_secp256k1_scalar_inverse : ident * funspec :=
  DECLARE _secp256k1_scalar_inverse
  WITH r_ptr : val, x_ptr : val, x : Scalar, gv : globals,
       sh_r : share, sh_x : share, sh_modinfo : share
  PRE [ tptr t_secp256k1_scalar, tptr t_secp256k1_scalar ]
    PROP (writable_share sh_r;
          readable_share sh_x;
          readable_share sh_modinfo)
    PARAMS (r_ptr; x_ptr)
    GLOBALS (gv)
    SEP (data_at_ sh_r t_secp256k1_scalar r_ptr;
         scalar_at sh_x x_ptr x;
         modinfo_at sh_modinfo (gv _secp256k1_const_modinfo_scalar) secp256k1_N)
  POST [ tvoid ]
    EX r : Scalar,
    PROP (is_modular_inverse (scalar_val x) secp256k1_N (scalar_val r))
    RETURN ()
    SEP (scalar_at sh_r r_ptr r;
         scalar_at sh_x x_ptr x;
         modinfo_at sh_modinfo (gv _secp256k1_const_modinfo_scalar) secp256k1_N).
