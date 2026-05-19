(** * contract.gprog.int128: the int128-subsystem funspec context. *)
(** Copyright (C) 2026 remix7531
    SPDX-License-Identifier: MIT *)

Require Export secp256k1.vst.base.
Require Export secp256k1.contract.int128.
Require Export secp256k1.contract.impl.int128.

(** [src/int128.h] (+ the [int128_struct_impl.h] helpers): the u128 family
    then the i128 family. *)
Definition Gprog_int128 : funspecs := [
  spec_secp256k1_umul128;
  spec_secp256k1_u128_load;
  spec_secp256k1_u128_mul;
  spec_secp256k1_u128_accum_mul;
  spec_secp256k1_u128_accum_u64;
  spec_secp256k1_u128_rshift;
  spec_secp256k1_u128_to_u64;
  spec_secp256k1_u128_hi_u64;
  spec_secp256k1_u128_from_u64;
  spec_secp256k1_u128_check_bits;
  spec_secp256k1_mul128;
  spec_secp256k1_i128_load;
  spec_secp256k1_i128_mul;
  spec_secp256k1_i128_accum_mul;
  spec_secp256k1_i128_dissip_mul;
  spec_secp256k1_i128_det;
  spec_secp256k1_i128_rshift;
  spec_secp256k1_i128_to_u64;
  spec_secp256k1_i128_to_i64;
  spec_secp256k1_i128_from_i64;
  spec_secp256k1_i128_eq_var;
  spec_secp256k1_i128_check_pow2
].

Definition Gprog : funspecs := ltac:(with_library prog Gprog_int128).
