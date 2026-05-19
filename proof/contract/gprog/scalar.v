(** * contract.gprog.scalar: the scalar-subsystem funspec context. *)
(** Copyright (C) 2026 remix7531
    SPDX-License-Identifier: MIT *)

(** Context = the scalar specs plus their callee subsystems (the mul/reduce
    pipeline forward_calls the u128 helpers; set/get_b32 the be64 utils).
    The two scalar-inverse entry points live in [contract.gprog.modinv] --
    they call into the safegcd drivers. *)

Require Export secp256k1.contract.gprog.int128.
Require Export secp256k1.contract.gprog.util.
Require Export secp256k1.contract.scalar.
Require Export secp256k1.contract.impl.scalar.

(** [src/scalar.h] / [scalar_4x64_impl.h]: the accumulator helpers, the
    reduction pipeline, and the public [secp256k1_scalar_mul]. *)
Definition Gprog_scalar : funspecs := [
  spec_secp256k1_scalar_muladd;
  spec_secp256k1_scalar_muladd_fast;
  spec_secp256k1_scalar_sumadd;
  spec_secp256k1_scalar_sumadd_fast;
  spec_secp256k1_scalar_extract;
  spec_secp256k1_scalar_extract_fast;
  spec_secp256k1_scalar_check_overflow;
  spec_secp256k1_scalar_reduce;
  spec_secp256k1_scalar_mul_512;
  spec_secp256k1_scalar_reduce_512;
  spec_secp256k1_scalar_mul;
  spec_secp256k1_scalar_set_int;
  spec_secp256k1_scalar_clear;
  spec_secp256k1_scalar_cmov;
  spec_secp256k1_scalar_verify;
  spec_secp256k1_scalar_is_zero;
  spec_secp256k1_scalar_is_one;
  spec_secp256k1_scalar_is_even;
  spec_secp256k1_scalar_is_high;
  spec_secp256k1_scalar_eq;
  spec_secp256k1_scalar_negate;
  spec_secp256k1_scalar_half;
  spec_secp256k1_scalar_add;
  spec_secp256k1_scalar_cadd_bit;
  spec_secp256k1_scalar_cond_negate;
  spec_secp256k1_scalar_split_128;
  spec_secp256k1_scalar_set_b32;
  spec_secp256k1_scalar_set_b32_seckey;
  spec_secp256k1_scalar_get_b32;
  spec_secp256k1_scalar_shift_limb;
  spec_secp256k1_scalar_mul_shift_var;
  spec_secp256k1_scalar_split_lambda;
  spec_secp256k1_scalar_get_bits_limb32;
  spec_secp256k1_scalar_get_bits_var
].

Definition Gprog : funspecs :=
  ltac:(with_library prog (Gprog_int128 ++ Gprog_util ++ Gprog_scalar)).
