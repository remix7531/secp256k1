(** * audit.statement: the pin on the headline theorem. *)
(** Copyright (C) 2026 remix7531
    SPDX-License-Identifier: MIT *)

(** Gate 3 of [audit/check.sh]: this file names [secp256k1_fv.secp256k1_verified]
    and re-states its FULL type, pasted verbatim from that theorem's statement in
    [../secp256k1_fv.v], as a bare [Check].  If the headline is later renamed,
    weakened (a conjunct dropped, a [Gprog] context swapped for a bigger one that
    hides a missing callee, a funspec replaced by a namesake with a looser
    postcondition), or reshaped in any way that changes its type, this [Check]
    stops typechecking and [make audit] / [make axioms] fails loudly instead of
    silently accepting a quieter theorem under the same name.

    Update this file ONLY after re-reviewing [secp256k1_fv.v]'s headline: copy the
    new type across, do not "fix" this file to match a change you have not
    reviewed. *)

Require Import secp256k1.vst.base.

Require Import secp256k1.contract.int128.
Require Import secp256k1.contract.util.
Require Import secp256k1.contract.scalar.
Require Import secp256k1.contract.field.
Require Import secp256k1.contract.modinv.

Require secp256k1.contract.gprog.int128.
Require secp256k1.contract.gprog.util.
Require secp256k1.contract.gprog.scalar.
Require secp256k1.contract.gprog.field.
Require secp256k1.contract.gprog.modinv.

Require secp256k1.secp256k1_fv.

(* ================================================================= *)
(** ** The pin -- the exact type of [secp256k1_verified], pasted verbatim. *)

Check (secp256k1_fv.secp256k1_verified :
  semax_body Vprog secp256k1.contract.gprog.int128.Gprog
    f_secp256k1_u128_load spec_secp256k1_u128_load /\
  semax_body Vprog secp256k1.contract.gprog.int128.Gprog
    f_secp256k1_u128_mul spec_secp256k1_u128_mul /\
  semax_body Vprog secp256k1.contract.gprog.int128.Gprog
    f_secp256k1_u128_accum_mul spec_secp256k1_u128_accum_mul /\
  semax_body Vprog secp256k1.contract.gprog.int128.Gprog
    f_secp256k1_u128_accum_u64 spec_secp256k1_u128_accum_u64 /\
  semax_body Vprog secp256k1.contract.gprog.int128.Gprog
    f_secp256k1_u128_rshift spec_secp256k1_u128_rshift /\
  semax_body Vprog secp256k1.contract.gprog.int128.Gprog
    f_secp256k1_u128_to_u64 spec_secp256k1_u128_to_u64 /\
  semax_body Vprog secp256k1.contract.gprog.int128.Gprog
    f_secp256k1_u128_hi_u64 spec_secp256k1_u128_hi_u64 /\
  semax_body Vprog secp256k1.contract.gprog.int128.Gprog
    f_secp256k1_u128_from_u64 spec_secp256k1_u128_from_u64 /\
  semax_body Vprog secp256k1.contract.gprog.int128.Gprog
    f_secp256k1_u128_check_bits spec_secp256k1_u128_check_bits /\
  semax_body Vprog secp256k1.contract.gprog.int128.Gprog
    f_secp256k1_i128_load spec_secp256k1_i128_load /\
  semax_body Vprog secp256k1.contract.gprog.int128.Gprog
    f_secp256k1_i128_mul spec_secp256k1_i128_mul /\
  semax_body Vprog secp256k1.contract.gprog.int128.Gprog
    f_secp256k1_i128_accum_mul spec_secp256k1_i128_accum_mul /\
  semax_body Vprog secp256k1.contract.gprog.int128.Gprog
    f_secp256k1_i128_det spec_secp256k1_i128_det /\
  semax_body Vprog secp256k1.contract.gprog.int128.Gprog
    f_secp256k1_i128_rshift spec_secp256k1_i128_rshift /\
  semax_body Vprog secp256k1.contract.gprog.int128.Gprog
    f_secp256k1_i128_to_u64 spec_secp256k1_i128_to_u64 /\
  semax_body Vprog secp256k1.contract.gprog.int128.Gprog
    f_secp256k1_i128_to_i64 spec_secp256k1_i128_to_i64 /\
  semax_body Vprog secp256k1.contract.gprog.int128.Gprog
    f_secp256k1_i128_from_i64 spec_secp256k1_i128_from_i64 /\
  semax_body Vprog secp256k1.contract.gprog.int128.Gprog
    f_secp256k1_i128_eq_var spec_secp256k1_i128_eq_var /\
  semax_body Vprog secp256k1.contract.gprog.int128.Gprog
    f_secp256k1_i128_check_pow2 spec_secp256k1_i128_check_pow2 /\
  semax_body Vprog secp256k1.contract.gprog.util.Gprog
    f_secp256k1_read_be64 spec_secp256k1_read_be64 /\
  semax_body Vprog secp256k1.contract.gprog.util.Gprog
    f_secp256k1_write_be64 spec_secp256k1_write_be64 /\
  semax_body Vprog secp256k1.contract.gprog.util.Gprog
    f_secp256k1_memzero_explicit spec_secp256k1_memzero_explicit /\
  semax_body Vprog secp256k1.contract.gprog.util.Gprog
    f_secp256k1_memclear_explicit spec_secp256k1_memclear_explicit /\
  semax_body Vprog secp256k1.contract.gprog.util.Gprog
    f_secp256k1_ctz64_var_debruijn spec_secp256k1_ctz64_var_debruijn /\
  semax_body Vprog secp256k1.contract.gprog.util.Gprog
    f_secp256k1_ctz64_var spec_secp256k1_ctz64_var /\
  semax_body Vprog secp256k1.contract.gprog.scalar.Gprog
    f_secp256k1_scalar_mul spec_secp256k1_scalar_mul /\
  semax_body Vprog secp256k1.contract.gprog.scalar.Gprog
    f_secp256k1_scalar_set_int spec_secp256k1_scalar_set_int /\
  semax_body Vprog secp256k1.contract.gprog.scalar.Gprog
    f_secp256k1_scalar_clear spec_secp256k1_scalar_clear /\
  semax_body Vprog secp256k1.contract.gprog.scalar.Gprog
    f_secp256k1_scalar_cmov spec_secp256k1_scalar_cmov /\
  semax_body Vprog secp256k1.contract.gprog.scalar.Gprog
    f_secp256k1_scalar_verify spec_secp256k1_scalar_verify /\
  semax_body Vprog secp256k1.contract.gprog.scalar.Gprog
    f_secp256k1_scalar_is_zero spec_secp256k1_scalar_is_zero /\
  semax_body Vprog secp256k1.contract.gprog.scalar.Gprog
    f_secp256k1_scalar_is_one spec_secp256k1_scalar_is_one /\
  semax_body Vprog secp256k1.contract.gprog.scalar.Gprog
    f_secp256k1_scalar_is_even spec_secp256k1_scalar_is_even /\
  semax_body Vprog secp256k1.contract.gprog.scalar.Gprog
    f_secp256k1_scalar_is_high spec_secp256k1_scalar_is_high /\
  semax_body Vprog secp256k1.contract.gprog.scalar.Gprog
    f_secp256k1_scalar_eq spec_secp256k1_scalar_eq /\
  semax_body Vprog secp256k1.contract.gprog.scalar.Gprog
    f_secp256k1_scalar_negate spec_secp256k1_scalar_negate /\
  semax_body Vprog secp256k1.contract.gprog.scalar.Gprog
    f_secp256k1_scalar_half spec_secp256k1_scalar_half /\
  semax_body Vprog secp256k1.contract.gprog.scalar.Gprog
    f_secp256k1_scalar_add spec_secp256k1_scalar_add /\
  semax_body Vprog secp256k1.contract.gprog.scalar.Gprog
    f_secp256k1_scalar_cadd_bit spec_secp256k1_scalar_cadd_bit /\
  semax_body Vprog secp256k1.contract.gprog.scalar.Gprog
    f_secp256k1_scalar_cond_negate spec_secp256k1_scalar_cond_negate /\
  semax_body Vprog secp256k1.contract.gprog.scalar.Gprog
    f_secp256k1_scalar_split_128 spec_secp256k1_scalar_split_128 /\
  semax_body Vprog secp256k1.contract.gprog.scalar.Gprog
    f_secp256k1_scalar_set_b32 spec_secp256k1_scalar_set_b32 /\
  semax_body Vprog secp256k1.contract.gprog.scalar.Gprog
    f_secp256k1_scalar_set_b32_seckey spec_secp256k1_scalar_set_b32_seckey /\
  semax_body Vprog secp256k1.contract.gprog.scalar.Gprog
    f_secp256k1_scalar_get_b32 spec_secp256k1_scalar_get_b32 /\
  semax_body Vprog secp256k1.contract.gprog.scalar.Gprog
    f_secp256k1_scalar_mul_shift_var spec_secp256k1_scalar_mul_shift_var /\
  semax_body Vprog secp256k1.contract.gprog.scalar.Gprog
    f_secp256k1_scalar_split_lambda spec_secp256k1_scalar_split_lambda /\
  semax_body Vprog secp256k1.contract.gprog.scalar.Gprog
    f_secp256k1_scalar_get_bits_limb32 spec_secp256k1_scalar_get_bits_limb32 /\
  semax_body Vprog secp256k1.contract.gprog.scalar.Gprog
    f_secp256k1_scalar_get_bits_var spec_secp256k1_scalar_get_bits_var /\
  semax_body Vprog secp256k1.contract.gprog.modinv.Gprog
    f_secp256k1_scalar_inverse_var spec_secp256k1_scalar_inverse_var /\
  semax_body Vprog secp256k1.contract.gprog.modinv.Gprog
    f_secp256k1_scalar_inverse spec_secp256k1_scalar_inverse /\
  semax_body Vprog secp256k1.contract.gprog.field.Gprog
    f_secp256k1_fe_impl_add spec_secp256k1_fe_impl_add /\
  semax_body Vprog secp256k1.contract.gprog.modinv.Gprog
    f_secp256k1_modinv64_var spec_secp256k1_modinv64_var /\
  semax_body Vprog secp256k1.contract.gprog.modinv.Gprog
    f_secp256k1_modinv64 spec_secp256k1_modinv64).
