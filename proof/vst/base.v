(** * vst.base: floyd + the Clight AST + [CompSpecs]/[Vprog] -- the VST root. *)
(** Copyright (C) 2026 remix7531
    SPDX-License-Identifier: MIT *)

(** Shared VST automation, arithmetic support, and the extracted C program. *)

Require Export VST.floyd.proofauto.
Require Export compcert.lib.Zbits.
Require Export secp256k1.clight.extraction.
Import Clightdefs.ClightNotations.
Local Open Scope clight_scope.

(* ================================================================= *)
(** ** The arithmetic program used by internal body proofs. *)

(** Internal arithmetic proofs use this subset of the full extraction. *)
Definition arithmetic_function_idents : list ident :=
  [_secp256k1_memzero_explicit; _secp256k1_memclear_explicit;
   _secp256k1_ctz64_var_debruijn; _secp256k1_ctz64_var;
   _secp256k1_read_be64; _secp256k1_write_be64;
   _secp256k1_modinv64_signed62_assign; _secp256k1_modinv64_normalize_62;
   _secp256k1_modinv64_divsteps_59; _secp256k1_modinv64_divsteps_62_var;
   _secp256k1_modinv64_update_de_limb; _secp256k1_modinv64_update_de_62;
   _secp256k1_modinv64_update_fg_62; _secp256k1_modinv64_update_fg_62_var;
   _secp256k1_modinv64; _secp256k1_modinv64_var;
   _secp256k1_scalar_set_int; _secp256k1_scalar_get_bits_limb32;
   _secp256k1_scalar_get_bits_var; _secp256k1_scalar_check_overflow;
   _secp256k1_scalar_reduce; _secp256k1_scalar_add;
   _secp256k1_scalar_cadd_bit; _secp256k1_scalar_set_b32;
   _secp256k1_scalar_get_b32; _secp256k1_scalar_is_zero;
   _secp256k1_scalar_negate; _secp256k1_scalar_half;
   _secp256k1_scalar_is_one; _secp256k1_scalar_is_high;
   _secp256k1_scalar_cond_negate; _secp256k1_scalar_muladd;
   _secp256k1_scalar_muladd_fast; _secp256k1_scalar_sumadd;
   _secp256k1_scalar_sumadd_fast; _secp256k1_scalar_extract;
   _secp256k1_scalar_extract_fast; _secp256k1_scalar_reduce_512;
   _secp256k1_scalar_mul_512; _secp256k1_scalar_mul;
   _secp256k1_scalar_split_128; _secp256k1_scalar_eq;
   _secp256k1_scalar_shift_limb; _secp256k1_scalar_mul_shift_var;
   _secp256k1_scalar_cmov; _secp256k1_scalar_from_signed62;
   _secp256k1_scalar_to_signed62; _secp256k1_scalar_inverse;
   _secp256k1_scalar_inverse_var; _secp256k1_scalar_is_even;
   _secp256k1_scalar_clear; _secp256k1_scalar_set_b32_seckey;
   _secp256k1_scalar_verify; _secp256k1_scalar_split_lambda;
   _secp256k1_umul128; _secp256k1_mul128; _secp256k1_u128_load;
   _secp256k1_u128_mul; _secp256k1_u128_accum_mul;
   _secp256k1_u128_accum_u64; _secp256k1_u128_rshift;
   _secp256k1_u128_to_u64; _secp256k1_u128_hi_u64;
   _secp256k1_u128_from_u64; _secp256k1_u128_check_bits;
   _secp256k1_i128_load; _secp256k1_i128_mul;
   _secp256k1_i128_accum_mul; _secp256k1_i128_dissip_mul;
   _secp256k1_i128_det; _secp256k1_i128_rshift;
   _secp256k1_i128_to_u64; _secp256k1_i128_to_i64;
   _secp256k1_i128_from_i64; _secp256k1_i128_eq_var;
   _secp256k1_i128_check_pow2; _secp256k1_fe_impl_add].

Definition arithmetic_variable_idents : list ident :=
  [_debruijn; _secp256k1_const_modinfo_scalar; _secp256k1_const_lambda;
   _minus_b1; _minus_b2; _g1; _g2].

Definition ident_in (identifiers : list ident) (identifier : ident) : bool :=
  existsb (Pos.eqb identifier) identifiers.

Definition arithmetic_global_definition
    (definition : ident * globdef Clight.fundef type) : bool :=
  match definition with
  | (identifier, Gfun (Internal _)) =>
      ident_in arithmetic_function_idents identifier
  | (identifier, Gvar _) => ident_in arithmetic_variable_idents identifier
  | (_, Gfun (External _ _ _ _)) => true
  end.

Definition arithmetic_global_definitions :
    list (ident * globdef Clight.fundef type) :=
  filter arithmetic_global_definition extraction.global_definitions.

Definition arithmetic_public_ident (identifier : ident) : bool :=
  existsb (fun definition => Pos.eqb identifier (fst definition))
    arithmetic_global_definitions.

Definition arithmetic_public_idents : list ident :=
  filter arithmetic_public_ident extraction.public_idents.

(** [_extraction_targets] is deliberately absent because its initializer
    refers to production functions outside this arithmetic program. *)
Definition prog : Clight.program :=
  Clightdefs.mkprogram extraction.composites arithmetic_global_definitions
    arithmetic_public_idents extraction._main Logic.I.

(* ================================================================= *)
(** ** CompSpecs / Vprog -- VST [compspecs] / [varspecs] from [prog]. *)

#[export] Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs. mk_varspecs prog. Defined.

(* ================================================================= *)
(** Struct aliases live in [vst/helper/structs_*.v] and are derived from
    member signatures rather than anonymous identifier numbers. *)
