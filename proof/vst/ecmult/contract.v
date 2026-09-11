(** * vst.ecmult.contract: funspecs for src/ecmult_gen.h. *)
(** Copyright (C) 2026 remix7531
    SPDX-License-Identifier: MIT *)

(** The precomputed table is a global in the extracted program. Its contents
    are modelled in [theory/ecmult/tables.v]. *)

Require Import secp256k1.vst.base.
Require Import secp256k1.vst.composites.
Require Import secp256k1.vst.helper.structs_group.
Require Import secp256k1.vst.helper.structs_scalar.
Require Import secp256k1.theory.scalar.limbs.
Require Import secp256k1.theory.ecmult.ecmult_gen.

Definition t_secp256k1_ecmult_gen_context : type :=
  Tstruct ltac:(derive_struct_id
    (cons (_built, Some tint)
      (cons (_scalar_offset, @None type)
        (cons (_ge_offset, @None type)
          (cons (_proj_blind, @None type) nil))))) noattr.

(* ================================================================= *)
(** ** [secp256k1_ecmult_gen_ge]: multiplication by the generator.

    The contract describes allocated memory and permissions. It does not
    relate the scalar, point, or context contents to the mathematical model. *)

Definition spec_secp256k1_ecmult_gen_ge : ident * funspec :=
  DECLARE _secp256k1_ecmult_gen_ge
  WITH ctx_ptr : val, r_ptr : val, n_ptr : val, n : Z,
       sh_ctx : share, sh_r : share, sh_n : share
  PRE [ tptr t_secp256k1_ecmult_gen_context,
        tptr t_secp256k1_ge,
        tptr t_secp256k1_scalar ]
    PROP (readable_share sh_ctx;
          writable_share sh_r;
          readable_share sh_n;
          (0 <= n < secp256k1_N)%Z)
    PARAMS (ctx_ptr; r_ptr; n_ptr)
    SEP (memory_block sh_ctx (sizeof t_secp256k1_ecmult_gen_context) ctx_ptr;
         memory_block sh_r (sizeof t_secp256k1_ge) r_ptr;
         memory_block sh_n (sizeof t_secp256k1_scalar) n_ptr)
  POST [ tvoid ]
    PROP ()
    RETURN ()
    SEP (memory_block sh_ctx (sizeof t_secp256k1_ecmult_gen_context) ctx_ptr;
         memory_block sh_r (sizeof t_secp256k1_ge) r_ptr;
         memory_block sh_n (sizeof t_secp256k1_scalar) n_ptr).

(* ================================================================= *)
(** ** Generator multiplication contracts. *)
Definition Gprog_ecmult_gen_scaffold : funspecs := [
  spec_secp256k1_ecmult_gen_ge
].
