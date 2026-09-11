(** * vst.group.contract: funspecs for src/group.h. *)
(** Copyright (C) 2026 remix7531
    SPDX-License-Identifier: MIT *)

(** Point resources are described by [memory_block], which records allocation
    and permissions without constraining coordinates. *)

Require Import secp256k1.vst.base.
Require Export secp256k1.vst.helper.structs_group.
Require secp256k1.specification.
Import specification.Math.
Import specification.Math.raw.

(* ================================================================= *)
(** ** [secp256k1_gej_add_ge]: mixed Jacobian and affine point addition. *)

Definition spec_secp256k1_gej_add_ge : ident * funspec :=
  DECLARE _secp256k1_gej_add_ge
  WITH r_ptr : val, a_ptr : val, b_ptr : val,
       sh_r : share, sh_a : share, sh_b : share
  PRE [ tptr t_secp256k1_gej, tptr t_secp256k1_gej,
        tptr t_secp256k1_ge ]
    PROP (writable_share sh_r;
          readable_share sh_a;
          readable_share sh_b)
    PARAMS (r_ptr; a_ptr; b_ptr)
    SEP (memory_block sh_r (sizeof t_secp256k1_gej) r_ptr;
         memory_block sh_a (sizeof t_secp256k1_gej) a_ptr;
         memory_block sh_b (sizeof t_secp256k1_ge) b_ptr)
  POST [ tvoid ]
    PROP ()
    RETURN ()
    SEP (memory_block sh_r (sizeof t_secp256k1_gej) r_ptr;
         memory_block sh_a (sizeof t_secp256k1_gej) a_ptr;
         memory_block sh_b (sizeof t_secp256k1_ge) b_ptr).

(* ================================================================= *)
(** ** Group contracts. *)
Definition Gprog_group_scaffold : funspecs := [
  spec_secp256k1_gej_add_ge
].
