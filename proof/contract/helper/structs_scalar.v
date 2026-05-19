(** * structs_scalar: clightgen struct-id aliases for the scalar subsystem. *)
(** Copyright (C) 2026 remix7531
    SPDX-License-Identifier: MIT *)

(** Quarantined out of [vst/base.v] (see [structs_int128] for the
    rationale).  Depends only on the generated AST + CompCert [Ctypes]. *)

From compcert Require Import Ctypes.
Require Import secp256k1.clight.extraction.
Require Import secp256k1.vst.composites.

(* secp256k1_scalar = { uint64_t d[4] } -- ids derived by member signature
   (see [vst/composites.v]), so a re-extraction's renumber is a non-event. *)
Definition t_secp256k1_scalar : type :=
  Tstruct ltac:(derive_struct_id (cons (_d, @None type) nil)) noattr.
Definition t_secp256k1_uint256 : type := t_secp256k1_scalar.

(* The int128 multiply accumulator [secp256k1_accumulator] = { uint64_t c0, c1,
   c2 } -- consumed by the scalar reduce path
   (verif/scalar/impl/scalar_reduce_512.v), hence kept with the scalar structs.
   Historically the most drift-prone id (__1234 -> __1238 -> __1251 -> __1191);
   now derived. *)
Definition t_secp256k1_acc : type :=
  Tstruct ltac:(derive_struct_id
                  (cons (_c0, @None type)
                     (cons (_c1, @None type)
                        (cons (_c2, @None type) nil)))) noattr.
