(** * structs_scalar: clightgen struct-id aliases for the scalar subsystem. *)
(** Copyright (C) 2026 remix7531
    SPDX-License-Identifier: MIT *)

From compcert Require Import Ctypes.
Require Import secp256k1.clight.extraction.
Require Import secp256k1.vst.composites.

(* secp256k1_scalar = { uint64_t d[4] } -- ids derived by member signature
   (see [vst/composites.v]), independent of anonymous identifier numbering. *)
Definition t_secp256k1_scalar : type :=
  Tstruct ltac:(derive_struct_id (cons (_d, @None type) nil)) noattr.
Definition t_secp256k1_uint256 : type := t_secp256k1_scalar.

(* The scalar reduction accumulator stores three 64-bit limbs. *)
Definition t_secp256k1_acc : type :=
  Tstruct ltac:(derive_struct_id
                  (cons (_c0, @None type)
                     (cons (_c1, @None type)
                        (cons (_c2, @None type) nil)))) noattr.
