(** * structs_int128: clightgen struct-id aliases for the int128 subsystem. *)
(** Copyright (C) 2026 remix7531
    SPDX-License-Identifier: MIT *)

From compcert Require Import Ctypes.
Require Import secp256k1.clight.extraction.
Require Import secp256k1.vst.composites.

(* secp256k1_uint128 = { uint64_t lo, hi } -- id derived by member signature
   (see [vst/composites.v]), independent of anonymous identifier numbering. *)
Definition t_secp256k1_u128 : type :=
  Tstruct ltac:(derive_struct_id
                  (cons (_lo, @None type) (cons (_hi, @None type) nil))) noattr.

(* Signed and unsigned helpers use the same extracted struct. *)
Definition t_secp256k1_i128 : type := t_secp256k1_u128.
