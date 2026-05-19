(** * structs_int128: clightgen struct-id aliases for the int128 subsystem. *)
(** Copyright (C) 2026 remix7531
    SPDX-License-Identifier: MIT *)

(** Quarantined out of [vst/base.v]: a re-extraction renumbers the
    anonymous composites, and pinning them here (rather than in the ~95-importer
    [vst/base.v]) confines that churn to the owning subsystem.  Depends only on
    the generated AST + CompCert [Ctypes] -- no [proofauto]/[CompSpecs] -- so it
    sits at the very bottom of the layer and can be required by the contract
    helpers without a cycle. *)

From compcert Require Import Ctypes.
Require Import secp256k1.clight.extraction.
Require Import secp256k1.vst.composites.

(* secp256k1_uint128 = { uint64_t lo, hi } -- id derived by member signature
   (see [vst/composites.v]), so a re-extraction's renumber is a non-event. *)
Definition t_secp256k1_u128 : type :=
  Tstruct ltac:(derive_struct_id
                  (cons (_lo, @None type) (cons (_hi, @None type) nil))) noattr.

(* The signed 128-bit helpers share the same anonymous { uint64_t lo, hi }
   struct as the unsigned ones in this single AST, so the signed alias is just
   the unsigned struct (replaces the old contract/modinv_int128.v alias). *)
Definition t_secp256k1_i128 : type := t_secp256k1_u128.
