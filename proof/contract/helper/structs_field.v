(** * structs_field: clightgen struct-id alias for the field subsystem. *)
(** Copyright (C) 2026 remix7531
    SPDX-License-Identifier: MIT *)

(** Quarantined out of [vst/base.v] (see [structs_int128] for the
    rationale).  Depends only on the generated AST + CompCert [Ctypes]. *)

From Stdlib Require Import ZArith.
From compcert Require Import Ctypes Clightdefs.
Require Import secp256k1.clight.extraction.
Require Import secp256k1.vst.composites.

(* secp256k1_fe = { uint64_t n[5] } (the base-2^52, 5-limb field element).  With
   VERIFY off, the magnitude/normalized debug fields are absent, so the extracted
   struct is the single [_n : tarray tulong 5] member.  The member TYPE is pinned
   in the signature because the future [fe_storage] is also a lone [_n], with
   [tarray tulong 4]. *)
Definition t_secp256k1_fe : type :=
  Tstruct ltac:(derive_struct_id
                  (cons (_n, @Some type (tarray tulong 5%Z)) nil)) noattr.
