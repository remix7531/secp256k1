(** * structs_modinv: clightgen struct-id aliases for the modinv (safegcd) subsystem. *)
(** Copyright (C) 2026 remix7531
    SPDX-License-Identifier: MIT *)

(** Quarantined out of [vst/base.v] (see [structs_int128] for the
    rationale).  Depends only on the generated AST + CompCert [Ctypes]. *)

From compcert Require Import Ctypes.
Require Import secp256k1.clight.extraction.
Require Import secp256k1.vst.composites.

(* modinv64 (safegcd) structs.  secp256k1_modinv64_var is a retained extraction
   target in extraction.c, so its whole call graph -- and these three structs
   -- are in this AST.  (Field shapes: signed62 = { int64_t v[5] }, modinfo =
   { signed62 modulus; uint64_t modulus_inv62 }, trans2x2 = { int64_t u,v,q,r }.)
   Ids derived by member signature (see [vst/composites.v]); [modinfo]'s nested
   [signed62] member is matched by name, so inner-id drift is irrelevant. *)
Definition t_secp256k1_modinv64_signed62 : type :=
  Tstruct ltac:(derive_struct_id (cons (_v, @None type) nil)) noattr.
Definition t_secp256k1_modinv64_modinfo  : type :=
  Tstruct ltac:(derive_struct_id
                  (cons (_modulus, @None type)
                     (cons (_modulus_inv62, @None type) nil))) noattr.
Definition t_secp256k1_modinv64_trans2x2 : type :=
  Tstruct ltac:(derive_struct_id
                  (cons (_u, @None type)
                     (cons (_v, @None type)
                        (cons (_q, @None type)
                           (cons (_r, @None type) nil))))) noattr.
