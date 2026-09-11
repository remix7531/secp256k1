(** * structs_group: Clight struct aliases for group elements. *)
(** Copyright (C) 2026 remix7531
    SPDX-License-Identifier: MIT *)

From compcert Require Import Ctypes Clightdefs.
Require Import secp256k1.clight.extraction.
Require Import secp256k1.vst.composites.

Definition t_secp256k1_ge : type :=
  Tstruct ltac:(derive_struct_id
    (cons (_x, @None type)
      (cons (_y, @None type) (cons (_infinity, Some tint) nil)))) noattr.

Definition t_secp256k1_gej : type :=
  Tstruct ltac:(derive_struct_id
    (cons (_x, @None type)
      (cons (_y, @None type)
        (cons (_z, @None type) (cons (_infinity, Some tint) nil))))) noattr.
