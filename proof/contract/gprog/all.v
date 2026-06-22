(** * contract.gprog.all: the full funspec union (audit / linking anchor). *)
(** Copyright (C) 2026 remix7531
    SPDX-License-Identifier: MIT *)

(** Nobody under [verif/] proves against this context; it exists so the audit
    surface and a future [semax_func] whole-program theorem have the one
    global function-spec table.  [Gprog_all_list] deliberately EXCLUDES the
    Admitted jacobi spec -- the audited union is the proved surface. *)

Require Export secp256k1.contract.gprog.jacobi.
Require Export secp256k1.contract.gprog.field.

Definition Gprog_all_list : funspecs :=
  Gprog_int128 ++ Gprog_util ++ Gprog_scalar ++ Gprog_field ++ Gprog_modinv.

Definition Gprog : funspecs := ltac:(with_library prog Gprog_all_list).
