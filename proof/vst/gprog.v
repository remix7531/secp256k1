(** * vst.gprog: the funspec table for internal arithmetic proofs. *)
(** Copyright (C) 2026 remix7531
    SPDX-License-Identifier: MIT *)

(** Shared contracts for the internal arithmetic body proofs. *)

Require Export secp256k1.vst.base.
Require Export secp256k1.vst.int128.contract.
Require Export secp256k1.vst.int128.impl.
Require Export secp256k1.vst.util.contract.
Require Export secp256k1.vst.scalar.contract.
Require Export secp256k1.vst.scalar.impl.
Require Export secp256k1.vst.field.contract.
Require Export secp256k1.vst.modinv.contract.
Require Export secp256k1.vst.modinv.impl.

(* ================================================================= *)
(** ** Arithmetic contracts. *)

(** Each module contributes its public list and, where it has [static]
    helpers, its internal one.  The split is per FILE rather than per
    visibility choice: a module's [contract.v] and [impl.v] do not import
    each other, so neither can name the other's specs. *)

Definition Gprog_proved_list : funspecs :=
  Gprog_int128_public ++ Gprog_int128_impl
  ++ Gprog_util
  ++ Gprog_scalar_public
  ++ Gprog_scalar_impl
  ++ Gprog_field
  ++ Gprog_modinv_public
  ++ Gprog_modinv_impl.

(* ================================================================= *)
(** ** The shared table. *)

Definition Gprog_all_list : funspecs := Gprog_proved_list.

(** [with_library] adds the builtin and external declarations required by
    the proof framework. *)
Definition Gprog : funspecs := ltac:(with_library prog Gprog_all_list).
