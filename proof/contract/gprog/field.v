(** * contract.gprog.field: the field-subsystem funspec context. *)
(** Copyright (C) 2026 remix7531
    SPDX-License-Identifier: MIT *)

(** Context = the field specs plus their callee subsystems (the 5x52 bodies
    lean on the u128 helpers; normalize/cmp use nothing else today). *)

Require Export secp256k1.contract.gprog.int128.
Require Export secp256k1.contract.gprog.util.
Require Export secp256k1.contract.field.

(** [src/field.h] / [field_5x52_impl.h] (base [2^52]).  The first field op;
    grows as more [secp256k1_fe_*] bodies are verified.  New subsystems follow
    this convention: one [Gprog_<mod>] list, appended below. *)
Definition Gprog_field : funspecs := [
  spec_secp256k1_fe_impl_add
].

Definition Gprog : funspecs :=
  ltac:(with_library prog (Gprog_int128 ++ Gprog_util ++ Gprog_field)).
