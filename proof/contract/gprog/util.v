(** * contract.gprog.util: the util-subsystem funspec context. *)
(** Copyright (C) 2026 remix7531
    SPDX-License-Identifier: MIT *)

(** Per-subsystem [Gprog] contexts: every file under [contract/gprog/] defines
    the SAME identifier [Gprog] from a per-context spec list, so a verif file
    picks its context by which gprog file it Requires -- the [semax_body]
    statements never change.  Each context is a superset of the bodies'
    actual [forward_call] targets; [contract.gprog.all] keeps the full union
    for the audit surface and a future whole-program linking theorem. *)

Require Export secp256k1.vst.base.
Require Export secp256k1.contract.util.

(** [src/util.h]: the big-endian byte-order helpers used by the [set_b32] /
    [get_b32] scalar (de)serialization. *)
Definition Gprog_util : funspecs := [
  spec_secp256k1_read_be64;
  spec_secp256k1_write_be64;
  spec_secp256k1_memzero_explicit;
  spec_secp256k1_memclear_explicit;
  spec_secp256k1_ctz64_var_debruijn;
  spec_secp256k1_ctz64_var
].

Definition Gprog : funspecs := ltac:(with_library prog Gprog_util).
