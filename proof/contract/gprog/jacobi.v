(** * contract.gprog.jacobi: the jacobi funspec context (quarantines the Admitted spec). *)
(** Copyright (C) 2026 remix7531
    SPDX-License-Identifier: MIT *)

(** The ONLY context containing [spec_secp256k1_jacobi64_maybe_var], whose
    body is Admitted (an explicit outstanding gap): no other subsystem's
    proof can [forward_call] it, structurally.  Used solely by
    [verif/modinv/jacobi64_maybe_var.v]. *)

Require Export secp256k1.contract.gprog.modinv.
Require Export secp256k1.contract.jacobi.

(** [src/modinv64_impl.h]: the Jacobi-symbol helper. *)
Definition Gprog_jacobi : funspecs := [
  spec_secp256k1_jacobi64_maybe_var
].

Definition Gprog : funspecs :=
  ltac:(with_library prog
    (Gprog_int128 ++ Gprog_util ++ Gprog_scalar ++ Gprog_modinv
                  ++ Gprog_jacobi)).
