(** * contract.gprog.modinv: the modinv (safegcd) funspec context. *)
(** Copyright (C) 2026 remix7531
    SPDX-License-Identifier: MIT *)

(** Context = the whole safegcd stack over the scalar context (the drivers
    convert through scalar <-> signed62, and the divstep bodies call the
    signed i128 helpers + ctz64). *)

Require Export secp256k1.contract.gprog.scalar.
Require Export secp256k1.contract.impl.modinv.

(** [src/modinv64.h] / [modinv64_impl.h]: the safegcd divstep stack, the two
    public drivers ([modinv64] / [modinv64_var]), and the [scalar <-> signed62]
    converters plus the two scalar-inverse entry points that bridge into them.
    The signed [i128_*] / [ctz64] helpers the modinv bodies call already live in
    [Gprog_int128] / [Gprog_util], so they are not repeated here. *)
Definition Gprog_modinv : funspecs := [
  spec_secp256k1_modinv64_signed62_assign;
  spec_secp256k1_modinv64_normalize_62;
  spec_secp256k1_modinv64_divsteps_62_var;
  spec_secp256k1_modinv64_divsteps_59;
  spec_secp256k1_modinv64_update_de_limb;
  spec_secp256k1_modinv64_update_de_62;
  spec_secp256k1_modinv64_update_fg_62_var;
  spec_secp256k1_modinv64_update_fg_62;
  spec_secp256k1_modinv64_var;
  spec_secp256k1_scalar_to_signed62;
  spec_secp256k1_scalar_from_signed62;
  spec_secp256k1_scalar_inverse_var;
  spec_secp256k1_modinv64;
  spec_secp256k1_scalar_inverse
].

Definition Gprog : funspecs :=
  ltac:(with_library prog
    (Gprog_int128 ++ Gprog_util ++ Gprog_scalar ++ Gprog_modinv)).
