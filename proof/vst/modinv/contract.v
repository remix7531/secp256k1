(** * vst.modinv.contract: PUBLIC funspecs for the safegcd modular inverse drivers
    [secp256k1_modinv64] / [secp256k1_modinv64_var]. *)
(** Copyright (C) 2026 remix7531
    Ported from BlockstreamResearch/simplicity Coq/C/secp256k1/spec_modinv64.v
    (commit c1dddedd), Copyright (c) 2018 Blockstream, originally MIT.
    Upstream notice reproduced in proof/README.md.
    SPDX-License-Identifier: MIT *)

(** This is the public [src/modinv64.h] surface.  The INTERNAL helper funspecs
    ([signed62_assign], [normalize_62], [divsteps_*], [update_*], [Trans_repr])
    and the modinv proving [Gprog] live in [vst/modinv/impl.v] (which
    re-exports this file).  [Signed62] / [make_modinfo] live in
    [vst/helper/signed62.v] and [debruijn64_array] / [ctz64_*] in
    [vst/util/contract.v]; both are re-exported here since the public specs use them.

    Struct aliases are derived from member signatures in [vst/helper]. *)

Require Import VST.floyd.proofauto.
Require Import secp256k1.vst.base.
Require Import secp256k1.vst.helper.structs_modinv.
Require Import secp256k1.theory.modinv.modinv.
(* [Signed62] / [make_modinfo] and [debruijn64_array] are used by the public
   specs; re-export so [vst/modinv/impl.v] (which re-exports this file) hands
   the whole surface to the verif layer. *)
Require Export secp256k1.vst.helper.signed62.
Require Export secp256k1.vst.util.contract.

Opaque Z.shiftr Z.pow.

(* ================================================================= *)
(** ** modinv funspecs -- [secp256k1_modinv64_var] + the driver itself. *)

(** [secp256k1_modinv64_var]: replace [*x] with its modular inverse
    [mod_inv x m] modulo [m] (variable-time safegcd driver). General version:
    [m] odd, [1 < m < 2^256], [0 <= x < m], and [x] coprime to [m] (or 0). *)
Definition spec_secp256k1_modinv64_var : ident * funspec :=
  DECLARE _secp256k1_modinv64_var
  WITH x : Z, m : Z, ptrx : val, modinfo : val,
       shx : share, sh_modinfo : share, sh_debruijn : share, gv : globals
  PRE [ tptr t_secp256k1_modinv64_signed62, tptr t_secp256k1_modinv64_modinfo ]
    PROP (Z.Odd m;
          0 <= x < m;
          1 < m < 2^256;
          x = 0 \/ rel_prime x m;
          writable_share shx;
          readable_share sh_modinfo;
          readable_share sh_debruijn)
    PARAMS (ptrx; modinfo)
    GLOBALS (gv)
    SEP (signed62_at shx ptrx x;
         modinfo_at sh_modinfo modinfo m;
         debruijn64_array sh_debruijn gv)
  POST [ tvoid ]
    EX rv : Z,
    PROP (is_modular_inverse x m rv)
    RETURN ()
    SEP (signed62_at shx ptrx rv;
         modinfo_at sh_modinfo modinfo m;
         debruijn64_array sh_debruijn gv).

(* ================================================================= *)
(** ** Constant-time driver -- [secp256k1_modinv64] (no debruijn table). *)

(** [secp256k1_modinv64]: replace [*x] with its modular inverse [mod_inv x m]
    modulo [m] -- the CONSTANT-time safegcd driver (a fixed 10*59 = 590
    divsteps).  Same contract as [..._var] but WITHOUT the debruijn table: the
    constant-time [divsteps_59] uses no [ctz64_var] table lookup.  General
    version: [m] odd, [1 < m < 2^256], [0 <= x < m], [x] coprime to [m] (or 0). *)
Definition spec_secp256k1_modinv64 : ident * funspec :=
  DECLARE _secp256k1_modinv64
  WITH x : Z, m : Z, ptrx : val, modinfo : val, shx : share, sh_modinfo : share
  PRE [ tptr t_secp256k1_modinv64_signed62, tptr t_secp256k1_modinv64_modinfo ]
    PROP (Z.Odd m;
          0 <= x < m;
          1 < m < 2^256;
          x = 0 \/ rel_prime x m;
          writable_share shx;
          readable_share sh_modinfo)
    PARAMS (ptrx; modinfo)
    SEP (signed62_at shx ptrx x;
         modinfo_at sh_modinfo modinfo m)
  POST [ tvoid ]
    EX rv : Z,
    PROP (is_modular_inverse x m rv)
    RETURN ()
    SEP (signed62_at shx ptrx rv;
         modinfo_at sh_modinfo modinfo m).


(* ================================================================= *)
(** ** The module's funspec list -- the two public safegcd drivers. *)

Definition Gprog_modinv_public : funspecs := [
  spec_secp256k1_modinv64_var;
  spec_secp256k1_modinv64
].
