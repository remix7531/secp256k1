(** * contract.jacobi: PUBLIC funspec for [secp256k1_jacobi64_maybe_var]. *)
(** Copyright (C) 2026 remix7531
    SPDX-License-Identifier: MIT *)

(** The public [src/modinv64.h] Jacobi-symbol entry point.  This is original
    work (NOT part of the BlockstreamResearch/simplicity modinv port), so it
    lives in its own file rather than the MIT-ported [contract/modinv.v].

    The function computes the Jacobi symbol [(x | m)] of a coprime input in
    variable time via the safegcd posdivsteps; being "maybe", it may return [0]
    ("unknown") if it does not converge within its iteration cap.  The model is
    [model.modinv.jacobi_symbol].  No body proof is included, and the function
    is deliberately not part of the audited [verified_surface]. *)

Require Import VST.floyd.proofauto.
Require Import secp256k1.vst.base.
Require Import secp256k1.contract.helper.structs_modinv.
Require Import secp256k1.model.modinv.
Require Import secp256k1.contract.helper.signed62.
Require Import secp256k1.contract.util.

Opaque Z.shiftr Z.pow.

(* ================================================================= *)
(** ** Jacobi funspec -- [secp256k1_jacobi64_maybe_var]. *)

(** [secp256k1_jacobi64_maybe_var x modinfo]: returns the Jacobi symbol
    [(x | m)] in [{-1, 1}], or [0] if the variable-time iteration does not
    converge within its cap ("maybe").  [*x] is read-only (copied into locals).
    Preconditions mirror the [_var] driver: [m] odd, [1 < m < 2^256],
    [0 <= x < m], and [x] coprime to [m] (the Jacobi symbol of a coprime input
    is +/-1).  The result is pinned to [jacobi_symbol x m] whenever it is
    nonzero. *)
Definition spec_secp256k1_jacobi64_maybe_var : ident * funspec :=
  DECLARE _secp256k1_jacobi64_maybe_var
  WITH x : Z, m : Z, ptrx : val, modinfo : val,
       shx : share, sh_modinfo : share, sh_debruijn : share, gv : globals
  PRE [ tptr t_secp256k1_modinv64_signed62, tptr t_secp256k1_modinv64_modinfo ]
    PROP (Z.Odd m;
          0 <= x < m;
          1 < m < 2^256;
          rel_prime x m;
          readable_share shx;
          readable_share sh_modinfo;
          readable_share sh_debruijn)
    PARAMS (ptrx; modinfo)
    GLOBALS (gv)
    SEP (signed62_at shx ptrx x;
         modinfo_at sh_modinfo modinfo m;
         debruijn64_array sh_debruijn gv)
  POST [ tint ]
    EX rv : Z,
    PROP (rv = -1 \/ rv = 0 \/ rv = 1;
          rv <> 0 -> rv = jacobi_symbol x m)
    RETURN (Vint (Int.repr rv))
    SEP (signed62_at shx ptrx x;
         modinfo_at sh_modinfo modinfo m;
         debruijn64_array sh_debruijn gv).
