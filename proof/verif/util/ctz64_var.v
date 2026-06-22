(** * verif.util.ctz64_var: body proof for secp256k1_ctz64_var. *)
(** Copyright (C) 2026 remix7531
    Ported from BlockstreamResearch/simplicity Coq/C/secp256k1/verif_modinv64_impl.v
    (commit c1dddedd), Copyright (c) 2018 Blockstream, originally MIT.
    Upstream notice reproduced in proof/README.md.
    SPDX-License-Identifier: MIT *)

(** Split out from the upstream-ported verif_modinv64_impl.v (one semax_body
    per file, per the project convention). *)

Require Import secp256k1.vst.base.
Require Import secp256k1.contract.util.
Require Import secp256k1.contract.gprog.util.
Require Import secp256k1.theory.extra_math.
Require Import secp256k1.theory.modinv.divsteps.theory.
Require Import secp256k1.theory.modinv.divsteps.bound724.
Require Import secp256k1.theory.modinv.construction.inverse.
Require secp256k1.theory.modinv.construction.divstep.
Require Import secp256k1.tactics.hygiene.

(** [secp256k1_ctz64_var(a)] returns the number of trailing zero bits of [a]
    ([Z_ctz a]). [VERIFY_CHECK(a != 0)] excludes the undefined [a = 0] input;
    with no compiler ctz builtin available it dispatches to the de Bruijn fallback. *)
Lemma body_secp256k1_ctz64_var: semax_body Vprog Gprog f_secp256k1_ctz64_var spec_secp256k1_ctz64_var.
Proof.
  start_function.

  (* ===== return secp256k1_ctz64_var_debruijn(a) ===== *)

  (* secp256k1_ctz64_var_debruijn(a) -- VERIFY-off: the VERIFY_CHECK(a != 0)
     abort branch is not in the AST. *)
  forward_call.

  (* return zeros *)
  forward.
Qed.
