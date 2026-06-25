(** * verif.modinv.impl.modinv64_signed62_assign: body proof for secp256k1_modinv64_signed62_assign. *)
(** Copyright (C) 2026 remix7531
    Ported from BlockstreamResearch/simplicity Coq/C/secp256k1/verif_modinv64_impl.v
    (commit c1dddedd), Copyright (c) 2018 Blockstream, originally MIT.
    Upstream notice reproduced in proof/README.md.
    SPDX-License-Identifier: MIT *)

(** Split out from the upstream-ported verif_modinv64_impl.v (one semax_body
    per file, per the project convention). *)

Require Import secp256k1.vst.base.
Require Import secp256k1.contract.impl.modinv.
Require Import secp256k1.contract.gprog.modinv.
Require Import secp256k1.theory.extra_math.
Require Import secp256k1.theory.modinv.divsteps.theory.
Require Import secp256k1.theory.modinv.divsteps.bound724.
Require Import secp256k1.theory.modinv.construction.inverse.
Require secp256k1.theory.modinv.construction.divstep.
Require Import secp256k1.tactics.hygiene.

(** [secp256k1_modinv64_signed62_assign(r, a)] copies the five 62-bit limbs of
    [*a] into [*r]; the modelled value [x] is preserved unchanged. *)
Lemma body_secp256k1_modinv64_signed62_assign: semax_body Vprog Gprog f_secp256k1_modinv64_signed62_assign spec_secp256k1_modinv64_signed62_assign.
Proof.
  start_function.

  (* The signed-62 representation has length 5 -- needed for the limb stores. *)
  assert (Hlenx := Signed62.reprn_Zlength 5 x).

  (* ===== r->v[i] = a->v[i] for i = 0..4 (five load/store pairs) ===== *)

  (* _t'5 = a->v[0] *)
  forward.
  (* r->v[0] = _t'5 *)
  forward.

  (* _t'4 = a->v[1] *)
  forward.
  (* r->v[1] = _t'4 *)
  forward.

  (* _t'3 = a->v[2] *)
  forward.
  (* r->v[2] = _t'3 *)
  forward.

  (* _t'2 = a->v[3] *)
  forward.
  (* r->v[3] = _t'2 *)
  forward.

  (* _t'1 = a->v[4] *)
  forward.
  (* r->v[4] = _t'1 *)
  forward.

  (* ===== Postcondition: the five stores rebuilt the limb list of [x] ===== *)
  entailer!!.
Qed.
