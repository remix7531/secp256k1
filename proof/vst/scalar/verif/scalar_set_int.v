(** * Verif_scalar_set_int: Proof of body_secp256k1_scalar_set_int *)
(** Copyright (C) 2026 remix7531
    SPDX-License-Identifier: MIT *)

Require Import secp256k1.vst.base.
Require Import secp256k1.vst.helper.notations.
Require Import secp256k1.vst.gprog.
Require Import secp256k1.vst.tactics.core.
Require Import secp256k1.vst.tactics.int128.
Require Import secp256k1.vst.tactics.scalar.

(* ================================================================= *)
(** ** secp256k1_scalar_set_int -- [*r = v]. *)

(** The C writes [v] to limb 0 and zeroes limbs 1..3.  Since [v < 2^32],
    the resulting value is exactly [v], so [v] is a reduced scalar.  After
    the four stores, the postcondition reduces to a list equality between
    the [upd_Znth] chain and [scalar_to_val v], where every high limb of
    [v] is zero. *)
Lemma body_secp256k1_scalar_set_int:
  semax_body Vprog Gprog
    f_secp256k1_scalar_set_int spec_secp256k1_scalar_set_int.
Proof.
  start_function.

  (* ===== Stage 0: store v and zero the high limbs ===== *)

  (* r->d[0] = v; r->d[1] = r->d[2] = r->d[3] = 0 *)
  forward.
  forward.
  forward.
  forward.

  (* ===== Stage 1: Postcondition ===== *)

  (* The stored value [v] is already a reduced scalar. *)
  assert (Hr : 0 <= v < secp256k1_N) by (unfold secp256k1_N; lia).
  Exists (mkScalar v Hr).
  entailer!.

  (* Collapse the upd_Znth chain to [scalar_to_val v]; high limbs vanish. *)
  apply derives_refl'.
  unfold scalar_to_val.
  cbn [scalar_val scalar_reduce].
  rewrite (Z.mod_small v (2^64)) by lia.
  rewrite (Z.div_small v (2^64)), (Z.div_small v (2^128)),
          (Z.div_small v (2^192)) by lia.
  rewrite !Zmod_0_l.
  list_solve.
Qed.
