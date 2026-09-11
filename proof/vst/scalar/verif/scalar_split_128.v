(** * Verif_scalar_split_128: Proof of body_secp256k1_scalar_split_128 *)
(** Copyright (C) 2026 remix7531
    SPDX-License-Identifier: MIT *)

Require Import secp256k1.vst.base.
Require Import secp256k1.vst.helper.notations.
Require Import secp256k1.vst.gprog.
Require Import secp256k1.vst.tactics.core.
Require Import secp256k1.vst.tactics.int128.
Require Import secp256k1.vst.tactics.scalar.

(* ================================================================= *)
(** ** secp256k1_scalar_split_128 -- [r1 = k mod 2^128, r2 = k / 2^128]. *)

(** The C copies [k]'s low two limbs into [r1] (zeroing limbs 2,3) and
    [k]'s high two limbs into [r2] (zeroing limbs 2,3).  The witnesses are
    [r1 = k mod 2^128] and [r2 = k / 2^128]; both lie in [[0, 2^128)], hence
    below [N], so each is a reduced scalar.  After the eight stores the
    postcondition reduces to two list equalities between an [upd_Znth] chain
    and [scalar_to_val] of the witness; each limb identity is a pure mod/div
    fact about splitting [k] at [2^128]. *)
Lemma body_secp256k1_scalar_split_128:
  semax_body Vprog Gprog
    f_secp256k1_scalar_split_128 spec_secp256k1_scalar_split_128.
Proof.
  start_function.

  (* ===== Walk the C: load k->d[i], store into r1/r2, zero high limbs ===== *)

  forward. (* _t'4 = k->d[0] *)
  forward. (* r1->d[0] = _t'4 *)
  forward. (* _t'3 = k->d[1] *)
  forward. (* r1->d[1] = _t'3 *)
  forward. (* r1->d[2] = 0 *)
  forward. (* r1->d[3] = 0 *)
  forward. (* _t'2 = k->d[2] *)
  forward. (* r2->d[0] = _t'2 *)
  forward. (* _t'1 = k->d[3] *)
  forward. (* r2->d[1] = _t'1 *)
  forward. (* r2->d[2] = 0 *)
  forward. (* r2->d[3] = 0 *)

  (* ===== Supply the witnesses: low/high halves of [k] are reduced ===== *)

  pose proof (scalar_range k) as Hk.
  assert (Hr1 : 0 <= k mod 2 ^ 128 < secp256k1_N) by
    (pose proof (Z.mod_pos_bound (scalar_val k) (2 ^ 128) ltac:(lia));
     unfold secp256k1_N in *; lia).
  assert (Hr2 : 0 <= k / 2 ^ 128 < secp256k1_N) by
    (split;
     [ apply Z.div_pos; lia
     | apply Z.div_lt_upper_bound; [lia | unfold secp256k1_N in *; lia] ]).
  Exists (mkScalar (k mod 2 ^ 128) Hr1) (mkScalar (k / 2 ^ 128) Hr2).
  entailer!.

  (* ===== Discharge the two limb-list equalities ===== *)

  apply sepcon_derives.

  (* r1 = k mod 2^128: limbs (k0, k1, 0, 0). *)
  - apply derives_refl'.
    f_equal.
    unfold scalar_to_val.
    cbn [scalar_val scalar_reduce].
    (* (k mod 2^128) mod 2^64 = k mod 2^64 *)
    assert (He0 : (k mod 2 ^ 128) mod 2 ^ 64 = k mod 2 ^ 64) by
      (symmetry; rewrite <- (Znumtheory.Zmod_div_mod (2 ^ 64) (2 ^ 128));
       try lia; exists (2 ^ 64); reflexivity).
    (* ((k mod 2^128) / 2^64) mod 2^64 = (k / 2^64) mod 2^64 *)
    assert (He1 : (k mod 2 ^ 128 / 2 ^ 64) mod 2 ^ 64 = (k / 2 ^ 64) mod 2 ^ 64).
    { change (2 ^ 128) with (2 ^ 64 * 2 ^ 64).
      rewrite Z.rem_mul_r by lia.
      rewrite Z.mul_comm.
      rewrite Z.div_add by lia.
      rewrite (Z.div_small (k mod 2 ^ 64)) by (apply Z.mod_pos_bound; lia).
      rewrite Z.add_0_l.
      rewrite Z.mod_mod by lia.
      reflexivity. }
    (* high limbs of [k mod 2^128] vanish (it is below 2^128) *)
    assert (He2 : (k mod 2 ^ 128 / 2 ^ 128) mod 2 ^ 64 = 0) by
      (rewrite (Z.div_small (k mod 2 ^ 128) (2 ^ 128)) by
         (apply Z.mod_pos_bound; lia); reflexivity).
    assert (He3 : (k mod 2 ^ 128 / 2 ^ 192) mod 2 ^ 64 = 0).
    { rewrite (Z.div_small (k mod 2 ^ 128) (2 ^ 192)).
      reflexivity.
      split.
      apply Z.mod_pos_bound; lia.
      eapply Z.lt_le_trans.
      apply Z.mod_pos_bound; lia.
      apply Z.pow_le_mono_r; lia. }
    rewrite He0, He1, He2, He3.
    list_solve.

  (* r2 = k / 2^128: limbs (k2, k3, 0, 0). *)
  - apply derives_refl'.
    f_equal.
    unfold scalar_to_val.
    cbn [scalar_val scalar_reduce].
    (* ((k / 2^128) / 2^64) mod 2^64 = (k / 2^192) mod 2^64 *)
    assert (Hf1 : (k / 2 ^ 128 / 2 ^ 64) mod 2 ^ 64 = (k / 2 ^ 192) mod 2 ^ 64) by
      (rewrite Z.div_div by lia; reflexivity).
    (* high limbs of [k / 2^128] vanish (k < 2^256) *)
    assert (Hf2 : (k / 2 ^ 128 / 2 ^ 128) mod 2 ^ 64 = 0).
    { rewrite Z.div_div by lia.
      change (2 ^ 128 * 2 ^ 128) with (2 ^ 256).
      rewrite (Z.div_small k (2 ^ 256)) by (unfold secp256k1_N in Hk; lia).
      reflexivity. }
    assert (Hf3 : (k / 2 ^ 128 / 2 ^ 192) mod 2 ^ 64 = 0).
    { rewrite Z.div_div by lia.
      change (2 ^ 128 * 2 ^ 192) with (2 ^ 320).
      rewrite (Z.div_small k (2 ^ 320)) by (unfold secp256k1_N in Hk; lia).
      reflexivity. }
    rewrite Hf1, Hf2, Hf3.
    list_solve.
Qed.
