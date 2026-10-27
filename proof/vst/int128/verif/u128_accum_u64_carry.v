(** * Verif_u128_accum_u64_carry: Proof of body_secp256k1_u128_accum_u64_carry *)
(** Copyright (C) 2026 remix7531
    SPDX-License-Identifier: MIT *)

Require Import secp256k1.vst.base.
Require Import secp256k1.vst.helper.notations.
Require Import secp256k1.vst.gprog.
Require Import secp256k1.vst.tactics.core.
Require Import secp256k1.vst.tactics.int128.

(* ================================================================= *)
(** ** Arithmetic helpers -- reduction mod [2^128] and the carry out. *)

Lemma u128_mod_range : forall x, 0 <= x mod 2^128 < 2^128.
Proof.
  intros x.
  apply Z.mod_pos_bound.
  lia.
Qed.

(** Reducing mod [2^128] leaves both 64-bit limbs unchanged. *)
Lemma limb_mod128_0 : forall x, limb (2^64) (x mod 2^128) 0 = limb (2^64) x 0.
Proof.
  intros x.
  rewrite <- !limb_fold0.
  apply Z.mod_mod_divide.
  exists (2^64).
  reflexivity.
Qed.

Lemma limb_mod128_1 : forall x, limb (2^64) (x mod 2^128) 1 = limb (2^64) x 1.
Proof.
  intros x.
  rewrite <- !limb_fold1.
  assert (Hsplit : x / 2^64 = x mod 2^128 / 2^64 + x / 2^128 * 2^64).
  { rewrite <- Z.div_add by lia.
    f_equal.
    pose proof (Z.div_mod x (2^128) ltac:(lia)).
    lia. }
  rewrite Hsplit.
  rewrite Z.mod_add by lia.
  reflexivity.
Qed.

(** Below [2 * 2^64] the quotient by [2^64] is the overflow bit, in the
    [<? Int64.modulus] form that [ltu_carry_b2z] produces. *)
Lemma div_pow64_bit : forall z,
  0 <= z < 2 * 2^64 -> z / 2^64 = if z <? Int64.modulus then 0 else 1.
Proof.
  intros z Hz.
  change Int64.modulus with (2^64).
  destruct (Z.ltb_spec z (2^64)) as [Hlt | Hge].
  - apply Z.div_small.
    lia.
  - symmetry.
    apply Z.div_unique with (r := z - 2^64); lia.
Qed.

(** The carry out of [x + y] past [2^128] is the carry out of the high limb
    after it absorbs the carry out of the low limb. *)
Lemma u128_u64_carry_out : forall x y,
  0 <= x < 2^128 -> 0 <= y < 2^64 ->
  (x + y) / 2^128 =
  (if limb (2^64) x 1 +
      (if limb (2^64) x 0 + y <? Int64.modulus then 0 else 1) <? Int64.modulus
   then 0 else 1).
Proof.
  intros x y Hx Hy.
  rewrite <- limb_fold0, <- limb_fold1.
  assert (Hhi : 0 <= x / 2^64 < 2^64).
  { split.
    - apply Z.div_pos; lia.
    - apply Z.div_lt_upper_bound; lia. }
  assert (Hlo : 0 <= x mod 2^64 < 2^64) by (apply Z.mod_pos_bound; lia).
  rewrite (Z.mod_small (x / 2^64)) by lia.
  change (2^128) with (2^64 * 2^64).
  rewrite <- Z.div_div by lia.
  replace (x + y) with (x / 2^64 * 2^64 + (x mod 2^64 + y))
    by (pose proof (Z.div_mod x (2^64) ltac:(lia)); lia).
  rewrite Z.div_add_l by lia.
  rewrite (div_pow64_bit (x mod 2^64 + y)) by lia.
  apply div_pow64_bit.
  destruct (x mod 2^64 + y <? Int64.modulus); lia.
Qed.

(* ================================================================= *)
(** ** secp256k1_u128_accum_u64_carry -- [r += a], returning the carry out. *)

Lemma body_secp256k1_u128_accum_u64_carry:
  semax_body Vprog Gprog
    f_secp256k1_u128_accum_u64_carry spec_secp256k1_u128_accum_u64_carry.
Proof.
  start_function.

  forward. (* t'4 = r->lo *)
  forward. (* r->lo = t'4 + a *)
  forward. (* t'3 = r->lo *)
  forward. (* c = (uint64_t)(t'3 < a) *)
  forward. (* t'2 = r->hi *)
  forward. (* r->hi = t'2 + c *)
  forward. (* t'1 = r->hi *)
  forward. (* return t'1 < c *)

  Exists (mkUInt128 ((u128_val r + u64_val a) mod 2^128)
            (u128_mod_range (u128_val r + u64_val a)))
         ((u128_val r + u64_val a) / 2^128).
  entailer!.

  - (* ===== Postcondition PROP and RETURN ===== *)
    cbn [u128_val].
    split; [|split].
    + (* the sum is below 2 * 2^128, so the carry is a bit *)
      assert (Hcarry : 0 <= (u128_val r + u64_val a) / 2^128 < 2).
      { split; [apply Z.div_pos | apply Z.div_lt_upper_bound]; rep_lia. }
      lia.
    + pose proof (Z.div_mod (u128_val r + u64_val a) (2^128) ltac:(lia)).
      lia.
    + (* return value: [r->hi < c] is the carry out of the high limb *)
      fold_limb.
      unfold Int64.cmpu.
      rewrite (ltu_carry_b2z (limb (2^64) (u128_val r) 0) (u64_val a))
        by (pose proof (limb_u64_range (u128_val r) 0); rep_lia).
      rewrite Int.signed_repr by (destruct (_ <? _); rep_lia).
      rewrite (ltu_carry_b2z (limb (2^64) (u128_val r) 1))
        by (pose proof (limb_u64_range (u128_val r) 1);
            try destruct (_ <? _); rep_lia).
      rewrite <- u128_u64_carry_out by rep_lia.
      reflexivity.

  - (* ===== Postcondition SEP: C struct = uint128_to_val of the wrapped sum ===== *)
    apply derives_refl'.
    unfold uint128_to_val.
    simpl u128_val.
    fold_limb.
    rewrite limb_mod128_0, limb_mod128_1.
    do 3 f_equal.
    + (* conjunct 0: lo limb *)
      apply Int64.eqm_samerepr.
      apply Int64.eqm_trans with
        (y := limb (2^64) (u128_val r) 0 + limb (2^64) (u64_val a) 0).
      * rewrite limb_u64_val_0.
        apply Int64.eqm_refl.
      * apply eqm_of_mod_eq.
        apply limb_add_0; rep_lia.
    + (* conjunct 1: hi limb *)
      apply Int64.eqm_samerepr.
      rewrite Int.signed_repr by (destruct (Int64.ltu _ _); simpl; rep_lia).
      rewrite ltu_carry_b2z
        by (pose proof (limb_u64_range (u128_val r) 0); rep_lia).
      apply Int64.eqm_trans with
        (y := limb (2^64) (u128_val r) 1 +
              (limb (2^64) (u64_val a) 1 +
               (if limb (2^64) (u128_val r) 0 + limb (2^64) (u64_val a) 0 <? 2^64
                then 0 else 1))).
      * rewrite limb_u64_val_0, limb_u64_val_1.
        unfold Int64.eqm.
        apply Zbits.eqmod_refl.
      * apply eqm_of_mod_eq.
        apply limb_add_1; rep_lia.
Qed.
