(** * Verif_u128_accum_mul_carry: Proof of body_secp256k1_u128_accum_mul_carry *)
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

(** The high limb of a 64x64 product is at most [2^64 - 2], so adding the
    low-limb carry to it cannot wrap. This is the fact behind the C
    [VERIFY_CHECK(hi != UINT64_MAX)]. *)
Lemma limb_mul_1_le : forall (a b : UInt64),
  limb (2^64) (u64_val a * u64_val b) 1 <= 2^64 - 2.
Proof.
  intros a b.
  rewrite <- limb_fold1.
  pose proof (mul_u64_hi_le (u64_val a) (u64_val b) ltac:(rep_lia) ltac:(rep_lia)).
  assert (0 <= u64_val a * u64_val b / 2^64).
  { apply Z.div_pos; [apply Z.mul_nonneg_nonneg; rep_lia | lia]. }
  rewrite Z.mod_small by lia.
  lia.
Qed.

(** The carry out of [x + y] past [2^128] is the carry out of the high limbs
    after they absorb the carry out of the low limbs. The bound on [y / 2^64]
    makes [limb (2^64) y 1] the whole high part of [y]. *)
Lemma u128_add_carry_out : forall x y,
  0 <= x < 2^128 -> 0 <= y -> y / 2^64 <= 2^64 - 2 ->
  (x + y) / 2^128 =
  (if limb (2^64) x 1 +
      (limb (2^64) y 1 +
       (if limb (2^64) x 0 + limb (2^64) y 0 <? Int64.modulus then 0 else 1))
      <? Int64.modulus
   then 0 else 1).
Proof.
  intros x y Hx Hy Hyhi.
  rewrite <- !limb_fold0, <- !limb_fold1.
  assert (Hxhi : 0 <= x / 2^64 < 2^64).
  { split.
    - apply Z.div_pos; lia.
    - apply Z.div_lt_upper_bound; lia. }
  assert (Hyhi0 : 0 <= y / 2^64) by (apply Z.div_pos; lia).
  assert (Hxlo : 0 <= x mod 2^64 < 2^64) by (apply Z.mod_pos_bound; lia).
  assert (Hylo : 0 <= y mod 2^64 < 2^64) by (apply Z.mod_pos_bound; lia).
  rewrite (Z.mod_small (x / 2^64)), (Z.mod_small (y / 2^64)) by lia.
  change (2^128) with (2^64 * 2^64).
  rewrite <- Z.div_div by lia.
  replace (x + y)
    with ((x / 2^64 + y / 2^64) * 2^64 + (x mod 2^64 + y mod 2^64))
    by (pose proof (Z.div_mod x (2^64) ltac:(lia));
        pose proof (Z.div_mod y (2^64) ltac:(lia)); lia).
  rewrite Z.div_add_l by lia.
  rewrite (div_pow64_bit (x mod 2^64 + y mod 2^64)) by lia.
  rewrite <- Z.add_assoc.
  apply div_pow64_bit.
  destruct (x mod 2^64 + y mod 2^64 <? Int64.modulus); lia.
Qed.

(* ================================================================= *)
(** ** secp256k1_u128_accum_mul_carry -- [r += a * b], returning the carry out. *)

Lemma body_secp256k1_u128_accum_mul_carry:
  semax_body Vprog Gprog
    f_secp256k1_u128_accum_mul_carry spec_secp256k1_u128_accum_mul_carry.
Proof.
  start_function.

  (* lo = secp256k1_umul128(a, b, &hi): forward_call also absorbs the
     [lo = _t'1] copy of the returned low limb. *)
  forward_call (a, b, v_hi, Tsh).
  Intros result.
  subst result.

  (* r->lo += lo *)
  forward. (* _t'8 = r->lo *)
  forward. (* r->lo = _t'8 + lo *)

  (* hi += r->lo < lo *)
  forward. (* _t'6 = hi *)
  forward. (* _t'7 = r->lo *)
  forward. (* hi = _t'6 + (_t'7 < lo) *)

  (* r->hi += hi *)
  forward. (* _t'4 = r->hi *)
  forward. (* _t'5 = hi *)
  forward. (* r->hi = _t'4 + _t'5 *)

  forward. (* _t'2 = r->hi *)
  forward. (* _t'3 = hi *)
  forward. (* return _t'2 < _t'3 *)

  Exists (mkUInt128 ((u128_val r + u64_val a * u64_val b) mod 2^128)
            (u128_mod_range (u128_val r + u64_val a * u64_val b)))
         ((u128_val r + u64_val a * u64_val b) / 2^128).
  entailer!.

  - (* ===== Postcondition PROP and RETURN ===== *)
    pose proof (u64_mul_bound a b) as Hmul.
    assert (Hmul0 : 0 <= u64_val a * u64_val b)
      by (apply Z.mul_nonneg_nonneg; rep_lia).
    cbn [u128_val].
    split; [|split].
    + (* the sum is below 2 * 2^128, so the carry is a bit *)
      assert (Hcarry : 0 <= (u128_val r + u64_val a * u64_val b) / 2^128 < 2).
      { split; [apply Z.div_pos | apply Z.div_lt_upper_bound]; rep_lia. }
      lia.
    + pose proof (Z.div_mod (u128_val r + u64_val a * u64_val b) (2^128) ltac:(lia)).
      lia.
    + (* return value: [r->hi < hi] is the carry out of the high limb *)
      fold_limb.
      pose proof (limb_mul_1_le a b) as Hp1.
      pose proof (limb_u64_range (u64_val a * u64_val b) 1) as Hp1r.
      rewrite (ltu_carry_b2z (limb (2^64) (u128_val r) 0)
                 (limb (2^64) (u64_val a * u64_val b) 0))
        by (pose proof (limb_u64_range (u128_val r) 0);
            pose proof (limb_u64_range (u64_val a * u64_val b) 0); rep_lia).
      rewrite Int.signed_repr by (destruct (_ <? _); rep_lia).
      rewrite (ltu_carry_b2z (limb (2^64) (u128_val r) 1))
        by (pose proof (limb_u64_range (u128_val r) 1);
            try destruct (_ <? _); rep_lia).
      rewrite <- u128_add_carry_out
        by (try apply mul_u64_hi_le; rep_lia).
      reflexivity.

  - (* ===== Postcondition SEP: C struct = uint128_to_val of the wrapped sum ===== *)
    apply derives_refl'.
    unfold uint128_to_val.
    simpl u128_val.
    fold_limb.
    rewrite limb_mod128_0, limb_mod128_1.
    do 3 f_equal.
    + (* conjunct 0: limb 0 (low word) *)
      apply Int64.eqm_samerepr.
      apply eqm_of_mod_eq.
      apply limb_add_0; [rep_lia | apply Z.mul_nonneg_nonneg; rep_lia].
    + (* conjunct 1: limb 1 (high word) *)
      apply Int64.eqm_samerepr.
      apply muladd_limb1; [rep_lia | apply Z.mul_nonneg_nonneg; rep_lia].
Qed.
