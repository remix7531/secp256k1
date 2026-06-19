(** * theory.modinv.construction.inverse: the constructive [mod_inv] (via Bezout). *)
(** Copyright (C) 2026 remix7531
    Ported from BlockstreamResearch/simplicity Coq/C/modinv.v
    (commit c1dddedd), Copyright (c) 2018 Blockstream, originally MIT.
    Upstream notice reproduced in proof/README.md.
    SPDX-License-Identifier: MIT *)

(** This is the REALIZATION side of the modular inverse: it defines [mod_inv] by
    the Bezout coefficient of the gcd and proves its number-theoretic properties
    ([mod_inv_zero], [mod_inv_mul_l] / [mod_inv_mul_r], [mod_inv_eqm], ...).
    This is what the verif/contract layers import when they need the safegcd
    construction; the caller-facing inverse property is stated inline in the
    public [secp256k1_scalar_inverse] funspec (no separate spec/bridge here).

    Adapted for Rocq 9.0 / VST 2.16 in this repository's layered proof tree. *)

Require Import ZArith.
Require Import Coq.ZArith.Znumtheory.
Require Import Lia.
Require Import secp256k1.theory.modinv.construction.bezout.

Open Scope Z_scope.
Arguments Z.add !x !y.
Arguments Z.sub !m !n.
Arguments Z.mul !x !y.

(* ================================================================= *)
(** ** Modular inverse -- [mod_inv]. *)

(** Modular inverse of [a] mod [b], via the Bezout coefficient of [gcd]. *)
Definition mod_inv a b := Z.modulo (u_bezout (Bezout_gcd (Z.modulo a b) b)) b.

(* ================================================================= *)
(** ** mod_inv correctness -- inverse / divisibility / uniqueness lemmas. *)

(** The inverse of [0] is [0]. *)
Lemma mod_inv_zero b : mod_inv 0 b = 0.
Proof.
  reflexivity.
Qed.

(** If [b] divides [a] then [a] has no inverse: [mod_inv a b = 0]. *)
Lemma mod_inv_divide a b : (b | a) -> mod_inv a b = 0.
Proof.
  intros Hba.
  unfold mod_inv.
  rewrite (Zdivide_mod _ _ Hba).
  apply (mod_inv_zero b).
Qed.

(** [mod_inv a b * a] is [gcd a b] modulo [b]. *)
Lemma mod_inv_mul_l a b : mod_inv a b * a mod b = Z.gcd a b mod b.
Proof.
  unfold mod_inv.
  destruct (Bezout_gcd (a mod b) b) as [u v Huv]; simpl.
  rewrite Zmult_mod_idemp_l, <- Zmult_mod_idemp_r.
  replace (u * (a mod b)) with (Z.gcd (a mod b) b + (- v) * b) by lia.
  destruct (Z.eq_dec b 0) as [->|Hb].
  * rewrite !Zmod_0_r; ring.
  * rewrite Z.gcd_mod, Z.gcd_comm by assumption.
    apply Z_mod_plus_full.
Qed.

(** [a * mod_inv a b] is [gcd a b] modulo [b] (commuted form). *)
Lemma mod_inv_mul_r a b : a * mod_inv a b mod b = Z.gcd a b mod b.
Proof.
  rewrite Z.mul_comm.
  apply mod_inv_mul_l.
Qed.

(** Any left inverse of [a] mod [b] is congruent to [mod_inv a b]. *)
Lemma mod_inv_mul_unique_l a b x : x * a mod b = 1 -> x mod b = mod_inv a b.
Proof.
  intros Hx.
  destruct (Z_dec' b 0) as [[Hb0|Hb0]| ->].
  * apply (Z.mod_neg_bound (x*a)) in Hb0.
    lia.
  * apply Zmod_divide_minus in Hx;[|assumption].
    destruct (Hx) as [c Hc].
    unfold mod_inv.
    symmetry.
    apply Zdivide_mod_minus;[apply Z.mod_pos_bound;assumption|].
    replace (u_bezout (Bezout_gcd (a mod b) b) - x mod b)
     with ((u_bezout (Bezout_gcd (a mod b) b) - x) + (x - x mod b)) by ring.
    apply Z.divide_add_r;[|apply Zmod_divide_minus;lia].
    destruct (Bezout_gcd (a mod b) b) as [u v Huv]; simpl.
    rewrite Z.gcd_mod, Zmod_eq in Huv by lia.
    assert (Hgcd : Z.gcd b a = 1).
    { apply Z.bezout_1_gcd.
      exists (-c); exists x.
      lia. }
    rewrite Hgcd in Huv.
    apply Z.gauss with a;[|lia].
    exists (-c - v + u*(a/b)).
    lia.
  * assert (Hmodinv := mod_inv_mul_r a 0).
    rewrite !Zmod_0_r, Z.gcd_0_r in *.
    rewrite Z.mul_comm in Hx.
    destruct (Z.mul_eq_1 _ _ Hx) as [->| ->];lia.
Qed.

(** Any right inverse of [a] mod [b] is congruent to [mod_inv a b]. *)
Lemma mod_inv_mul_unique_r a b x : a * x mod b = 1 -> x mod b = mod_inv a b.
Proof.
  rewrite Z.mul_comm.
  apply mod_inv_mul_unique_l.
Qed.

(** [mod_inv] respects congruence in its first argument. *)
Lemma mod_inv_eqm N a b : eqm N a b -> mod_inv a N = mod_inv b N.
Proof.
  intros Hab.
  unfold mod_inv.
  rewrite Hab.
  reflexivity.
Qed.

(* ================================================================= *)
(** ** Small-modulus inverses -- Hacker's Delight closed forms. *)

Transparent Z.shiftr Z.pow.

(** Hacker's Delight 5-bit Newton seed equals [mod_inv (-a) (2^4)]. *)
Lemma hackers_delight_a a : Z.Odd a ->
  Z.land (-(a + (Z.shiftl (Z.land (a + 1) 4)) 1)) (Z.ones 4) =  mod_inv (-a) (2^4).
Proof.
  rewrite <- Z.odd_spec.
  intros Hodd.
  rewrite Z.land_ones by lia.
  rewrite <- Z.sub_0_l, <- Zminus_mod_idemp_r, Z.sub_0_l.
  rewrite <- Zplus_mod_idemp_l.
  change (Z.land (a + 1) 4) with (Z.land (a + 1) (Z.land (Z.ones 4) 4)).
  rewrite Z.land_assoc, Z.land_ones by lia.
  rewrite <- (Zplus_mod_idemp_l a).
  unfold mod_inv.
  symmetry.
  rewrite <- Z.sub_0_l, <- Zminus_mod_idemp_r, Z.sub_0_l.
  assert (Ha : 0 <= a mod 2^4 < 2^4) by (apply Z.mod_pos_bound;lia).
  assert (Hodd0 : Z.odd (a mod 2 ^ 4) = true).
  - rewrite <- Z.bit0_odd in *|-*.
    rewrite <- Z.land_ones by lia.
    rewrite Z.land_spec, Hodd.
    reflexivity.
  - destruct (a mod 2^4) as [|b|b]; try discriminate; try lia.
    do 4 (destruct b; try reflexivity; try discriminate; try lia).
Qed.

(** Hacker's Delight 6-bit closed form equals [mod_inv (-a) (2^6)]. *)
Lemma hackers_delight_b a : Z.Odd a ->
  Z.land (a * (a * a - 2)) (Z.ones 6) =  mod_inv (-a) (2^6).
Proof.
  rewrite <- Z.odd_spec.
  intros Hodd.
  rewrite Z.land_ones by lia.
  rewrite <- Zmult_mod_idemp_l, <- Zmult_mod_idemp_r, <- Zminus_mod_idemp_l.
  rewrite <- (Zmult_mod_idemp_l a), <- (Zmult_mod_idemp_r a).
  rewrite Zminus_mod_idemp_l, Zmult_mod_idemp_r.
  unfold mod_inv.
  symmetry.
  rewrite <- Z.sub_0_l, <- Zminus_mod_idemp_r, Z.sub_0_l.
  assert (Ha : 0 <= a mod 2^6 < 2^6) by (apply Z.mod_pos_bound;lia).
  assert (Hodd0 : Z.odd (a mod 2 ^ 6) = true).
  - rewrite <- Z.bit0_odd in *|-*.
    rewrite <- Z.land_ones by lia.
    rewrite Z.land_spec, Hodd.
    reflexivity.
  - destruct (a mod 2^6) as [|b|b]; try discriminate; try lia.
    do 6 (destruct b; try reflexivity; try discriminate; try lia).
Qed.
