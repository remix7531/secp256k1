(** * theory.scalar.glv: abstract pure-Z lemmas for the GLV lattice bounds

    Two reusable, word-size-independent facts behind the
    [secp256k1_scalar_split_lambda] 128-bit output bounds:

    - [mul_shift_doubled_error]: the round-half-up rounding error of the C
      [mul_shift_var] computation, [|2^s * c - p| <= 2^(s-1)].
    - [abs_lincomb_bound]: a linear-combination absolute bound, the common
      shape of Lemmas 1-4 of the GLV estimate.

    Both are pure [Z]; no model constants, no separation logic. *)
(** Copyright (C) 2026 remix7531
    SPDX-License-Identifier: MIT *)

From Stdlib Require Import ZArith.
From Stdlib Require Import Lia.

Open Scope Z_scope.

(* ================================================================= *)
(** ** Round-half-up error bound -- [round_bit_eq] / [mul_shift_doubled_error]. *)

(** The C [mul_shift_var] computes [c = p / 2^s + (p / 2^(s-1)) mod 2], i.e.
    round-half-up of [p / 2^s].  The round bit [(p / 2^(s-1)) mod 2] is exactly
    bit [s-1] of [p], i.e. [(p mod 2^s) / 2^(s-1)]. *)
Lemma round_bit_eq : forall p s,
  1 <= s ->
  0 <= p ->
  (p / 2 ^ (s - 1)) mod 2 = (p mod 2 ^ s) / 2 ^ (s - 1).
Proof.
  (* ===== Setup: name the half-window h = 2^(s-1) and split p mod 2^s ===== *)
  intros p s Hs Hp.
  set (h := 2 ^ (s - 1)).
  assert (Hh : 0 < h) by (apply Z.pow_pos_nonneg; lia).
  (* 2^s = 2 * h, so the window 2^s is two halves of size h *)
  assert (Hsh : 2 ^ s = 2 * h).
  { unfold h.
    replace s with (Z.succ (s - 1)) at 1 by lia.
    rewrite Z.pow_succ_r by lia.
    lia. }
  pose proof (Z.div_mod p (2 * h) ltac:(lia)) as Hdm.
  pose proof (Z.mod_pos_bound p (2 * h) ltac:(lia)) as Hrem.
  set (a := p / (2 * h)) in *.
  set (rem := p mod (2 * h)) in *.

  (* ===== Main: reduce (p / h) mod 2 to rem / h ===== *)
  rewrite Hsh.
  (* LHS: (p / h) mod 2 ; RHS: rem / h *)
  (* peel the high quotient out of p / h so the mod 2 cancels it *)
  assert (Hph : p / h = rem / h + a * 2).
  { rewrite Hdm at 1.
    replace (2 * h * a + rem) with (rem + (a * 2) * h) by ring.
    rewrite Z.div_add by lia.
    lia. }
  rewrite Hph.
  (* the + a*2 term vanishes under mod 2 *)
  rewrite Z_mod_plus_full.

  (* ===== Closeout: rem / h is in [0,2), so mod 2 is the identity ===== *)
  assert (Hrh : 0 <= rem / h < 2).
  { split.
    - apply Z.div_pos; lia.
    - apply Z.div_lt_upper_bound; lia. }
  rewrite Z.mod_small by lia.
  reflexivity.
Qed.

(** The doubled rounding error is bounded by [2^(s-1)].  This is the sole
    rounding fact the GLV bound needs. *)
Lemma mul_shift_doubled_error : forall p s,
  1 <= s ->
  0 <= p ->
  Z.abs (2 ^ s * (p / 2 ^ s + (p / 2 ^ (s - 1)) mod 2) - p) <= 2 ^ (s - 1).
Proof.
  (* ===== Setup: name h, q = p / 2^s, r = p mod 2^s; pull in the round bit ===== *)
  intros p s Hs Hp.
  set (h := 2 ^ (s - 1)).
  assert (Hh : 0 < h) by (apply Z.pow_pos_nonneg; lia).
  (* 2^s = 2 * h, as in [round_bit_eq] *)
  assert (Hsh : 2 ^ s = 2 * h).
  { unfold h.
    replace s with (Z.succ (s - 1)) at 1 by lia.
    rewrite Z.pow_succ_r by lia.
    lia. }
  pose proof (Z.div_mod p (2 ^ s) ltac:(lia)) as Hdm.
  pose proof (Z.mod_pos_bound p (2 ^ s) ltac:(lia)) as Hr.
  (* the round bit (p / 2^(s-1)) mod 2 equals r / h *)
  pose proof (round_bit_eq p s Hs Hp) as Hbit.
  set (q := p / 2 ^ s) in *.
  set (r := p mod 2 ^ s) in *.
  fold h in Hbit.

  (* ===== Main: rewrite the rounded error as 2*h*(r/h) - r ===== *)
  rewrite Hbit.
  (* goal: Z.abs (2^s * (q + r / h) - p) <= h *)
  assert (Hexp : 2 ^ s * (q + r / h) - p = 2 * h * (r / h) - r).
  { rewrite Hdm. rewrite Hsh. ring. }
  rewrite Hexp.

  (* ===== Closeout: r / h is 0 or 1; both cases close by lia ===== *)
  (* r is one full window below 2*h, so r / h is 0 or 1 *)
  assert (Hrh : 0 <= r / h < 2).
  { split.
    - apply Z.div_pos; lia.
    - apply Z.div_lt_upper_bound; lia. }
  pose proof (Z.div_mod r h ltac:(lia)) as Hrm.
  pose proof (Z.mod_pos_bound r h ltac:(lia)) as Hrmb.
  assert (Hd : r / h = 0 \/ r / h = 1) by lia.
  apply Z.abs_le.
  destruct Hd as [Hd | Hd]; rewrite Hd in *; lia.
Qed.

(* ================================================================= *)
(** ** Linear-combination absolute bound -- [abs_lincomb_bound]. *)

(** From [M * x = u * E1 + v * E2] with [M > 0] and [|Ei| <= ei], conclude
    [M * |x| <= |u| * e1 + |v| * e2].  This is the shape of Lemmas 1-4 of the
    GLV estimate (triangle inequality on a 2-term linear combination). *)
Lemma abs_lincomb_bound : forall M x u v E1 E2 e1 e2,
  0 < M ->
  M * x = u * E1 + v * E2 ->
  Z.abs E1 <= e1 ->
  Z.abs E2 <= e2 ->
  M * Z.abs x <= Z.abs u * e1 + Z.abs v * e2.
Proof.
  (* ===== Setup: move M inside the absolute value ===== *)
  intros M x u v E1 E2 e1 e2 HM Heq HE1 HE2.
  (* M >= 0, so M * |x| = |M * x| *)
  assert (HMx : M * Z.abs x = Z.abs (M * x)).
  { rewrite Z.abs_mul.
    rewrite (Z.abs_eq M) by lia.
    reflexivity. }

  (* ===== Main: substitute M*x = u*E1 + v*E2 and apply the triangle inequality ===== *)
  rewrite HMx, Heq.
  eapply Z.le_trans; [apply Z.abs_triangle | ].
  rewrite !Z.abs_mul.
  (* bound each term |u|*|Ei| <= |u|*ei separately *)
  apply Z.add_le_mono.
  - (* term 1: |u| * |E1| <= |u| * e1 *)
    apply Z.mul_le_mono_nonneg_l; [apply Z.abs_nonneg | exact HE1].
  - (* term 2: |v| * |E2| <= |v| * e2 *)
    apply Z.mul_le_mono_nonneg_l; [apply Z.abs_nonneg | exact HE2].
Qed.
