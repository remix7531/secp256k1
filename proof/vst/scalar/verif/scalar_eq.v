(** * Verif_scalar_eq: Proof of body_secp256k1_scalar_eq *)
(** Copyright (C) 2026 remix7531
    SPDX-License-Identifier: MIT *)

Require Import secp256k1.vst.base.
Require Import secp256k1.vst.helper.notations.
Require Import secp256k1.vst.gprog.
Require Import secp256k1.vst.tactics.core.
Require Import secp256k1.vst.tactics.int128.
Require Import secp256k1.vst.tactics.scalar.

(* ================================================================= *)
(** ** secp256k1_scalar_eq -- [a = b]. *)

(** The C body returns
    [((a->d[0] ^ b->d[0]) | (a->d[1] ^ b->d[1])
      | (a->d[2] ^ b->d[2]) | (a->d[3] ^ b->d[3])) == 0].
    After loading the eight limbs and the return, the postcondition is a
    pure equality between the [Int64] OR-cascade test and the spec's
    [if Z.eq_dec (scalar_val a) (scalar_val b) then 1 else 0].

    The argument: the cascade is [Int64.zero] iff each per-limb
    [xor (a_i) (b_i)] is zero, i.e. [a_i = b_i] for every limb; by the
    4-limb decomposition of two values [< 2^256] that is exactly
    [scalar_val a = scalar_val b]. *)
Lemma body_secp256k1_scalar_eq:
  semax_body Vprog Gprog
    f_secp256k1_scalar_eq spec_secp256k1_scalar_eq.
Proof.
  start_function.

  (* ===== Stage 1: walk the C body (eight limb loads, then return) ===== *)

  forward. (* _t'1 = a->d[0] *)
  forward. (* _t'5 = b->d[0] *)
  forward. (* _t'2 = a->d[1] *)
  forward. (* _t'6 = b->d[1] *)
  forward. (* _t'3 = a->d[2] *)
  forward. (* _t'7 = b->d[2] *)
  forward. (* _t'4 = a->d[3] *)
  forward. (* _t'8 = b->d[3] *)
  forward. (* return (cascade of per-limb xors) == 0 *)

  (* ===== Stage 2: reduce to the pure Int64/Z postcondition ===== *)

  entailer!.
  unfold scalar_to_val; rewrite ?Znth_cons, ?Znth_0_cons; simpl.
  change (Int.signed (Int.repr 0)) with 0.
  fold_limb.
  f_equal.
  f_equal.

  (* ===== Stage 3: name the eight limbs with their ranges ===== *)

  set (a0 := limb (2^64) a 0).
  set (a1 := limb (2^64) a 1).
  set (a2 := limb (2^64) a 2).
  set (a3 := limb (2^64) a 3).
  set (b0 := limb (2^64) b 0).
  set (b1 := limb (2^64) b 1).
  set (b2 := limb (2^64) b 2).
  set (b3 := limb (2^64) b 3).
  assert (Ha0 : 0 <= a0 < 2^64) by apply limb_u64_lt.
  assert (Ha1 : 0 <= a1 < 2^64) by apply limb_u64_lt.
  assert (Ha2 : 0 <= a2 < 2^64) by apply limb_u64_lt.
  assert (Ha3 : 0 <= a3 < 2^64) by apply limb_u64_lt.
  assert (Hb0 : 0 <= b0 < 2^64) by apply limb_u64_lt.
  assert (Hb1 : 0 <= b1 < 2^64) by apply limb_u64_lt.
  assert (Hb2 : 0 <= b2 < 2^64) by apply limb_u64_lt.
  assert (Hb3 : 0 <= b3 < 2^64) by apply limb_u64_lt.

  (* ===== Stage 4: bitwise building blocks ===== *)

  (* the bitwise zero-test lemmas live in [tactics.core]
     ([int64_or_eq_zero_iff] / [int64_xor_repr_eq_zero_iff]), shared with
     [scalar_is_zero] and [scalar_is_one]. *)
  (* An [Int64.or] is zero iff both operands are zero. *)
  pose proof int64_or_eq_zero_iff as Hor.
  (* [xor (repr x) (repr y)] is zero iff [x = y] for in-range limbs. *)
  pose proof int64_xor_repr_eq_zero_iff as Hxor2.

  (* ===== Stage 5: the 4-limb decomposition of both scalars ===== *)

  assert (Harange : 0 <= scalar_val a < 2^256)
    by (pose proof (scalar_range a); unfold secp256k1_N in *; lia).
  assert (Hbrange : 0 <= scalar_val b < 2^256)
    by (pose proof (scalar_range b); unfold secp256k1_N in *; lia).
  assert (Hdeca : scalar_val a = a0 + a1 * 2^64 + a2 * 2^128 + a3 * 2^192).
  {
    pose proof (eval4_limbs (2^64) (scalar_val a) ltac:(lia)
                  ltac:(change (2^256) with ((2^64)^4) in Harange; lia)) as He.
    unfold eval4 in He.
    subst a0 a1 a2 a3.
    change ((2^64)^2) with (2^128) in He.
    change ((2^64)^3) with (2^192) in He.
    symmetry.
    exact He.
  }
  assert (Hdecb : scalar_val b = b0 + b1 * 2^64 + b2 * 2^128 + b3 * 2^192).
  {
    pose proof (eval4_limbs (2^64) (scalar_val b) ltac:(lia)
                  ltac:(change (2^256) with ((2^64)^4) in Hbrange; lia)) as He.
    unfold eval4 in He.
    subst b0 b1 b2 b3.
    change ((2^64)^2) with (2^128) in He.
    change ((2^64)^3) with (2^192) in He.
    symmetry.
    exact He.
  }

  (* ===== Stage 6: assemble the master equivalence ===== *)

  (* [scalar_val a = scalar_val b] iff the four limb pairs agree. *)
  assert (Hziff : scalar_val a = scalar_val b <-> a0 = b0 /\ a1 = b1 /\ a2 = b2 /\ a3 = b3).
  {
    split.
    - rewrite Hdeca, Hdecb.
      intro Hq.
      lia.
    - intros (E0 & E1 & E2 & E3).
      rewrite Hdeca, Hdecb, E0, E1, E2, E3.
      lia.
  }
  (* The whole cascade is [Int64.zero] iff [scalar_val a = scalar_val b]. *)
  change (Int64.repr 0) with Int64.zero.
  assert (Hbig : Int64.or (Int64.or (Int64.or
                   (Int64.xor (Int64.repr a0) (Int64.repr b0))
                   (Int64.xor (Int64.repr a1) (Int64.repr b1)))
                   (Int64.xor (Int64.repr a2) (Int64.repr b2)))
                   (Int64.xor (Int64.repr a3) (Int64.repr b3))
                 = Int64.zero <-> scalar_val a = scalar_val b).
  {
    rewrite !Hor.
    rewrite (Hxor2 a0 b0 Ha0 Hb0).
    rewrite (Hxor2 a1 b1 Ha1 Hb1).
    rewrite (Hxor2 a2 b2 Ha2 Hb2).
    rewrite (Hxor2 a3 b3 Ha3 Hb3).
    rewrite Hziff.
    tauto.
  }

  (* ===== Stage 7: case-split the boolean test against the spec ===== *)

  set (big := Int64.or (Int64.or (Int64.or
                (Int64.xor (Int64.repr a0) (Int64.repr b0))
                (Int64.xor (Int64.repr a1) (Int64.repr b1)))
                (Int64.xor (Int64.repr a2) (Int64.repr b2)))
                (Int64.xor (Int64.repr a3) (Int64.repr b3))) in *.
  pose proof (Int64.eq_spec big Int64.zero) as Hsp.
  destruct (Int64.eq big Int64.zero) eqn:E.
  - (* branch: the cascade is Int64.zero *)
    destruct (Z.eq_dec a b) as [Hab|Hab].
    + (* branch: a = b -- both sides are 1 *)
      simpl Z.b2z.
      reflexivity.
    + (* branch: big = zero but a <> b: Hbig forces a = b *)
      simpl Z.b2z.
      exfalso.
      apply Hbig in Hsp.
      contradiction.
  - (* branch: the cascade is not Int64.zero *)
    destruct (Z.eq_dec a b) as [Hab|Hab].
    + (* branch: big <> zero but a = b: Hbig forces big = zero *)
      simpl Z.b2z.
      exfalso.
      apply Hbig in Hab.
      contradiction.
    + (* branch: a <> b -- both sides are 0 *)
      simpl Z.b2z.
      reflexivity.
Qed.
