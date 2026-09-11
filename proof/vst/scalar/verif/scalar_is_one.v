(** * Verif_scalar_is_one: Proof of body_secp256k1_scalar_is_one *)
(** Copyright (C) 2026 remix7531
    SPDX-License-Identifier: MIT *)

Require Import secp256k1.vst.base.
Require Import secp256k1.vst.helper.notations.
Require Import secp256k1.vst.gprog.
Require Import secp256k1.vst.tactics.core.
Require Import secp256k1.vst.tactics.int128.
Require Import secp256k1.vst.tactics.scalar.

(* ================================================================= *)
(** ** secp256k1_scalar_is_one -- [a = 1]. *)

(** The C body returns [((a->d[0] ^ 1) | a->d[1] | a->d[2] | a->d[3]) == 0].
    After loading the four limbs and the return, the postcondition is a pure
    equality between the [Int64] OR-cascade test and the spec's
    [if Z.eq_dec (scalar_val a) 1 then 1 else 0].

    The argument: the cascade is [Int64.zero] iff each disjunct is zero, i.e.
    [xor d0 1 = 0] (so [d0 = 1]) and [d1 = d2 = d3 = 0]; by the 4-limb
    decomposition of [scalar_val a < 2^256] that is exactly [scalar_val a = 1]. *)
Lemma body_secp256k1_scalar_is_one:
  semax_body Vprog Gprog
    f_secp256k1_scalar_is_one spec_secp256k1_scalar_is_one.
Proof.
  start_function.

  (* ===== Stage 1: walk the C body ===== *)

  forward. (* _t'1 = a->d[0] *)
  forward. (* _t'2 = a->d[1] *)
  forward. (* _t'3 = a->d[2] *)
  forward. (* _t'4 = a->d[3] *)
  forward. (* return ((t'1 ^ 1) | t'2 | t'3 | t'4) == 0 *)

  (* ===== Stage 2: reduce to the pure Int64/Z postcondition ===== *)

  entailer!.
  unfold scalar_to_val; rewrite ?Znth_cons, ?Znth_0_cons; simpl.
  change (Int.signed (Int.repr 1)) with 1.
  change (Int.signed (Int.repr 0)) with 0.
  fold_limb.
  f_equal.
  f_equal.

  (* ===== Stage 3: name the four limbs with their ranges ===== *)

  set (d0 := limb (2^64) a 0).
  set (d1 := limb (2^64) a 1).
  set (d2 := limb (2^64) a 2).
  set (d3 := limb (2^64) a 3).
  assert (Hd0 : 0 <= d0 < 2^64) by apply limb_u64_lt.
  assert (Hd1 : 0 <= d1 < 2^64) by apply limb_u64_lt.
  assert (Hd2 : 0 <= d2 < 2^64) by apply limb_u64_lt.
  assert (Hd3 : 0 <= d3 < 2^64) by apply limb_u64_lt.

  (* ===== Stage 4: bitwise building blocks ===== *)

  (* the bitwise zero-test lemmas live in [tactics.core]
     ([int64_repr_eq_zero_iff] / [int64_or_eq_zero_iff] /
     [int64_xor_repr_eq_zero_iff]), shared with [scalar_is_zero] and
     [scalar_eq]. *)
  (* An in-range [Int64.repr] is zero iff the underlying Z is zero. *)
  pose proof int64_repr_eq_zero_iff as Hzi.
  (* An [Int64.or] is zero iff both operands are zero. *)
  pose proof int64_or_eq_zero_iff as Hor.
  (* [xor d0 1] is zero iff [d0 = 1] (the [y = 1] instance). *)
  pose proof (int64_xor_repr_eq_zero_iff d0 1 Hd0 ltac:(lia)) as Hxor.

  (* ===== Stage 5: the 4-limb decomposition of scalar_val a ===== *)

  assert (Harange : 0 <= scalar_val a < 2^256)
    by (pose proof (scalar_range a); unfold secp256k1_N in *; lia).
  assert (Hdecomp : scalar_val a = d0 + d1 * 2^64 + d2 * 2^128 + d3 * 2^192).
  {
    pose proof (eval4_limbs (2^64) (scalar_val a) ltac:(lia)
                  ltac:(change (2^256) with ((2^64)^4) in Harange; lia)) as He.
    unfold eval4 in He.
    subst d0 d1 d2 d3.
    change ((2^64)^2) with (2^128) in He.
    change ((2^64)^3) with (2^192) in He.
    symmetry.
    exact He.
  }

  (* ===== Stage 6: assemble the master equivalence ===== *)

  (* [scalar_val a = 1] iff the limbs are [1,0,0,0]. *)
  assert (Hziff : scalar_val a = 1 <-> d0 = 1 /\ d1 = 0 /\ d2 = 0 /\ d3 = 0).
  {
    split.
    - rewrite Hdecomp.
      intro Hq.
      lia.
    - intros (E0 & E1 & E2 & E3).
      rewrite Hdecomp, E0, E1, E2, E3.
      lia.
  }
  (* The whole cascade is [Int64.zero] iff [scalar_val a = 1]. *)
  assert (Hbig : Int64.or (Int64.or (Int64.or
                   (Int64.xor (Int64.repr d0) (Int64.repr 1))
                   (Int64.repr d1)) (Int64.repr d2)) (Int64.repr d3)
                 = Int64.zero <-> scalar_val a = 1).
  {
    rewrite !Hor, Hxor, (Hzi d1 Hd1), (Hzi d2 Hd2), (Hzi d3 Hd3), Hziff.
    tauto.
  }

  (* ===== Stage 7: case-split the boolean test against the spec ===== *)

  change (Int64.repr 0) with Int64.zero.
  set (big := Int64.or (Int64.or (Int64.or
                (Int64.xor (Int64.repr d0) (Int64.repr 1))
                (Int64.repr d1)) (Int64.repr d2)) (Int64.repr d3)) in *.
  pose proof (Int64.eq_spec big Int64.zero) as Hsp.
  destruct (Int64.eq big Int64.zero) eqn:E.
  - (* branch: the cascade is Int64.zero *)
    destruct (Z.eq_dec a 1) as [Ha|Ha].
    + (* branch: a = 1 -- both sides are 1 *)
      simpl Z.b2z.
      reflexivity.
    + (* branch: big = zero but a <> 1: Hbig forces a = 1 *)
      simpl Z.b2z.
      exfalso.
      apply Hbig in Hsp.
      contradiction.
  - (* branch: the cascade is not Int64.zero *)
    destruct (Z.eq_dec a 1) as [Ha|Ha].
    + (* branch: big <> zero but a = 1: Hbig forces big = zero *)
      simpl Z.b2z.
      exfalso.
      apply Hbig in Ha.
      contradiction.
    + (* branch: a <> 1 -- both sides are 0 *)
      simpl Z.b2z.
      reflexivity.
Qed.
