(** * Verif_scalar_is_zero: Proof of body_secp256k1_scalar_is_zero *)
(** Copyright (C) 2026 remix7531
    SPDX-License-Identifier: MIT *)

Require Import secp256k1.vst.base.
Require Import secp256k1.contract.helper.notations.
Require Import secp256k1.contract.gprog.scalar.
Require Import secp256k1.tactics.core.
Require Import secp256k1.tactics.int128.
Require Import secp256k1.tactics.scalar.

(* ================================================================= *)
(** ** secp256k1_scalar_is_zero -- [a = 0]. *)

(** The C body returns [(a->d[0] | a->d[1] | a->d[2] | a->d[3]) == 0].
    After the four limb loads and the return, the postcondition is a
    pure equality between [Z.b2z (Int64.eq (OR of the four limb words)
    Int64.zero)] and the spec's [if scalar_val a = 0 then 1 else 0].

    The proof rests on one fact: the bitwise OR of the four 64-bit limbs
    is [Int64.zero] iff [scalar_val a = 0].  We assemble it from three
    pieces:
      - [Hor2]: [Int64.or x y = Int64.zero <-> x = 0 /\ y = 0] (bitwise);
      - [Hrepr0]: for a limb [v] in [[0, 2^64)], [Int64.repr v = 0 <-> v = 0];
      - [limbs4_zero_iff] (theory): all four base-[2^64] limbs of a value
        in [[0, 2^256)] are zero iff the value is zero. *)
Lemma body_secp256k1_scalar_is_zero:
  semax_body Vprog Gprog
    f_secp256k1_scalar_is_zero spec_secp256k1_scalar_is_zero.
Proof.
  start_function.

  (* ===== Walk the C body: four limb loads, then the return ===== *)

  forward. (* _t'1 = a->d[0] *)
  forward. (* _t'2 = a->d[1] *)
  forward. (* _t'3 = a->d[2] *)
  forward. (* _t'4 = a->d[3] *)
  forward. (* return (_t'1 | _t'2 | _t'3 | _t'4) == 0 *)

  (* ===== Reduce the return value to a pure Int64 equality ===== *)

  entailer!.
  unfold scalar_to_val, sem_or, sem_cast_i2l, sem_cast_pointer,
         both_long, sem_cast_i2i.
  simpl.
  change (Z.pow_pos 2 64) with (2 ^ 64) in *.
  change (Z.pow_pos 2 128) with (2 ^ 128) in *.
  change (Z.pow_pos 2 192) with (2 ^ 192) in *.
  change (Int.signed (Int.repr 0)) with 0 in *.
  fold (Z.div a (2 ^ 64)).
  fold (Z.div a (2 ^ 128)).
  fold (Z.div a (2 ^ 192)).

  (* ===== Helper 1: Int64.or is zero iff both operands are zero ===== *)
  (* the bitwise [or]/[repr] zero-test lemmas live in [tactics.core]
     ([int64_or_eq_zero_iff] / [int64_repr_eq_zero_iff]), shared with
     [scalar_is_one] and [scalar_eq]. *)
  pose proof int64_or_eq_zero_iff as Hor2.
  (* ===== Helper 2: a limb word is zero iff its Z value is zero ===== *)
  pose proof int64_repr_eq_zero_iff as Hrepr0.

  (* ===== Bounds: scalar_val a < N < 2^256, and each limb < 2^64 ===== *)

  assert (Ha256 : 0 <= a < 2 ^ 256).
  {
    pose proof (scalar_range a) as Hr.
    unfold secp256k1_N in Hr.
    lia.
  }
  assert (Hb0 : 0 <= a mod 2 ^ 64 < 2 ^ 64)
    by (apply Z.mod_pos_bound; lia).
  assert (Hb1 : 0 <= (a / 2 ^ 64) mod 2 ^ 64 < 2 ^ 64)
    by (apply Z.mod_pos_bound; lia).
  assert (Hb2 : 0 <= (a / 2 ^ 128) mod 2 ^ 64 < 2 ^ 64)
    by (apply Z.mod_pos_bound; lia).
  assert (Hb3 : 0 <= (a / 2 ^ 192) mod 2 ^ 64 < 2 ^ 64)
    by (apply Z.mod_pos_bound; lia).

  (* ===== Central fact: OR of the four limb words is zero iff a = 0 ===== *)

  assert (Hbig :
    Int64.or
      (Int64.or
         (Int64.or (Int64.repr (a mod 2 ^ 64))
            (Int64.repr ((a / 2 ^ 64) mod 2 ^ 64)))
         (Int64.repr ((a / 2 ^ 128) mod 2 ^ 64)))
      (Int64.repr ((a / 2 ^ 192) mod 2 ^ 64)) = Int64.zero
    <-> scalar_val a = 0).
  {
    (* Peel the OR tree to four [Int64.repr limb = 0] facts ... *)
    rewrite Hor2.
    rewrite Hor2.
    rewrite Hor2.
    rewrite (Hrepr0 _ Hb0).
    rewrite (Hrepr0 _ Hb1).
    rewrite (Hrepr0 _ Hb2).
    rewrite (Hrepr0 _ Hb3).
    (* ... then fold to base-2^64 limbs and apply the theory lemma. *)
    rewrite (limb_fold0 (scalar_val a)), (limb_fold1 (scalar_val a)),
            (limb_fold2 (scalar_val a)), (limb_fold3 (scalar_val a)).
    rewrite <- (limbs4_zero_iff (2 ^ 64) (scalar_val a)) by
      (first [ lia | change ((2 ^ 64) ^ 4) with (2 ^ 256); lia ]).
    tauto.
  }

  (* ===== Conclude by cases on whether a is zero ===== *)

  change (Int64.repr 0) with Int64.zero.
  destruct (Z.eq_dec a 0) as [Ha0 | Han0].
  - (* a = 0: the OR is zero, so the comparison is true *)
    rewrite (proj2 Hbig Ha0).
    rewrite Int64.eq_true.
    reflexivity.
  - (* a <> 0: the OR is nonzero, so the comparison is false *)
    assert (Hne :
      Int64.or
        (Int64.or
           (Int64.or (Int64.repr (a mod 2 ^ 64))
              (Int64.repr ((a / 2 ^ 64) mod 2 ^ 64)))
           (Int64.repr ((a / 2 ^ 128) mod 2 ^ 64)))
        (Int64.repr ((a / 2 ^ 192) mod 2 ^ 64)) <> Int64.zero).
    {
      intros Hc.
      apply Han0.
      apply Hbig.
      exact Hc.
    }
    rewrite (Int64.eq_false _ _ Hne).
    reflexivity.
Qed.
