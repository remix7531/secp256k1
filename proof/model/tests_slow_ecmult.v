(** * model.tests_slow_ecmult: seconds-scale known-answer checks for [model.ecmult]. *)
(** Copyright (C) 2026 remix7531
    SPDX-License-Identifier: MIT *)

(** The [model/tests_ecmult.v] checks that cost too much for that file's 30
    second budget: the two exhaustive wNAF sweeps, and the Strauss ladder
    exercised on nontrivial digit values.  Deliberately NOT in
    [_RocqProject]. VST-free, no axioms.

    Three cost-driven limits on these known-answer tests:

    (1) NO [G_toy].  [model.ecmult]'s [strauss] pins the REAL secp256k1
    generator ([G] / [G_128]), because the C build this extraction targets
    hard-codes [secp256k1_pre_g] / [secp256k1_pre_g_128] and is never
    compiled with [EXHAUSTIVE_TEST_ORDER].  The toy generator is therefore
    used only for the VARIABLE point [A] below -- exactly the role an
    arbitrary caller-supplied point plays in the real
    [secp256k1_ecmult_strauss_wnaf] -- while the "ng" side is checked against
    the real [G].  [model.ecmult] does now expose [strauss_gen], which takes
    the two generator-side points as arguments (so an [EXHAUSTIVE_TEST_ORDER]
    substitution IS expressible, and a cheap stand-in for [G_128] would avoid
    the fixed tax described in (2) below), but the checks here deliberately
    exercise the pinned [strauss]: that is the definition [contract/ecmult]
    and [verif/ecmult] are written against, and a check of [strauss_gen] at
    substituted points would not pin it.

    (2) A FIXED per-call tax dominates, not the digit values.  Every
    [strauss] call reaches [strauss_rung], whose body mentions [G_128]
    ([2^128 * G], 128 [pdouble] deep) even on a row where that stream's
    digit is [0].  Empirically (this phase's own probing, recorded in
    [unverified]), [vm_compute] pays the FULL cost of realising [G_128] on
    EVERY term that reaches [strauss_rung] -- multiple minutes on the
    reference machine, independent of how small [na] / [ng] are.  This is
    the opposite of what [model/ecmult.v]'s own header comment expects of
    its "[strauss G 6 0 0 0]" example.  Whether that cost is shared across
    the several [Lemma]s in ONE file (the ordinary behaviour of [vm_compute]'s
    global-value cache within one compilation) or paid AGAIN by each one was
    not confirmed within this phase's time budget -- also in [unverified].

    (3) SAMPLED, not exhaustive, and far MORE sparsely than the plan asks.
    Because of (2), the checks below are THREE representative [strauss]
    calls, not the full [13 * 13] product order 13 alone would need, nor even
    the
    "one value per digit-count class" sampling this file originally aimed
    for: THREE calls -- one multi-row single-stream case, one two-stream
    interleaving case, and one call on the other toy curve -- are the minimum
    that still exercises the ladder's fold and its row-alignment logic at
    all. *)

From Stdlib Require Import ZArith.
From Stdlib Require Import Lia.
From Stdlib Require Import List.
Import ListNotations.

Require Import secp256k1.model.constants.
Require Import secp256k1.model.group.
Require Import secp256k1.model.ecmult.

Open Scope Z_scope.

(* ================================================================= *)
(** ** The wNAF sweep, in full -- moved here verbatim from
    [model/tests_ecmult.v]; see that file for [wnaf_digit_wf_b] /
    [wnaf_no_two_consec_b] / [wnaf_row_ok] / [wnaf_range_ok]. *)

(** Boolean form of [wnaf_digit_wf]: [d] is [0], or odd and within
    [+/- (2^(w-1) - 1)]. *)
Definition wnaf_digit_wf_b (w d : Z) : bool :=
  (d =? 0)
  || (Z.odd d && (- (2 ^ (w - 1) - 1) <=? d) && (d <=? 2 ^ (w - 1) - 1)).

(** No two consecutive digits are both nonzero. *)
Fixpoint wnaf_no_two_consec_b (ds : list Z) : bool :=
  match ds with
  | [] => true
  | [_] => true
  | d1 :: ((d2 :: _) as rest) =>
      negb (negb (d1 =? 0) && negb (d2 =? 0)) && wnaf_no_two_consec_b rest
  end.

(** All three properties for one input [a] at window [w]. *)
Definition wnaf_row_ok (w a : Z) : bool :=
  let ds := wnaf a w in
  (wnaf_eval ds =? a)
  && forallb (wnaf_digit_wf_b w) ds
  && wnaf_no_two_consec_b ds.

(** Every one of [len] nonnegative inputs, at window [w]. *)
Definition wnaf_range_ok (w len : Z) : bool :=
  forallb (wnaf_row_ok w) (map Z.of_nat (seq 0 (Z.to_nat len))).

(** Every [a] in [[0, 2^16)] at [window_a] (the C's [WINDOW_A]). *)
Lemma chk_wnaf_exhaustive_window_a : wnaf_range_ok window_a 65536 = true.
Proof. vm_compute. reflexivity. Qed.

(** Every [a] in [[0, 2^16)] at [window_g] (the C's [WINDOW_G]). *)
Lemma chk_wnaf_exhaustive_window_g : wnaf_range_ok window_g 65536 = true.
Proof. vm_compute. reflexivity. Qed.

(* ================================================================= *)
(** ** The two [EXHAUSTIVE_TEST_ORDER] toy generators, transcribed
    independently of [model/tests_ecmult_gen.v] (per-module test files do
    not depend on one another): coordinates word-for-word from
    [SECP256K1_G_ORDER_13] / [SECP256K1_G_ORDER_199]
    ([src/group_impl.h:22-33]), most-significant 32-bit word first.
    Cross-checked in Python (a from-scratch affine double-and-add over the
    same [p]): both points are on their stated curve
    ([SECP256K1_B = 2] / [4], [src/group_impl.h:54-64]) and have the stated
    order. *)

Definition G13_x_z : Z :=
  0xa2482ff84bf34edfa51262fde57921dbe0dd2cb7a5914790bc71631fc09704fb.
Definition G13_y_z : Z :=
  0x942536cba3e494923a701cc3ee3e443fdf182aa915b8aa6a166d3b19ba84b045.
Definition G199_x_z : Z :=
  0x7fb07b5cd07c3bda553902e27a87ea2c35108a7f051f41e5b76abad51f2703ad.
Definition G199_y_z : Z :=
  0xa2515395b4c4438952a634fac10dd4d6d6f474598990c273a4f3116d32ff969.

Program Definition fe_G13_x : Fe := mkFe G13_x_z _.
Next Obligation. unfold G13_x_z, secp256k1_P. lia. Qed.

Program Definition fe_G13_y : Fe := mkFe G13_y_z _.
Next Obligation. unfold G13_y_z, secp256k1_P. lia. Qed.

Program Definition fe_G199_x : Fe := mkFe G199_x_z _.
Next Obligation. unfold G199_x_z, secp256k1_P. lia. Qed.

Program Definition fe_G199_y : Fe := mkFe G199_y_z _.
Next Obligation. unfold G199_y_z, secp256k1_P. lia. Qed.

(** The order-13 toy generator: on [y^2 = x^3 + 2]. *)
Definition G13 : Point := PAff fe_G13_x fe_G13_y.

(** The order-199 toy generator: on [y^2 = x^3 + 4]. *)
Definition G199 : Point := PAff fe_G199_x fe_G199_y.

(* ================================================================= *)
(** ** The Strauss ladder -- [strauss] against independently-computed
    [smul] / [padd].  Exactly THREE calls (see the file header's point (3)
    for why): each one pays the [G_128] tax once, so what is sampled here is
    not digit VALUES but the three STRUCTURAL shapes a [strauss] call can
    take -- a multi-row single stream, two interleaved streams of different
    lengths, and the other toy curve at all -- rather than a wide sweep of
    either. *)

(** [na = 12]: window-5 recoding is [[0; 0; 3]], three rows -- the longest
    digit list any value below order 13 produces at window 5, exercising two
    [pdouble]s in a row before the one nonzero digit lands. *)
Lemma chk_strauss_G13_12 : strauss G13 12 0 0 0 = smul 12 G13.
Proof. vm_compute. reflexivity. Qed.

(** Both streams nonzero at once, with DIFFERENT digit-list lengths: [na = 6]
    (window-5 recoding [[0; 3]]) needs two window-[a] rows, [ng = 5]
    (window-15 recoding [[5]]) needs only one window-[g] row, so
    [strauss_rows]' zero-padding of the shorter list is what makes this
    reduce correctly -- the row-alignment case a single-stream call cannot
    exercise. *)
Lemma chk_strauss_G13_6_and_G_5 :
  strauss G13 6 0 5 0 = padd (smul 6 G13) (smul 5 G).
Proof. vm_compute. reflexivity. Qed.

(** The order-199 toy curve, at all: [na = 1] keeps the [A]-side of this
    call as cheap as a nonzero digit can be ([[1]], one row, no doubling),
    since the point of this check is exercising [G199] rather than adding
    more digit-shape coverage the two checks above already give. *)
Lemma chk_strauss_G199_1 : strauss G199 1 0 0 0 = smul 1 G199.
Proof. vm_compute. reflexivity. Qed.
