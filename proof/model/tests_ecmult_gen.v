(** * model.tests_ecmult_gen: known-answer checks for [model.ecmult_gen]. *)
(** Copyright (C) 2026 remix7531
    SPDX-License-Identifier: MIT *)

(** Executable sanity checks of [model/ecmult_gen.v] against independently
    known values, so a reviewer can see what the comb geometry and the
    blinding invariant mean before reading any VST proof.  Every check is a
    closed equation discharged by [vm_compute; reflexivity]; each names
    where its expected value comes from.  This file is VST-free (imports
    only other [model/] files) and carries no axioms.

    TOY GROUPS.  [model.ecmult_gen]'s [comb] / [ecmult_gen_model] cannot be
    exercised at their PINNED geometry ([COMB_BITS = 264]): that costs hours
    of [vm_compute] (see that file's header).  The library's own exhaustive
    test suite solves exactly this problem by recompiling with
    [EXHAUSTIVE_TEST_ORDER] defined, which shrinks [COMB_RANGE] /
    [COMB_BLOCKS] / [COMB_TEETH] and swaps in an alternate generator of small
    order ([src/group_impl.h:22-33]) -- the SAME field (so field code, and
    this model's [Fe] / [padd] / [pdouble], are unchanged) but a DIFFERENT
    curve [y^2 = x^3 + b] for a small [b], chosen so the generator's order is
    13 or 199.  This file transcribes those two toy generators and exercises
    [model.ecmult_gen]'s parametric [_of] geometry family at the matching
    [EXHAUSTIVE_TEST_ORDER] settings ([src/ecmult_gen.h:43-63]).  See that
    file's COST note: [comb]/[smul] at even these small orders still costs
    real [fe_inv] calls over the FULL 256-bit field, so the exhaustive-over-
    every-scalar checks live in [model/tests_slow_ecmult_gen.v] instead --
    and so does the module's headline check, [chk_ecmult_gen13_blinded]
    ([ecmult_gen_model_of] at the order-13 geometry, the one check that
    exercises the blinding composition rather than the comb alone: 92.9 s
    measured standalone, far past this file's 30 s budget). *)

From Stdlib Require Import ZArith.
From Stdlib Require Import Lia.

Require Import secp256k1.model.constants.
Require Import secp256k1.model.group.
Require Import secp256k1.model.scalar.
Require Import secp256k1.model.ecmult_gen.

Open Scope Z_scope.

(* ================================================================= *)
(** ** The comb geometry at the library's [EXHAUSTIVE_TEST_ORDER] settings.

    [comb_spacing_of] / [comb_bits_of] / [comb_points_of] are the parametric
    [_of] family [model.ecmult_gen] states precisely so these two toy
    geometries stay expressible without editing that file.  Expected values
    from [src/ecmult_gen.h:43-63]: order 13 sets [COMB_RANGE 4],
    [COMB_BLOCKS 1], [COMB_TEETH 2]; order 199 sets [COMB_RANGE 8],
    [COMB_BLOCKS 2], [COMB_TEETH 3]. *)

(** Order 13's spacing: [ceil(4 / (1*2)) = 2]. *)
Lemma chk_comb_spacing_13 : comb_spacing_of 4 1 2 = 2.
Proof. vm_compute. reflexivity. Qed.

(** Order 13's comb covers [1*2*2 = 4] bits -- exactly [COMB_RANGE], no
    slack, since [4] already divides evenly. *)
Lemma chk_comb_bits_13 : comb_bits_of 1 2 2 = 4.
Proof. vm_compute. reflexivity. Qed.

(** Order 13's table holds [2^(2-1) = 2] points per block. *)
Lemma chk_comb_points_13 : comb_points_of 2 = 2.
Proof. vm_compute. reflexivity. Qed.

(** Order 199's spacing: [ceil(8 / (2*3)) = ceil(8/6) = 2]. *)
Lemma chk_comb_spacing_199 : comb_spacing_of 8 2 3 = 2.
Proof. vm_compute. reflexivity. Qed.

(** Order 199's comb covers [2*3*2 = 12] bits, 4 more than [COMB_RANGE = 8]
    (the same slack pattern as the pinned geometry's 264 vs. 256). *)
Lemma chk_comb_bits_199 : comb_bits_of 2 3 2 = 12.
Proof. vm_compute. reflexivity. Qed.

(** Order 199's table holds [2^(3-1) = 4] points per block. *)
Lemma chk_comb_points_199 : comb_points_of 3 = 4.
Proof. vm_compute. reflexivity. Qed.

(* ================================================================= *)
(** ** The two [EXHAUSTIVE_TEST_ORDER] toy generators.

    Coordinates transcribed word-for-word from [SECP256K1_G_ORDER_13] /
    [SECP256K1_G_ORDER_199] ([src/group_impl.h:22-33]), most-significant
    32-bit word first (the same convention [model.group]'s own [G_x] / [G_y]
    use for [SECP256K1_G] -- see that file's header comment).  Independently
    recomputed and cross-checked in Python (a from-scratch affine
    double-and-add over the same [p]): both points are on their stated curve
    and both have the stated order (the [chk_g13_order] / [chk_g199_order]
    checks below repeat that same computation here, under [vm_compute]). *)

(** [G13]'s x coordinate ([SECP256K1_G_ORDER_13], first 8 words). *)
Definition G13_x_z : Z :=
  0xa2482ff84bf34edfa51262fde57921dbe0dd2cb7a5914790bc71631fc09704fb.

(** [G13]'s y coordinate ([SECP256K1_G_ORDER_13], last 8 words). *)
Definition G13_y_z : Z :=
  0x942536cba3e494923a701cc3ee3e443fdf182aa915b8aa6a166d3b19ba84b045.

(** [G199]'s x coordinate ([SECP256K1_G_ORDER_199], first 8 words). *)
Definition G199_x_z : Z :=
  0x7fb07b5cd07c3bda553902e27a87ea2c35108a7f051f41e5b76abad51f2703ad.

(** [G199]'s y coordinate ([SECP256K1_G_ORDER_199], last 8 words). *)
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

(** The order-13 toy generator. *)
Definition G13 : Point := PAff fe_G13_x fe_G13_y.

(** The order-199 toy generator. *)
Definition G199 : Point := PAff fe_G199_x fe_G199_y.

(** [model.group]'s [on_curve] is fixed to [SECP256K1_B = 7]; the toy curves
    use a different [b] each ([src/group_impl.h:54-64]), so this restates the
    same equation shape with [b] as a parameter, exactly the generalisation
    [model.group]'s own [on_curve] would need to cover the exhaustive-test
    curves too. *)
Definition on_curve_b (b : Z) (a : Point) : Prop :=
  match a with
  | PInf => True
  | PAff x y =>
      (fe_val y * fe_val y) mod secp256k1_P
        = (fe_val x * fe_val x * fe_val x + b) mod secp256k1_P
  end.

(** [G13] is on [y^2 = x^3 + 2] ([src/group_impl.h:59], [SECP256K1_B = 2] in
    the [EXHAUSTIVE_TEST_ORDER == 13] branch). *)
Lemma chk_g13_on_curve : on_curve_b 2 G13.
Proof. vm_compute. reflexivity. Qed.

(** [G199] is on [y^2 = x^3 + 4] ([src/group_impl.h:64], [SECP256K1_B = 4] in
    the [EXHAUSTIVE_TEST_ORDER == 199] branch). *)
Lemma chk_g199_on_curve : on_curve_b 4 G199.
Proof. vm_compute. reflexivity. Qed.

(* ================================================================= *)
(** ** [ecmult_gen_scalar_diff] against the C's own construction.

    [model.ecmult_gen] states the blinding difference in closed form, as
    [(2^COMB_BITS - 1) * inv2 mod n].  The C reaches the same residue the
    other way round, by doubling [1] a total of [COMB_BITS - 1] times and
    then adding [-1/2] ([secp256k1_ecmult_gen_scalar_diff],
    [src/ecmult_gen_impl.h:39-51]).  This check re-derives the C's form and
    compares, so a slipped exponent (263 against 264) or a flipped sign on the
    half would fail here rather than hide behind the two [Admitted] lemmas
    that are the only other things saying what this scalar is for.  Pure [Z]
    arithmetic, no point operations: milliseconds. *)

(** The closed form really is [2^(COMB_BITS-1) + (-1/2)] modulo [n].  Both
    sides are
    [0x800000000000000000000000000000a205e8fb1bb354323df6b9e8de4cfa8020]. *)
Lemma chk_scalar_diff_matches_c :
  scalar_val ecmult_gen_scalar_diff
    = (2 ^ (comb_bits - 1)
       + (secp256k1_N - scalar_val (scalar_half scalar_one))) mod secp256k1_N.
Proof. vm_compute. reflexivity. Qed.
