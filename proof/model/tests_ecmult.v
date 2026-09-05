(** * model.tests_ecmult: known-answer checks for [model.ecmult]. *)
(** Copyright (C) 2026 remix7531
    SPDX-License-Identifier: MIT *)

(** Executable sanity checks of [model/ecmult.v] against independently known
    values, so a reviewer can see what the wNAF recoding and the single-point
    Strauss ladder mean before reading any VST proof.  Every check is a
    closed equation discharged by [vm_compute; reflexivity]; each names
    where its expected value comes from.  This file is VST-free (imports
    only [model/] files) and carries no axioms.

    COST.  [wnaf] / [wnaf_eval] are pure [Z] recursion, free at any single
    input -- but exhaustively over [2^16] inputs at each of the two window
    widths the C uses, that recursion measures well past a minute under
    [vm_compute] (in [model/tests_slow_ecmult.v] for that reason).  A FEW
    concrete [wnaf] values stay here instead, as a cheap illustration of the
    encoding the exhaustive sweep checks in full.

    Every [strauss] check, even a fully degenerate one like
    [strauss G 0 0 0 0], is ALSO seconds-scale, and for a reason worth
    recording precisely: [strauss]'s definition reaches [strauss_rung],
    which mentions [G_128] ([2^128 * G], 128 [pdouble] calls deep) in its
    body.  [vm_compute] realises [G_128] as part of evaluating ANY term that
    reaches [strauss_rung] -- even a call whose actual digits are all [0], so
    that [smul 0 G_128] never uses the value once computed.  (This is the
    opposite of what [model/ecmult.v]'s own header comment expects of the
    "[strauss G 6 0 0 0]" example; see this phase's [unverified] entry.)
    [ecmult_model], by contrast, never mentions [G_128], so its free cases
    ([na = ng = 0] and [na = 1, ng = 0]) stay here uncontaminated. *)

From Stdlib Require Import ZArith.
From Stdlib Require Import List.
Import ListNotations.

Require Import secp256k1.model.constants.
Require Import secp256k1.model.group.
Require Import secp256k1.model.ecmult.

Open Scope Z_scope.

(* ================================================================= *)
(** ** wNAF recoding, a few concrete values -- illustrating the encoding
    [model/tests_slow_ecmult.v]'s exhaustive sweep checks over the full
    [[0, 2^16)] range.  Little-endian: digit [i] carries weight [2^i]. *)

(** [6 = 0 + 3*2]: the low bit is even (digit [0]), the remaining [3] is a
    single legal window-5 digit. *)
Lemma chk_wnaf_6 : wnaf 6 window_a = 0 :: 3 :: nil.
Proof. vm_compute. reflexivity. Qed.

(** [11] alone is already a legal window-5 digit ([11 < 2^4 - 1 = 15]): one
    row, no doubling. *)
Lemma chk_wnaf_11 : wnaf 11 window_a = 11 :: nil.
Proof. vm_compute. reflexivity. Qed.

(** [12 = 0 + 0*2 + 3*4]: two even bits before the [3]. *)
Lemma chk_wnaf_12 : wnaf 12 window_a = 0 :: 0 :: 3 :: nil.
Proof. vm_compute. reflexivity. Qed.

(** At [window_g], the much larger digit range ([2^14 - 1 = 16383]) absorbs
    [5] into a single digit exactly as [window_a] would. *)
Lemma chk_wnaf_5_window_g : wnaf 5 window_g = 5 :: nil.
Proof. vm_compute. reflexivity. Qed.

(* ================================================================= *)
(** ** [ecmult_model] on its two zero-cost cases -- the postcondition
    [contract/ecmult]'s funspec states, checked directly (no [fe_inv]:
    [na = 0] needs no [padd] at all, and [na = 1] is [padd PInf G = G]). *)

Lemma chk_ecmult_model_zero : ecmult_model G 0 0 = PInf.
Proof. vm_compute. reflexivity. Qed.

Lemma chk_ecmult_model_one : ecmult_model G 1 0 = G.
Proof. vm_compute. reflexivity. Qed.
