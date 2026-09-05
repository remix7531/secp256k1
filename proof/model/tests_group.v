(** * model.tests_group: known-answer checks for [model.group]. *)
(** Copyright (C) 2026 remix7531
    SPDX-License-Identifier: MIT *)

(** Executable sanity checks of [model/group.v] against independently known
    values, so a reviewer can see what the [Point] / [padd] / [pdouble] /
    [smul] model means before reading any VST proof.  Every check is a
    closed equation discharged by [vm_compute; reflexivity]; each names
    where its expected value comes from.  This file is VST-free (imports
    only [model.constants] and [model.group], which re-exports
    [model.field]) and carries no axioms.

    COST.  A field inversion ([fe_inv], one 256-bit [pow_mod] over Coq's
    bignum [Z], not primitive machine words) costs about 6 seconds under
    [vm_compute] on the reference machine, and [padd] / [pdouble] each need
    one.  Checks that stay within a handful of such calls live here; the
    generator's full-order scalar multiple ([secp256k1_N * G], and the GLV
    identity [pmul_lambda G = smul secp256k1_lambda G], both needing on the
    order of 380 point operations, i.e. tens of minutes) are OUT OF SCOPE for
    any [vm_compute] check and remain unverified. Checks that
    still cost a handful of seconds (small multiples of [G], the
    [lift_x_even] round trip) are in [model/tests_slow_group.v] instead. *)

From Stdlib Require Import ZArith.

Require Import secp256k1.model.constants.
Require Import secp256k1.model.group.

Open Scope Z_scope.

(* ================================================================= *)
(** ** The generator matches SEC2 -- [G_x] / [G_y] / [on_curve]. *)

(** [G]'s x coordinate, decimal (SEC2 "secp256k1" 2.4.1), transcribed
    independently of the hex literal [model.group] uses to define [G_x] --
    a decimal/hex digit-transcription error in either would show up here. *)
Lemma chk_G_x_dec :
  G_x = 55066263022277343669578718895168534326250603453777594175500187360389116729240.
Proof. vm_compute. reflexivity. Qed.

(** [G]'s y coordinate, decimal (SEC2 "secp256k1" 2.4.1), same independence
    argument as [chk_G_x_dec]. *)
Lemma chk_G_y_dec :
  G_y = 32670510020758816978083085130507043184471273380659243275938904335757337482424.
Proof. vm_compute. reflexivity. Qed.

(** [G] satisfies [y^2 = x^3 + 7 mod p] -- the [on_curve] predicate itself,
    re-derived here (rather than reused from [model.group]'s own
    [on_curve_G]) so the check is visible in this KAT file without a reader
    having to open [model/group.v].  Cheap: two multiplications and a [mod],
    no [pow_mod] loop. *)
Lemma chk_G_on_curve : on_curve G.
Proof. vm_compute. reflexivity. Qed.

(* ================================================================= *)
(** ** Free identities of [pneg] / [padd] -- no field inversion needed. *)

(** Negation is an involution: mirroring twice in the x-axis returns the
    original point.  Only [fe_negate] (a subtraction), never [fe_inv].
    Compared via [point_eqb], not [=]: [PAff]'s two [Fe] fields each carry a
    range PROOF, so two structurally-equal-VALUE points built through
    different [fe_negate] applications are only propositionally equal
    ([model.group]'s own [point_eqb_eq]), never [vm_compute]-convertible --
    the same reason [model.group]'s doc comment gives for [point_eqb]
    existing at all. *)
Lemma chk_pneg_involution : point_eqb (pneg (pneg G)) G = true.
Proof. vm_compute. reflexivity. Qed.

(** [G + (-G) = PInf]: the vertical-chord case of [padd] (equal x, opposite
    y) returns the identity directly, without ever computing a slope --
    the one [padd] case that costs no [fe_inv].  [PInf] carries no [Fe], so
    ordinary [=] (not [point_eqb]) is fine here. *)
Lemma chk_padd_G_negG : padd G (pneg G) = PInf.
Proof. vm_compute. reflexivity. Qed.

(* ================================================================= *)
(** ** The GLV endomorphism, field side -- [secp256k1_beta] cube root.

    [proof/model/tests.v]'s [chk_lambda_cube] already checks the SCALAR side
    ([lambda^3 = 1 mod n]); this is the FIELD-side counterpart the point-level
    identity [lambda_endo] rests on.  [model.group]'s own
    [beta_cube_root_unity] proves the same fact as one lemma over [Fe]; this
    restates it as a raw [Z] equation so it is visible without leaving this
    KAT file. *)

(** [beta^3 = 1 mod p] (transcribed from [src/field.h:69-72]). *)
Lemma chk_beta_cube_z : secp256k1_beta ^ 3 mod secp256k1_P = 1.
Proof. vm_compute. reflexivity. Qed.

(** [beta] is nontrivial: a trivial cube root would make the GLV split
    useless. *)
Lemma chk_beta_ne_1_z : secp256k1_beta <> 1.
Proof. unfold secp256k1_beta. discriminate. Qed.

(* ================================================================= *)
(** ** Parity -- [has_even_y]. *)

(** [G]'s y is even (SEC2: [G_y] ends in the hex digit [8]), matching
    BIP-340's convention that the generator itself has even y. *)
Lemma chk_has_even_y_G : has_even_y G = true.
Proof. vm_compute. reflexivity. Qed.

(** [-G] has odd y: [p] is odd and [G_y] is even, so [p - G_y] is odd.  Only
    a subtraction and a parity test, no [fe_inv]. *)
Lemma chk_has_even_y_negG : has_even_y (pneg G) = false.
Proof. vm_compute. reflexivity. Qed.
