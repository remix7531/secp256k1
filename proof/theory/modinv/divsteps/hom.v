(** * theory.modinv.divsteps.hom: the dyadic-rational -> rational homomorphism. *)
(** Copyright (C) 2026 remix7531
    Adapted from sipa/safegcd-bounds coq/divsteps/divsteps_convexhull.v
    (commit 06abb7f), Copyright (c) 2021 Blockstream, originally MIT.
    Upstream notice reproduced in proof/README.md.
    SPDX-License-Identifier: MIT *)

(** Integrated into this repository's layered proof tree (Rocq 9.0). *)

Require Import List.
Require Import QArith.
Require Import Qpower.
Require Import Orders.
Require Import Sorted.
Import ListNotations.

Require Import secp256k1.theory.modinv.divsteps.base.

(* ================================================================= *)
(** ** [D] -> [Q] homomorphism -- arithmetic and ordering carry to [Q]. *)

(** The [inject_D : D >-> Q] coercion is a ring homomorphism.  Each proof
    aligns the two dyadic exponents through [Dalign_lr], expands [inject_D],
    and discharges the residual identity over [Q].  These four rewrites are
    the building blocks of the [DQ] autorewrite database (see [qq]). *)

(** [Dadd] injects to rational addition. *)
Lemma Dadd_Q : forall x y, Dadd x y == x + y.
Proof.
  intros x y.
  unfold Dadd.
  assert (Hxy := Dalign_lr x y).
  destruct (Dalign x y) as [[xm ym] e].
  destruct Hxy as [<- <-].
  unfold inject_D.
  simpl.
  rewrite inject_Z_plus.
  ring.
Qed.

(** [Dsub] injects to rational subtraction. *)
Lemma Dsub_Q : forall x y, Dsub x y == x - y.
Proof.
  intros x y.
  unfold Dsub.
  assert (Hxy := Dalign_lr x y).
  destruct (Dalign x y) as [[xm ym] e].
  destruct Hxy as [<- <-].
  unfold inject_D, Z.sub.
  simpl.
  rewrite inject_Z_plus, inject_Z_opp.
  ring.
Qed.

(** [Dmult] injects to rational multiplication (exponents add). *)
Lemma Dmult_Q : forall x y, Dmult x y == x * y.
Proof.
  intros x y.
  unfold Dmult, inject_D.
  simpl.
  rewrite inject_Z_mult, Qpower_plus by discriminate.
  ring.
Qed.

(** [Dhalf] injects to division by two (predecessor exponent). *)
Lemma Dhalf_Q : forall x, Dhalf x == x / 2.
Proof.
  intros x.
  unfold Dhalf, inject_D, Z.pred.
  simpl.
  rewrite Qpower_plus, Qmult_assoc by discriminate.
  reflexivity.
Qed.

(** The boolean strict-less-than [Dltb] reflects the [Q] strict order. *)
Lemma Dltb_Q : forall x y, Dltb x y = true -> x < y.
Proof.
  intros a b.
  unfold Dltb, D_as_TTLT.leb, D_as_OrderedTypeAlt.compare.
  rewrite D_as_OrderedTypeAlt.compare_sym, Dcompare_Q, Qlt_alt.
  case (a ?= b);
    try discriminate;
    reflexivity.
Qed.
