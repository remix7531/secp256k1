(** * theory.modinv.divsteps.qq: rational point pairs -- sums, scaling, convex combinations. *)
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
Require Import secp256k1.theory.modinv.divsteps.hom.

(* ================================================================= *)
(** ** Rational pairs [QQ] -- sums, scaling, convex combinations. *)

(** A [QQ] is a point in the rational plane.  [Qsum] folds a list of scalars,
    [Qcombine] folds a weighted list of dyadic points into their (unnormalised)
    barycentre, and [QQavg c a b] is the convex combination [c*a + (1-c)*b].
    A dyadic point [DD] injects into [QQ] via the [inject_DD] coercion. *)

Definition QQ : Set := Q * Q.
Definition Qsum := fold_right Qplus 0.
Definition Qcombine :=
  fold_right (fun (qp : Q * DD) a =>
             (fst a + fst qp * fst (snd qp), snd a + fst qp * snd (snd qp)))
             (0,0).
Definition QQplus p1 p2 := (fst p1 + fst p2, snd p1 + snd p2).
Definition QQscale c p := (c * fst p, c * snd p).
Definition QQavg c p1 p2 := QQplus (QQscale c p1) (QQscale (1-c) p2).
Definition QQeq (p q : QQ) := fst p == fst q /\ snd p == snd q.
Definition inject_DD (p : DD) : QQ := (inject_D (fst p), inject_D (snd p)).
Coercion inject_DD : DD >-> QQ.

(** [QQeq] is symmetric (it is componentwise [Qeq]). *)
Lemma QQeq_sym : forall p q, QQeq p q -> QQeq q p.
Proof.
  intros p q [Hfst Hsnd].
  unfold QQeq.
  auto with *.
Qed.

(** [DQ]: rewrite [D] arithmetic/comparison through the [Q] homomorphism. *)
#[export] Hint Rewrite Dcompare_Q Dadd_Q Dmult_Q Dsub_Q : DQ.

(** [Qsum] distributes over list concatenation. *)
Lemma Qsum_app : forall l1 l2, Qsum (l1 ++ l2) == Qsum l1 + Qsum l2.
Proof.
  intros l1 l2.
  unfold Qsum.
  rewrite fold_right_app.
  generalize (fold_right Qplus 0 l2).
  intros q.
  induction l1; simpl; [ring|].
  rewrite IHl1.
  ring.
Qed.

(** A sum of nonnegative scalars is nonnegative. *)
Lemma Qsum_pos : forall l, (forall x, In x l -> 0 <= x) ->
 0 <= Qsum l.
Proof.
  induction l; simpl; auto with *.
  intros H.
  change 0 with (0 + 0).
  auto using Qplus_le_compat.
Qed.

(** [Qsum] commutes with scaling every element by a constant. *)
Lemma Qsum_mult : forall c l, Qsum (map (Qmult c) l) == c * Qsum l.
Proof.
  induction l; simpl; try rewrite IHl; ring.
Qed.

(** Scaling a point by [1] is the identity. *)
Lemma QQscale_1 : forall p, QQeq (QQscale 1 p) p.
Proof.
  intros p.
  split; simpl; ring.
Qed.

(** Two successive scalings compose to a single scaling by the product. *)
Lemma QQscale_mult : forall a b p,
  QQeq (QQscale a (QQscale b p)) (QQscale (a*b) p).
Proof.
  intros a b p.
  split; simpl; ring.
Qed.

(** [Qcombine] distributes over list concatenation (as a [QQplus]). *)
Lemma Qcombine_app : forall l1 l2,
  QQeq (Qcombine (l1 ++ l2))
       (QQplus (Qcombine l1) (Qcombine l2)).
Proof.
  intros l1 l2.
  unfold Qcombine.
  rewrite fold_right_app.
  set (f := fun qp a => _).
  generalize (fold_right f (0,0) l2).
  intros q.
  induction l1; simpl; [split; simpl; ring|].
  unfold QQeq.
  simpl.
  destruct IHl1 as [-> ->].
  simpl.
  split; ring.
Qed.

(** Scaling a combination equals combining the elementwise-scaled weights. *)
Lemma Qcombine_scale : forall c l,
  QQeq (QQscale c (Qcombine l)) (Qcombine (map (fun x => (c * fst x, snd x)) l)).
Proof.
  intros c l.
  unfold QQeq.
  simpl.
  induction l; [split; simpl; ring|].
  simpl.
  destruct IHl as [<- <-].
  split; ring.
Qed.
