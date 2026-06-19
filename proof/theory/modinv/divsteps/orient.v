(** * theory.modinv.divsteps.orient: dyadic-pair equality and the orientation determinant. *)
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
Require Import secp256k1.theory.modinv.divsteps.qq.

(* ================================================================= *)
(** ** Dyadic-pair equality and the orientation determinant. *)

(** [Deq] / [DDeq] are decidable equality on dyadic points, both reflecting
    into rational equality ([Deq_Q] / [DDeq_Q]).  [Qdet p1 p2 p3] is the signed
    area of the triangle [p1 p2 p3]; [orientation] (from [base]) is its sign,
    as proved by [orientation_det].  The rotation / duplication / opposite laws
    below are exactly the symmetries of that determinant. *)

Definition Deq (a b : D) : Prop := Dcompare a b = Eq.
Definition DDeq (a b : DD) : Prop :=
  Deq (fst a) (fst b) /\ Deq (snd a) (snd b).

(** [Deq] is dyadic equality reflected into rational equality. *)
Lemma Deq_Q : forall x y, Deq x y <-> x == y.
Proof.
  intros x y.
  unfold Deq.
  rewrite Dcompare_Q.
  symmetry.
  apply Qeq_alt.
Qed.

(** Componentwise dyadic equality implies rational-pair equality. *)
Lemma DDeq_Q : forall p q : DD, DDeq p q -> QQeq p q.
Proof.
  intros [x1 y1] [x2 y2] [Hfst Hsnd].
  rewrite Deq_Q in *.
  split; simpl in *; congruence.
Qed.

Module DD_as_OTF <: OrderedTypeFull := OT_to_Full DDOrder.

(* Opaque point -- a canonical default [DD] used as [hd] fallback. *)
Definition null : DD.
exact (0:D,0:D)%Z.
Qed.

(** Reverse dyadic order (used to sort hulls right-to-left). *)
Definition DDreverse x y := DDOrder.lt y x.

(** Signed area of the triangle [p1 p2 p3] over [Q]. *)
Definition Qdet (p1 p2 p3 : QQ) :=
let (x1, y1) := p1 in
let (x2, y2) := p2 in
let (x3, y3) := p3 in
 (x1 * y2 - y1 * x2) +
 (x2 * y3 - y2 * x3) +
 (x3 * y1 - y3 * x1).

(** Swapping the last two vertices negates the determinant. *)
Lemma Qdet_opp : forall p q r, - Qdet p q r == Qdet p r q.
Proof.
  intros [x1 y1] [x2 y2] [x3 y3].
  simpl.
  ring.
Qed.

(** [orientation] is the sign of [Qdet]: it compares the determinant to [0]. *)
Lemma orientation_det : forall p1 p2 p3,
orientation p1 p2 p3 = (Qdet p1 p2 p3 ?= 0).
Proof.
  intros [x1 y1] [x2 y2] [x3 y3].
  simpl.
  autorewrite with DQ.
  destruct Qcompare_spec with
    (x1 * y2 - y1 * x2 + (x2 * y3 - y2 * x3) + (x3 * y1 - y3 * x1)) 0.
  * (* determinant = 0 *)
    apply Qeq_alt.
    apply Qplus_inj_r with (-((y1 - y3) * (x2 - x3))).
    rewrite Qplus_opp_r.
    rewrite <- H.
    ring.
  * (* determinant < 0 *)
    apply -> Qlt_alt.
    apply Qplus_lt_l with (-((y1 - y3) * (x2 - x3))).
    rewrite Qplus_opp_r.
    eapply Qlt_compat; [|reflexivity|apply H].
    ring.
  * (* determinant > 0 *)
    apply -> Qgt_alt.
    apply <- Qlt_minus_iff.
    eapply Qlt_compat; [reflexivity| |apply H].
    ring.
Qed.

(** A degenerate triangle (repeated vertex) has zero orientation. *)
Lemma orientation_dup : forall p q, orientation p q q = Eq.
Proof.
  intros [x1 y1] [x2 y2].
  rewrite orientation_det, <- Qeq_alt.
  simpl.
  ring.
Qed.

(** Cyclic rotation of the vertices preserves orientation. *)
Lemma orientation_rot : forall p q r,
 orientation p q r = orientation r p q.
Proof.
  intros [x1 y1] [x2 y2] [x3 y3].
  rewrite !orientation_det.
  simpl.
  set (a := _ + _).
  set (b := _ + _).
  setoid_replace a with b; [reflexivity|].
  unfold a, b.
  ring.
Qed.

(** Swapping the last two vertices flips the orientation comparison. *)
Lemma orientation_opp : forall p q r, CompOpp (orientation p q r) = orientation p r q.
Proof.
  intros p q r.
  rewrite !orientation_det.
  rewrite <- Qdet_opp.
  generalize (Qdet p r q).
  clear p q r.
  intros x.
  rewrite Qcompare_antisym.
  destruct (Qcompare_spec x 0).
  * (* x = 0 *)
    apply Qeq_alt.
    rewrite H.
    ring.
  * (* x < 0 *)
    apply -> Qlt_alt.
    setoid_replace (-x) with (0 + - x) by ring.
    apply -> Qlt_minus_iff.
    assumption.
  * (* x > 0 *)
    apply -> Qgt_alt.
    apply Qlt_minus_iff.
    ring_simplify.
    assumption.
Qed.

(** [orientation] respects dyadic-pair equality in all three arguments. *)
Add Morphism orientation with signature DDOrder.eq ==> DDOrder.eq ==> DDOrder.eq ==> eq as orientation_morph.
intros [x1 y1] [x2 y2] [H12a H12b].
intros [x3 y3] [x4 y4] [H34a H34b].
intros [x5 y5] [x6 y6] [H56a H56b].
rewrite !orientation_det.
simpl.
apply Deq_Q in H12a,H12b,H34a,H34b,H56a,H56b.
rewrite H12a,H12b,H34a,H34b,H56a,H56b.
reflexivity.
Qed.
