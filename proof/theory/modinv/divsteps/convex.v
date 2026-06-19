(** * theory.modinv.divsteps.convex: the convex-hull membership predicate [in_convex_hull]. *)
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
Require Import secp256k1.theory.modinv.divsteps.orient.
Require Import secp256k1.theory.modinv.divsteps.hull.

(* ================================================================= *)
(** ** The convex-hull membership predicate -- [in_convex_hull]. *)

(** [p] is [in_convex_hull s] when it is a nonnegative, weight-1 barycentric
    combination of points of the set [s].  [in_between p a b] is the same for
    the two-point set (a segment).  The lemmas below are the closure laws of
    that predicate: it is closed under [QQeq] / set equality / supersets, it
    respects singletons, and it is closed under convex averaging
    ([QQavg_in_convex_hull]) -- the workhorse of hull soundness. *)

Definition in_between p a b :=
 exists c, 0 <= c <= 1 /\ QQeq p (QQavg c a b).

Definition in_convex_hull (x : QQ) (s : DDSet.t) : Prop :=
exists l : list (Q * DD),
 (forall q p, In (q, p) l -> 0 <= q /\ DDSet.In p s) /\
 Qsum (map fst l) == 1 /\
 QQeq (Qcombine l) x.

(** The empty set has an empty hull. *)
Lemma in_convex_hull_Empty : forall {x}, ~in_convex_hull x DDSet.empty.
Proof.
  intros s [[|[q d]] [H0 [H1 [H2 H3]]]]; [discriminate|].
  destruct (H0 q d); auto with *.
  auto using (@DDSet.empty_spec d).
Qed.

(** Hull membership respects rational-pair equality of the point. *)
Lemma in_convex_hull_morph1 : forall p1 p2 s,
 QQeq p1 p2 ->
 in_convex_hull p1 s ->
 in_convex_hull p2 s.
Proof.
  intros p1 p2 s [Hp1 Hp2] [l Hl].
  exists l.
  split; try tauto.
  split; try tauto.
  unfold QQeq.
  rewrite <- Hp1, <- Hp2.
  fold (QQeq (Qcombine l) p1).
  tauto.
Qed.

(** Hull membership respects set equality of the support. *)
Lemma in_convex_hull_morph2 : forall p s1 s2,
 DDSet.eq s1 s2 ->
 in_convex_hull p s1 ->
 in_convex_hull p s2.
Proof.
  intros p s1 s2 Hs [l Hl].
  exists l.
  split; try tauto.
  intros a b H.
  destruct Hl as [Hl _].
  destruct (Hl a b H).
  split; try tauto.
  apply Hs.
  assumption.
Qed.

(** Every point of [s] lies in its own hull. *)
Lemma in_in_convex_hull : forall (p:DD) s,
 DDSet.In p s -> in_convex_hull p s.
Proof.
  intros p s Hp.
  exists ((1,p)::nil).
  split; [|split].
  * intros q0 p0 [Hqp|[]].
    injection Hqp; intros <- <-; clear Hqp.
    split; auto with *.
  * reflexivity.
  * unfold QQeq in *.
    simpl; split; ring.
Qed.

(** Hull membership is monotone in the support set. *)
Lemma in_convex_hull_subset : forall q s1 s2,
 DDSet.Subset s1 s2 -> in_convex_hull q s1 ->
 in_convex_hull q s2.
Proof.
  intros q s1 s2 Hs [l H].
  unfold DDSet.Subset in Hs.
  exists l; split; [|split]; firstorder.
Qed.

(** The hull of a singleton is that single point. *)
Lemma in_convex_hull_singleton : forall q (p:DD),
 in_convex_hull q (DDSet.add p DDSet.empty) ->
 QQeq q p.
Proof.
  intros q p [l [H0 [H1 H2]]].
  unfold QQeq.
  destruct H2 as [<- <-].
  setoid_replace (fst p:Q) with (1*(fst p)) by ring.
  setoid_replace (snd p:Q) with (1*(snd p)) by ring.
  rewrite <- H1; clear H1.
  induction l; simpl; [split; ring|].
  destruct IHl as [-> ->]; auto with *.
  specialize (H0 (fst a) (snd a) (or_introl (surjective_pairing a))).
  destruct H0 as [_ H0].
  apply DDSet.add_spec in H0.
  destruct H0 as [[H0 H1]|H0];
   [apply Deq_Q in H0, H1; rewrite H0, H1; split; ring|].
  apply DDSet.mem_spec in H0.
  discriminate.
Qed.

(** The hull is closed under convex averaging of two members. *)
Lemma QQavg_in_convex_hull : forall c p1 p2 s,
  0 <= c <= 1 ->
  in_convex_hull p1 s ->
  in_convex_hull p2 s ->
  in_convex_hull (QQavg c p1 p2) s.
Proof.
  intros c p1 p2 s Hc [l1 Hp1] [l2 Hp2].
  pose (f := fun c (x : Q * DD) => (c * fst x, snd x)).
  pose (l1' := map (f c) l1).
  pose (l2' := map (f (1-c)) l2).
  exists (l1' ++ l2').
  split; [|split].
  assert (Hc' : 0 <= 1 - c) by (apply -> Qle_minus_iff; tauto).
  * (* weights stay nonnegative and points stay in [s] *)
    intros q p Hqp.
    apply in_app_or in Hqp.
    destruct Hp1 as [Hp1 _].
    destruct Hp2 as [Hp2 _].
    destruct Hqp as [Hqp|Hqp]; split;
      apply in_map_iff in Hqp;
      destruct Hqp as [[x y] [Hx1 Hx2]];
      injection Hx1; intros <- <-;
      try apply Qmult_le_0_compat; firstorder.
  * (* the weights still sum to one *)
    destruct Hp1 as [_ [Hp1 _]].
    destruct Hp2 as [_ [Hp2 _]].
    rewrite map_app.
    unfold l1', l2'.
    rewrite !map_map.
    change (fun x => fst (f c x)) with (fun x : Q * DD => c * fst x).
    change (fun x => fst (f (1 - c) x)) with (fun x : Q * DD => (1 - c) * fst x).
    rewrite <- (map_map _ (Qmult (1-c))), <- map_map.
    rewrite Qsum_app, !Qsum_mult, Hp1, Hp2.
    ring.
  * (* the barycentre is the convex average *)
    unfold QQeq; simpl.
    destruct Hp1 as [_ [_ [<- <-]]].
    destruct Hp2 as [_ [_ [<- <-]]].
    destruct (Qcombine_app l1' l2') as [-> ->].
    simpl.
    destruct (Qcombine_scale c l1) as [-> ->].
    destruct (Qcombine_scale (1-c) l2) as [-> ->].
    fold (f c) (f (1-c)) l1' l2'.
    split; ring.
Qed.

(** [On_path p l]: [p] lies on the polyline through the points [l]. *)
Inductive On_path (p : QQ) : list DD -> Prop :=
| On_path_tl : forall a l, On_path p l -> On_path p (a::l)
| On_path_between : forall (a b : DD) l, in_between p (a:QQ) (b:QQ) -> On_path p (a::b::l).

(** [DDSet_from_list] is monotone under list inclusion. *)
Lemma incl_DDSet_from_list : forall l1 l2,
 incl l1 l2 ->
 DDSet.Subset (DDSet_from_list l1) (DDSet_from_list l2).
Proof.
  intros p l1 l2 H Hq.
  rewrite In_DDSet_from_list in *.
  destruct Hq as [r [Hqr Hr]].
  exists r; split; auto with *.
Qed.
