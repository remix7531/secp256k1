(** * theory.modinv.divsteps.hull: upper / lower hull construction and sortedness. *)
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

(* ================================================================= *)
(** ** Upper / lower hull construction and sortedness. *)

(** [make_upper] / [make_lower] fold the incremental gift-wrapping steps
    [add_upper_point] / [add_lower_point] over a point list; [convex_hull_alt]
    re-expresses [convex_hull] as those two folds over the reversed element
    list.  The remaining lemmas establish that both folds keep the sorted
    prefix ([SSorted_make_*]) and only shrink it ([incl_make_*]). *)

(** Set membership of [DDSet_from_list l] is (dyadic-)equality to some list
    element -- the reflection used throughout the hull-membership proofs. *)
Lemma In_DDSet_from_list : forall l (p : DD),
 DDSet.In p (DDSet_from_list l) <->
 exists q : DD, DDeq p q /\ In q l.
Proof.
  intros l p.
  unfold DDSet_from_list.
  rewrite <- fold_left_rev_right.
  transitivity (exists q :DD, DDeq p q /\ In q (rev l));
   [|split; intros [q Hq]; exists q; assert (H0 := in_rev l q); firstorder].
  change DDSet.elt with DD.
  induction (rev l); [|split].
  * (* base: the empty set has no members *)
    simpl; split; [|intros [q [Hq []]]].
    intros H.
    apply DDSet.empty_spec in H.
    elim H.
  * (* step, forward: membership of the added set *)
    intros Hp.
    apply DDSet.add_spec in Hp.
    destruct Hp as [Hp|Hp].
    - exists a.
      auto with *.
    - apply IHl0 in Hp.
      destruct Hp as [q [Hpq Hp]].
      exists q.
      auto with *.
  * (* step, backward: a witness lands in the added set *)
    intros [q [Hpq Hp]].
    apply DDSet.add_spec.
    destruct Hp as [->|Hp]; [left; assumption|right].
    apply IHl0.
    exists q.
    tauto.
Qed.

Definition make_upper l :=
  fold_right add_upper_point nil l.
Definition make_lower l :=
  fold_right add_lower_point nil l.

(** [convex_hull] as the concatenation of the two directed hull folds. *)
Definition convex_hull_alt : forall s,
 convex_hull s =
 DDSet_from_list (make_upper (rev (DDSet.elements s))
              ++ make_lower (rev (DDSet.elements s))).
Proof.
  intros s.
  unfold convex_hull.
  apply f_equal.
  rewrite !DDSet.fold_spec.
  rewrite <- !fold_left_rev_right.
  reflexivity.
Qed.

(* ----------------------------------------------------------------- *)
(** *** Head / residue decompositions of an incremental hull step. *)

(** Both [add_upper_point] and [add_lower_point] keep [a] as their head. *)
Lemma hd_add_upper_point : forall a l,
 add_upper_point a l = a :: tl (add_upper_point a l).
Proof.
  intros a l.
  induction l; [reflexivity|].
  simpl.
  destruct l as [|b l].
  * case (DDOrder.compare _ _); reflexivity.
  * case (orientation _ _ _); try reflexivity; apply IHl.
Qed.

Lemma hd_make_upper : forall l, hd null (make_upper l) = hd null l.
Proof.
  intros [|a l]; try reflexivity.
  simpl.
  rewrite hd_add_upper_point.
  reflexivity.
Qed.

Lemma hd_add_lower_point : forall a l,
  add_lower_point a l = a :: tl (add_lower_point a l).
Proof.
  intros a l.
  induction l; [reflexivity|].
  simpl.
  destruct l as [|b l].
  * case (DDOrder.compare _ _); reflexivity.
  * case (orientation _ _ _); try reflexivity; apply IHl.
Qed.

Lemma hd_make_lower : forall l, hd null (make_lower l) = hd null l.
Proof.
  intros [|a l]; try reflexivity.
  simpl.
  rewrite hd_add_lower_point.
  reflexivity.
Qed.

(** [add_upper_point_ris a l] / [add_lower_point_ris a l] are the residues: the
    points of [l] that survive inserting [a], so that [l] splits as residue
    ++ popped tail (proved by [tl_add*Point]). *)
Fixpoint add_upper_point_ris (p : DD) (l : list DD) : list DD :=
match l with
| [] => []
| q :: l0 => match l0 with
   | [] => match DDOrder.compare p q with
           | Eq => [q]
           | _ => []
           end
   | r :: _ => match orientation p q r with
                 | Gt => []
                 | _ => q :: add_upper_point_ris p l0
               end
   end
end.

Fixpoint add_lower_point_ris (p : DD) (l : list DD) : list DD :=
match l with
| [] => []
| q :: l0 => match l0 with
   | [] => match DDOrder.compare p q with
           | Eq => [q]
           | _ => []
           end
   | r :: _ => match orientation p q r with
                 | Lt => []
                 | _ => q :: add_lower_point_ris p l0
                 end
   end
end.

Lemma tl_add_upper_point : forall a l,
 l = add_upper_point_ris a l ++ tl (add_upper_point a l).
Proof.
  intros a.
  induction l; auto.
  simpl.
  destruct l as [|b l].
  * case (DDOrder.compare _ _); reflexivity.
  * case (orientation _ _ _); auto; cbn [app]; congruence.
Qed.

Lemma tl_add_lower_point : forall a l,
 l = add_lower_point_ris a l ++ tl (add_lower_point a l).
Proof.
  intros a.
  induction l; auto.
  simpl.
  destruct l as [|b l].
  * case (DDOrder.compare _ _); reflexivity.
  * case (orientation _ _ _); auto; cbn [app]; congruence.
Qed.

(* ----------------------------------------------------------------- *)
(** *** Sortedness is preserved by the hull folds. *)

(** A strongly-sorted concatenation splits into two strongly-sorted parts. *)
Lemma SSorted_app : forall A R (l1 l2 : list A),
 StronglySorted R (l1 ++ l2) ->
 StronglySorted R l1 /\ StronglySorted R l2.
Proof.
  intros A R l1 l2.
  induction l1; simpl; intros H.
  * split; auto; constructor.
  * inversion_clear H.
    destruct (IHl1 H0) as [Hl1 Hl2].
    split; try constructor; auto.
    apply Forall_app in H1.
    tauto.
Qed.

(** Reversing a sorted list sorts it under the reversed relation. *)
Lemma Sorted_rev : forall A R (l : list A),
 Sorted R l -> Sorted (fun x y => R y x) (rev l).
Proof.
  intros A R.
  set (R' := fun x y => _).
  assert (H : forall l l' a,
   Sorted R l -> Sorted R' l' -> HdRel R a l -> HdRel R' a l' ->
   Sorted R' (rev l ++ [a] ++ l')).
  { intros l.
    induction l; try constructor; auto.
    intros l' a0 Hl Hl' Hal Hal'.
    simpl.
    rewrite <- app_assoc.
    apply IHl.
    inversion_clear Hl; auto.
    constructor; auto.
    inversion_clear Hl; auto.
    constructor; inversion_clear Hal; auto. }
  intros [|a l] Hl; try constructor.
  simpl.
  inversion_clear Hl.
  apply H; try constructor; auto.
Qed.

(** [make_upper] returns a sublist of its input. *)
Lemma incl_make_upper : forall l,
 incl (make_upper l) l.
Proof.
  intros l.
  induction l; intros x Hx; auto.
  simpl in *.
  rewrite hd_add_upper_point in Hx.
  destruct Hx as [<-| Hx]; auto.
  right.
  apply IHl.
  rewrite (tl_add_upper_point a (make_upper l)).
  apply in_or_app.
  tauto.
Qed.

(** [make_lower] returns a sublist of its input. *)
Lemma incl_make_lower : forall l,
 incl (make_lower l) l.
Proof.
  intros l.
  induction l; intros x Hx; auto.
  simpl in *.
  rewrite hd_add_lower_point in Hx.
  destruct Hx as [<-| Hx]; auto.
  right.
  apply IHl.
  rewrite (tl_add_lower_point a (make_lower l)).
  apply in_or_app.
  tauto.
Qed.

(** [make_upper] preserves strong sortedness. *)
Lemma SSorted_make_upper : forall R l,
 StronglySorted R l ->
 StronglySorted R (make_upper l).
Proof.
  intros R l.
  induction l; auto.
  intros H.
  inversion_clear H.
  specialize (IHl H0).
  simpl.
  rewrite hd_add_upper_point.
  rewrite (tl_add_upper_point a) in IHl.
  apply SSorted_app in IHl.
  constructor; try tauto.
  eapply incl_Forall; [|apply H1].
  eapply incl_tran; [|apply incl_make_upper].
  rewrite (tl_add_upper_point a).
  auto with *.
Qed.

(** [make_lower] preserves strong sortedness. *)
Lemma SSorted_make_lower : forall R l,
 StronglySorted R l ->
 StronglySorted R (make_lower l).
Proof.
  intros R l.
  induction l; auto.
  intros H.
  inversion_clear H.
  specialize (IHl H0).
  simpl.
  rewrite hd_add_lower_point.
  rewrite (tl_add_lower_point a) in IHl.
  apply SSorted_app in IHl.
  constructor; try tauto.
  eapply incl_Forall; [|apply H1].
  eapply incl_tran; [|apply incl_make_lower].
  rewrite (tl_add_lower_point a).
  auto with *.
Qed.
