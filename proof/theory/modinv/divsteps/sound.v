(** * theory.modinv.divsteps.sound: points under / over a path -- hull soundness [convex_hull_sound]. *)
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
Require Import secp256k1.theory.modinv.divsteps.convex.

(* ================================================================= *)
(** ** Points under / over a path -- hull soundness ([convex_hull_sound]). *)

(** Any point on the polyline through [l] lies in the hull of [l]'s vertices. *)
Lemma on_path_convex : forall p l,
  On_path p l -> in_convex_hull p (DDSet_from_list l).
Proof.
  intros p l H.
  induction H.
  * eapply in_convex_hull_subset;[|apply IHOn_path].
    apply incl_DDSet_from_list.
    auto with *.
  * destruct H as [c [Hc Hp]].
    exists [(c,a);((1-c),b)];split;[intros q r [Hqr|[Hqr|[]]];injection Hqr; intros <- <-; clear Hqr|split].
    + split; try tauto.
      rewrite In_DDSet_from_list.
      exists a;repeat split;auto with *.
    + split;[apply -> Qle_minus_iff;tauto|].
      rewrite In_DDSet_from_list.
      exists b;repeat split;auto with *.
    + simpl;ring.
    + unfold QQeq;destruct Hp as [-> ->].
      simpl;split;ring.
Qed.

(* ----------------------------------------------------------------- *)
(** *** The upper hull lies weakly above every input point -- [under]. *)

(** [under p l]: some point of the path [l] sits directly above [p]
    (same abscissa, greater-or-equal ordinate). *)
Definition under p l := exists q, On_path q l /\ fst p == fst q /\ snd p <= snd q.

(** Every list element is [under] the list (unless the list is that singleton). *)
Lemma in_under : forall (p : DD) (l : list DD),
 In p l -> under (p:QQ) l \/ l = [p].
Proof.
  intros p l.
  induction l;try contradiction.
  intros [->|H].
  * destruct l;[right;reflexivity|].
    left.
    exists p; repeat split; auto with *.
    apply On_path_between.
    exists 1; repeat split;auto with *;simpl;ring.
  * left.
    specialize (IHl H).
    destruct IHl as [[q H0]| ->].
     exists q;split;[apply On_path_tl|]; tauto.
    exists p; repeat split; auto with *.
    apply On_path_between.
    exists 0; repeat split;auto with *;simpl;ring.
Qed.

(** The dyadic point order refines the abscissa order (weakly). *)
Lemma DDorder_fst : forall a b, DDOrder.lt a b -> fst a <= fst b.
Proof.
  intros a b H.
  rewrite Qle_lteq.
  destruct H as [H|[H _]];[left|right].
  * rewrite Qlt_alt, <- Dcompare_Q; auto.
  * rewrite Qeq_alt, <- Dcompare_Q; auto.
Qed.

(** At equal abscissa, the point order is the strict ordinate order. *)
Lemma DDorder_snd : forall a b, DDOrder.lt a b -> fst a == fst b -> snd a < snd b.
Proof.
  intros a b H H0.
  destruct H as [H|[H H']].
  * change (Dcompare (fst a) (fst b) = Lt) in H.
    rewrite Dcompare_Q, <- Qlt_alt in H.
    apply Qlt_not_eq in H.
    contradiction.
  * rewrite Qlt_alt, <- Dcompare_Q; auto.
Qed.

(** Inserting a point into the upper hull keeps every previously-[under]
    point [under]: the gift-wrapping step never lifts the hull off a point.
    The core case analyses whether [b] is popped and, if so, reconstructs the
    witness as a convex average of the surviving neighbours. *)
Lemma under_add_upper_point : forall p a l,
 StronglySorted DDreverse (a :: l) ->
 under p (a::l) -> under p (add_upper_point a l).
Proof.
  intros p a l.
  induction l.
  * intros Hsort [q [HPath [Hpq1 Hpq2]]].
    inversion_clear HPath;inversion H.
  * rename a0 into b.
    intros Hsort H.
    simpl.
    destruct l as [|c l].
     simpl.
     destruct (DDOrder.compare_spec a b); auto.
     inversion_clear Hsort.
     inversion_clear H2.
     change (DDOrder.lt b a) in H3.
     rewrite H0 in H3.
     destruct DDOrder.lt_strorder.
     elim (StrictOrder_Irreflexive b H3).
    compare (orientation a b c) Gt;[intros ->; auto|].
     intros Horient.
     cut (under p (add_upper_point a (c :: l))).
      intros;case (orientation a b c);try contradiction; auto.
     apply IHl.
      inversion_clear Hsort.
      inversion_clear H0.
      inversion_clear H1.
      constructor; auto.
     destruct H as [q [HPath [Hpq1 Hpq2]]].
       cut (under q (a :: c :: l)).
       intros [r [Hr [Heq1 Heq2]]].
       exists r;repeat split;auto;eauto with *.
      clear Hpq1 Hpq2 p IHl.
      change DD in a,b,c.
      assert (Hb : under (b:QQ) [a;c]).
       inversion_clear Hsort.
       inversion_clear H0.
       inversion_clear H2.
       clear H3.
       inversion_clear H.
       clear H2.
       inversion_clear H3.
       clear H2. 
       assert (Hac : fst c <= fst a).
        apply DDorder_fst.
        assumption.
       rewrite Qle_lteq in Hac.
       destruct Hac as [Hac|Hac].
       + rewrite Qlt_minus_iff in Hac.
         pose (d := ((fst b - fst c)/(fst a - fst c))).
         assert (Hd0 : 0 <= d).
          apply Qle_shift_div_l; auto.
          ring_simplify (0 * (fst a - fst c)).
          apply -> Qle_minus_iff.
          auto using DDorder_fst.
         assert (Hd1 : d <= 1).
          apply Qle_shift_div_r; auto.
          ring_simplify (1 * (fst a - fst c)).
          apply Qle_minus_iff.
          ring_simplify.
          apply -> Qle_minus_iff.
          auto using DDorder_fst.
         exists (QQavg d (a:QQ) (c:QQ)).
         simpl; repeat split.
           apply On_path_between.
           exists d;repeat split;auto.
          unfold d;field;auto with *.
         rewrite orientation_rot in Horient.
         destruct a as [a1 a2]; destruct b as [b1 b2]; destruct c as [c1 c2].
         unfold orientation in Horient.
         autorewrite with DQ in Horient.
         rewrite <- Qle_alt in Horient.
         simpl in *.
         setoid_replace (d * a2 + (1 - d) * c2) with (((b1 - c1)*a2 + (a1 - b1)*c2)/(a1 - c1)) 
           by (unfold d;field;auto with *).
         apply Qle_shift_div_l; auto with *.
         rewrite Qle_minus_iff in *.
         eapply Qle_trans;[apply Horient|].
         rewrite Qle_minus_iff.
         ring_simplify.
         auto with *.
       + exists a.
         split.
          apply On_path_between.
          exists 1;repeat split;simpl;auto with *; ring.
         assert (Hab : fst b == fst a).
          apply Qle_antisym.
           apply DDorder_fst; auto.
          rewrite <- Hac.
          apply DDorder_fst; auto.
         split;auto.
         apply Qlt_le_weak.
         apply DDorder_snd; auto.
    + destruct Hb as [r [Hr [Hr1 Hr2]]].
      inversion_clear Hr;[inversion_clear H; inversion_clear H0|].
      inversion_clear HPath;[inversion_clear H0|].
      - exists q;split;auto with *.
        apply On_path_tl; assumption.
      - destruct H as [x [Hx Hr]].
        destruct H1 as [y [Hy Hq]].
        exists (QQavg y (r:QQ) (c:QQ)); split;simpl.
          apply On_path_between.
          destruct Hx as [Hx0 Hx1].
          destruct Hy as [Hy0 Hy1].
          exists (x*y).
          unfold QQeq; simpl.
          destruct Hr as [-> ->]; simpl.
          repeat split; try ring; auto using Qmult_le_0_compat.
          rewrite Qle_lteq in Hx0.
          destruct Hx0 as [Hx0|<-];[|ring_simplify;auto with *].
          rewrite <- (Qmult_le_l _ _ x) in Hy1 by assumption.
          ring_simplify in Hy1.
          eauto with *.
         destruct Hq as [-> ->]; simpl.
         split;[rewrite Hr1;ring|].
         rewrite Qle_minus_iff in Hr2|-*.
         ring_simplify.
         setoid_replace (y * snd r + -1 * y * snd b) with (y * (snd r + - snd b)) by ring.
         destruct Hy;apply Qmult_le_0_compat; auto with *.
      - destruct H as [x [Hx Hr]].
        destruct H0 as [y [Hy Hq]].
        exists (QQavg y (a:QQ) (r:QQ)); split;simpl.
          apply On_path_between.
          destruct Hx as [Hx0 Hx1].
          destruct Hy as [Hy0 Hy1].
          exists (x + y*(1 - x)).
          unfold QQeq; simpl.
          destruct Hr as [-> ->]; simpl.
          repeat split; try ring.
           change 0 with (0 + 0).
           apply Qplus_le_compat; auto.
           apply Qmult_le_0_compat; auto.
           rewrite Qle_minus_iff in Hx1; auto.
          rewrite Qle_minus_iff.
          setoid_replace (1 + - (x + y * (1 - x))) with ((1 - x)*(1 - y)) by ring.
          rewrite Qle_minus_iff in Hx1, Hy1.
          apply Qmult_le_0_compat; auto.
         destruct Hq as [-> ->]; simpl.
         split;[rewrite Hr1;ring|].
         rewrite Qle_minus_iff in Hr2|-*.
         ring_simplify.
         setoid_replace (-1 * y * snd r + y * snd b + snd r + -1 * snd b) with ((1-y) * (snd r + - snd b)) by ring.
         destruct Hy as [Hy0 Hy1].
         rewrite Qle_minus_iff in Hy1.
         apply Qmult_le_0_compat; auto with *.
Qed.

(** Folding the whole upper-hull construction keeps every input point [under]
    the result (unless the input is the singleton [[p]]). *)
Lemma under_make_upper : forall (p:DD) l,
 StronglySorted DDreverse l ->
 In p l ->
 under (p:QQ) (make_upper l) \/ l = [p].
Proof.
  intros p.
  induction l; try contradiction.
  intros Hsort H.
  simpl.
  destruct l as [|b l].
   destruct H as [->|[]].
   right;reflexivity.
  left.
  apply under_add_upper_point.
   inversion_clear Hsort.
   constructor; auto using SSorted_make_upper.
   eapply incl_Forall;[|apply H1].
   apply incl_make_upper.
  destruct l as [|c l].
   simpl.
   apply in_under in H.
   destruct H;auto;discriminate.
  destruct H as [->|H].
   assert (H0 : In p (p :: make_upper (b :: c :: l))) by auto with *.
   apply in_under in H0.
   destruct H0 as [H0|H0];auto.
   simpl in H0.
   rewrite hd_add_upper_point in H0.
   discriminate.
  inversion_clear Hsort.
  specialize (IHl H0 H).
  destruct IHl as [[q Hq]|IHl];try discriminate.
  exists q;split;[apply On_path_tl|]; tauto.
Qed.

(* ----------------------------------------------------------------- *)
(** *** The lower hull lies weakly below every input point -- [over]. *)

(** [over p l]: some point of the path [l] sits directly below [p] (same
    abscissa, lesser-or-equal ordinate).  This is the mirror of [under]. *)
Definition over p l := exists q, On_path q l /\ fst p == fst q /\ snd q <= snd p.

(** Every list element is [over] the list (unless the list is that singleton). *)
Lemma in_over : forall (p : DD) (l : list DD),
 In p l -> over (p:QQ) l \/ l = [p].
Proof.
  intros p l.
  induction l;try contradiction.
  intros [->|H].
  * destruct l;[right;reflexivity|].
    left.
    exists p; repeat split; auto with *.
    apply On_path_between.
    exists 1; repeat split;auto with *;simpl;ring.
  * left.
    specialize (IHl H).
    destruct IHl as [[q H0]| ->].
     exists q;split;[apply On_path_tl|]; tauto.
    exists p; repeat split; auto with *.
    apply On_path_between.
    exists 0; repeat split;auto with *;simpl;ring.
Qed.

(** Mirror of [under_add_upper_point]: inserting a point into the lower hull
    keeps every previously-[over] point [over]. *)
Lemma over_add_lower_point : forall p a l,
 StronglySorted DDreverse (a :: l) ->
 over p (a::l) -> over p (add_lower_point a l).
Proof.
  intros p a l.
  induction l.
  * intros Hsort [q [HPath [Hpq1 Hpq2]]].
    inversion_clear HPath;inversion H.
  * rename a0 into b.
    intros Hsort H.
    simpl.
    destruct l as [|c l].
     simpl.
     destruct (DDOrder.compare_spec a b); auto.
     inversion_clear Hsort.
     inversion_clear H2.
     change (DDOrder.lt b a) in H3.
     rewrite H0 in H3.
     destruct DDOrder.lt_strorder.
     elim (StrictOrder_Irreflexive b H3).
    compare (orientation a b c) Lt;[intros ->; auto|].
     intros Horient.
     cut (over p (add_lower_point a (c :: l))).
      intros;case (orientation a b c);try contradiction; auto.
     apply IHl.
      inversion_clear Hsort.
      inversion_clear H0.
      inversion_clear H1.
      constructor; auto.
     destruct H as [q [HPath [Hpq1 Hpq2]]].
       cut (over q (a :: c :: l)).
       intros [r [Hr [Heq1 Heq2]]].
       exists r;repeat split;auto;eauto with *.
      clear Hpq1 Hpq2 p IHl.
      change DD in a,b,c.
      assert (Hb : over (b:QQ) [a;c]).
       inversion_clear Hsort.
       inversion_clear H0.
       inversion_clear H2.
       clear H3.
       inversion_clear H.
       clear H2.
       inversion_clear H3.
       clear H2. 
       assert (Hac : fst c <= fst a).
        apply DDorder_fst.
        assumption.
       rewrite Qle_lteq in Hac.
       destruct Hac as [Hac|Hac].
       + rewrite Qlt_minus_iff in Hac.
         pose (d := ((fst b - fst c)/(fst a - fst c))).
         assert (Hd0 : 0 <= d).
          apply Qle_shift_div_l; auto.
          ring_simplify (0 * (fst a - fst c)).
          apply -> Qle_minus_iff.
          auto using DDorder_fst.
         assert (Hd1 : d <= 1).
          apply Qle_shift_div_r; auto.
          ring_simplify (1 * (fst a - fst c)).
          apply Qle_minus_iff.
          ring_simplify.
          apply -> Qle_minus_iff.
          auto using DDorder_fst.
         exists (QQavg d (a:QQ) (c:QQ)).
         simpl; repeat split.
           apply On_path_between.
           exists d;repeat split;auto.
          unfold d;field;auto with *.
         rewrite orientation_rot in Horient.
         destruct a as [a1 a2]; destruct b as [b1 b2]; destruct c as [c1 c2].
         unfold orientation in Horient.
         autorewrite with DQ in Horient.
         rewrite <- Qge_alt in Horient.
         simpl in *.
         setoid_replace (d * a2 + (1 - d) * c2) with (((b1 - c1)*a2 + (a1 - b1)*c2)/(a1 - c1)) 
           by (unfold d;field;auto with *).
         apply Qle_shift_div_r; auto with *.
         rewrite Qle_minus_iff in *.
         eapply Qle_trans;[apply Horient|].
         rewrite Qle_minus_iff.
         ring_simplify.
         auto with *.
       + exists c.
         split.
          apply On_path_between.
          exists 0;repeat split;simpl;auto with *; ring.
         assert (Hab : fst c == fst b).
          apply Qle_antisym.
           apply DDorder_fst; auto.
          rewrite Hac.
          apply DDorder_fst; auto.
         split;auto with *.
         apply Qlt_le_weak.
         apply DDorder_snd; auto.
    + destruct Hb as [r [Hr [Hr1 Hr2]]].
      inversion_clear Hr;[inversion_clear H; inversion_clear H0|].
      inversion_clear HPath;[inversion_clear H0|].
      - exists q;split;auto with *.
        apply On_path_tl; assumption.
      - destruct H as [x [Hx Hr]].
        destruct H1 as [y [Hy Hq]].
        exists (QQavg y (r:QQ) (c:QQ)); split;simpl.
          apply On_path_between.
          destruct Hx as [Hx0 Hx1].
          destruct Hy as [Hy0 Hy1].
          exists (x*y).
          unfold QQeq; simpl.
          destruct Hr as [-> ->]; simpl.
          repeat split; try ring; auto using Qmult_le_0_compat.
          rewrite Qle_lteq in Hx0.
          destruct Hx0 as [Hx0|<-];[|ring_simplify;auto with *].
          rewrite <- (Qmult_le_l _ _ x) in Hy1 by assumption.
          ring_simplify in Hy1.
          eauto with *.
         destruct Hq as [-> ->]; simpl.
         split;[rewrite Hr1;ring|].
         rewrite Qle_minus_iff in Hr2|-*.
         ring_simplify.
         setoid_replace (y * snd b + -1 * y * snd r) with (y * (snd b + - snd r)) by ring.
         destruct Hy;apply Qmult_le_0_compat; auto with *.
      - destruct H as [x [Hx Hr]].
        destruct H0 as [y [Hy Hq]].
        exists (QQavg y (a:QQ) (r:QQ)); split;simpl.
          apply On_path_between.
          destruct Hx as [Hx0 Hx1].
          destruct Hy as [Hy0 Hy1].
          exists (x + y*(1 - x)).
          unfold QQeq; simpl.
          destruct Hr as [-> ->]; simpl.
          repeat split; try ring.
           change 0 with (0 + 0).
           apply Qplus_le_compat; auto.
           apply Qmult_le_0_compat; auto.
           rewrite Qle_minus_iff in Hx1; auto.
          rewrite Qle_minus_iff.
          setoid_replace (1 + - (x + y * (1 - x))) with ((1 - x)*(1 - y)) by ring.
          rewrite Qle_minus_iff in Hx1, Hy1.
          apply Qmult_le_0_compat; auto.
         destruct Hq as [-> ->]; simpl.
         split;[rewrite Hr1;ring|].
         rewrite Qle_minus_iff in Hr2|-*.
         ring_simplify.
         setoid_replace (-1 * y * snd b + y * snd r + snd b + -1 * snd r) with 
           ((1-y) * (snd b + - snd r)) by ring.
         destruct Hy as [Hy0 Hy1].
         rewrite Qle_minus_iff in Hy1.
         apply Qmult_le_0_compat; auto with *.
Qed.

(** Mirror of [under_make_upper]: the lower-hull fold keeps every input point
    [over] the result (unless the input is the singleton [[p]]). *)
Lemma over_make_lower : forall (p:DD) l,
 StronglySorted DDreverse l ->
 In p l ->
 over (p:QQ) (make_lower l) \/ l = [p].
Proof.
  intros p.
  induction l; try contradiction.
  intros Hsort H.
  simpl.
  destruct l as [|b l].
   destruct H as [->|[]].
   right;reflexivity.
  left.
  apply over_add_lower_point.
   inversion_clear Hsort.
   constructor; auto using SSorted_make_lower.
   eapply incl_Forall;[|apply H1].
   apply incl_make_lower.
  destruct l as [|c l].
   simpl.
   apply in_over in H.
   destruct H;auto;discriminate.
  destruct H as [->|H].
   assert (H0 : In p (p :: make_lower (b :: c :: l))) by auto with *.
   apply in_over in H0.
   destruct H0 as [H0|H0];auto.
   simpl in H0.
   rewrite hd_add_lower_point in H0.
   discriminate.
  inversion_clear Hsort.
  specialize (IHl H0 H).
  destruct IHl as [[q Hq]|IHl];try discriminate.
  exists q;split;[apply On_path_tl|]; tauto.
Qed.

(* ----------------------------------------------------------------- *)
(** *** Combining the two hulls -- [over_under] and [convex_hull_sound]. *)

(** A point that is [under] the upper hull and [over] the lower hull is a
    convex combination of a witness from each, hence in the combined hull. *)
Lemma over_under : forall p l1 l2,
 under p l1 ->
 over p l2 ->
 in_convex_hull p (DDSet_from_list (l1 ++ l2)).
Proof.
  intros p l1 l2 [p1 [Hl1 [Hp11 Hp12]]] [p2 [Hl2 [Hp21 Hp22]]].
  apply on_path_convex in Hl1.
  apply on_path_convex in Hl2.
  pose (c := (snd p - snd p2)/(snd p1 - snd p2)).
  assert (Hp0 := Qle_trans _ _ _ Hp22 Hp12).
  apply Qle_lt_or_eq in Hp0.
  assert (Hp : QQeq (QQavg c p1 p2) p).
   unfold QQeq; simpl.
   rewrite <- Hp11, <- Hp21.
   split;[ring|].
   destruct Hp0 as [Hp0|Hp0].
    rewrite Qlt_minus_iff in Hp0.
    unfold c; field; auto with *.
   unfold c; simpl.
   rewrite Hp0; ring_simplify.
   apply Qle_antisym; auto.
   rewrite <- Hp0.
   auto.
  eapply in_convex_hull_morph1;[apply Hp|].
  apply QQavg_in_convex_hull.
  * destruct Hp0 as [Hp0|Hp0].
     rewrite Qlt_minus_iff in Hp0.
     unfold c;split.
      apply Qle_shift_div_l; auto.
      ring_simplify (0 * (snd p1 - snd p2)).
      apply -> Qle_minus_iff; auto.
     apply Qle_shift_div_r; auto.
     rewrite Qle_minus_iff in * .
     ring_simplify.
     assumption.
    unfold c.
    rewrite Hp0.
    setoid_replace (snd p1 - snd p1) with 0 by ring.
    unfold Qdiv.
    change (/0) with 0.
    split;ring_simplify; auto with *.
  * eapply in_convex_hull_subset;[|apply Hl1].
    apply incl_DDSet_from_list; auto with *.
  * eapply in_convex_hull_subset;[|apply Hl2].
    apply incl_DDSet_from_list; auto with *.
Qed.

(** Soundness of [convex_hull]: every point of [s] lies in the hull's own hull.
    Splits the reversed element list into the upper and lower hulls and glues
    the [under] / [over] witnesses with [over_under]. *)
Lemma convex_hull_sound : forall s (p : DD), DDSet.In p s ->
  in_convex_hull p (convex_hull s).
Proof.
  intros s p H.
  apply DDSet.elements_spec1 in H.
  apply SetoidList.InA_rev in H.
  apply SetoidList.InA_alt in H.
  destruct H as [p0 [Hp H]].
  symmetry in Hp.
  change DD in p0.
  destruct Hp as [Hp0 Hp1].
  apply Deq_Q in Hp0,Hp1.
  apply in_convex_hull_morph1 with (p0:QQ);[split;auto|].
  clear -H.
  rename p0 into p.
  rewrite convex_hull_alt.
  assert (HSorted0 := DDSet.elements_spec2 s).
  change (Sorted (DDOrder.lt) (DDSet.elements s)) in HSorted0.
  assert (HSorted1 := Sorted_rev _ _ _ HSorted0).
  set (l := (rev _)) in *.
  set (l1 := make_upper _).
  set (l2 := make_lower _).
  change (Sorted DDreverse l) in HSorted1.
  clear HSorted0.
  destruct l as [|a [|b l]]; try contradiction.
   apply in_in_convex_hull.
   destruct H as [->|[]].
   simpl.
   apply In_DDSet_from_list.
   exists p;split;auto with *.
   change (DDOrder.eq p p).
   reflexivity.
  set (l0 := a :: b :: l) in *.
  apply Sorted_StronglySorted in HSorted1;
  [|intros x y z Hx Hy;unfold DDreverse in *;simpl;transitivity y;auto].
  assert (Hunder := under_make_upper p l0 HSorted1 H).
  assert (Hover := over_make_lower p l0 HSorted1 H).
  destruct Hunder as [Hunder|Hunder];try discriminate.
  destruct Hover as [Hover|Hover];try discriminate.
  apply over_under; auto.
Qed.
