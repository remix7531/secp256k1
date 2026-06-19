(** * theory.modinv.divsteps.base: dyadic rationals and the convex-hull divstep state machine. *)
(** Copyright (C) 2026 remix7531
    Adapted from sipa/safegcd-bounds coq/divsteps/divsteps_base.v
    (commit 06abb7f), Copyright (c) 2021 Blockstream, originally MIT.
    Upstream notice reproduced in proof/README.md.
    SPDX-License-Identifier: MIT *)

(** Integrated into this repository's layered proof tree (Rocq 9.0). *)

Require Import Orders.
Require Import OrdersEx.
Require Import OrdersAlt.
Require Import ZArith.
Require Import QArith.
Require Import Qpower.
Require Import MSets.
Require Import List.
Import ListNotations.

(** [INC] is the divstep delta increment, always +1 (mirrors [divsteps.INC] for this convex-hull encoding). *)
Definition INC : Z := 1.

(* ================================================================= *)
(** ** Dyadic rationals -- [D] = mantissa * 2 ^ exponent, with [Q] coercion. *)

(** [D] is a dyadic rational, mantissa * 2^exponent, injecting into [Q] via [inject_D]. *)
Record D := Dmake { Dmantissa : Z; Dexponent : Z }.

(** [D_from_Z] embeds an integer as a dyadic rational with exponent 0; registered as the [Z >-> D] coercion. *)
Definition D_from_Z (a : Z) := Dmake a 0.
Coercion D_from_Z : Z >-> D.

(** [inject_D] evaluates a dyadic [D] as the rational it denotes; registered as the [D >-> Q] coercion. *)
Definition inject_D (a : D) := (inject_Z (Dmantissa a) * 2 ^ Dexponent a)%Q.
Coercion inject_D : D >-> Q.

(** [DredH p z] strips trailing even (binary-zero) bits from [p], bumping [z] once per bit stripped. *)
Fixpoint DredH (p : positive) (z : Z) : positive*Z :=
  match p with
  | xO x => DredH x (Z.succ z)
  | _ => (p, z)
  end.

(** [Dred] reduces a dyadic [D] to canonical form by cancelling common factors of 2, via [DredH]. *)
Definition Dred (a : D) : D :=
  let (m, e) := a in
  match m with
  | Z0 => 0%Z
  | Zpos p => let (p', e') := DredH p e in Dmake (Zpos p') e'
  | Zneg p => let (p', e') := DredH p e in Dmake (Zneg p') e'
  end.

(** [Dalign a b] rescales [a]'s and [b]'s mantissas to a shared exponent, returning both mantissas and that exponent. *)
Definition Dalign (a b : D) : Z * Z * Z :=
  match (Dexponent a - Dexponent b)%Z with
  | Zpos d => (Z.shiftl (Dmantissa a) (Zpos d), Dmantissa b, Dexponent b)
  | Z0 => (Dmantissa a, Dmantissa b, Dexponent b)
  | Zneg d => (Dmantissa a, Z.shiftl (Dmantissa b) (Zpos d), Dexponent a)%Z
  end.

(** [Dalign] preserves value: the aligned mantissas paired with the common exponent still denote [x] and [y]. *)
Lemma Dalign_lr : forall x y, let '(xm', ym', e') := Dalign x y in
  inject_D (Dmake xm' e') == inject_D x /\
  inject_D (Dmake ym' e') == inject_D y.
Proof.
  intros [xm xe] [ym ye].
  cbv beta iota delta [Dalign Dexponent Dmantissa inject_D].
  case (xe - ye)%Z as [|p|p] eqn:He; [rewrite (Zminus_eq _ _ He); split; reflexivity| |];
    split; try reflexivity;
    rewrite Z.shiftl_mul_pow2, inject_Z_mult, Zpower_Qpower; auto with *;
    rewrite <- Qmult_assoc, <- Qpower_plus; try discriminate.
  - rewrite <- He, Z_as_OT.sub_add; reflexivity.
  - rewrite <- (Pos2Z.opp_neg p), <- He.
    replace (-(xe - ye) + xe)%Z with ye by ring.
    reflexivity.
Qed.

(** [Dadd] adds two dyadic rationals after aligning them to a common exponent. *)
Definition Dadd (a b : D) : D :=
  let '(a',b',e') := Dalign a b in Dmake (a' + b') e'.

(** [Dsub] subtracts two dyadic rationals after aligning them to a common exponent. *)
Definition Dsub (a b : D) : D :=
  let '(a',b',e') := Dalign a b in Dmake (a' - b') e'.

(** [Dmult] multiplies dyadic rationals: mantissas multiply, exponents add. *)
Definition Dmult (a b : D) : D :=
  Dmake (Dmantissa a * Dmantissa b) (Dexponent a + Dexponent b).

(** [Dhalf] halves a dyadic rational by decrementing its exponent. *)
Definition Dhalf (a : D) : D :=
  Dmake (Dmantissa a) (Z.pred (Dexponent a)).

(** [Dcompare] compares two dyadic rationals by aligning them and comparing the resulting mantissas. *)
Definition Dcompare (a b : D) : comparison :=
  let '(a',b',_) := Dalign a b in (a' ?= b')%Z.

(** [Dcompare] agrees with the [Q]-valued comparison [?=] on the rationals [x]/[y] denote. *)
Lemma Dcompare_Q : forall x y, Dcompare x y = (x ?= y)%Q.
Proof.
  intros x y.
  unfold Dcompare.
  assert (Hxy := Dalign_lr x y).
  destruct (Dalign x y) as [[xm' ym'] e'].
  destruct Hxy as [<- <-].
  unfold Qcompare.
  simpl.
  rewrite <- !Zmult_assoc.
  apply Zmult_compare_compat_r.
  apply Z.lt_gt.
  assert (Hp : forall p, (0 < Z.pow_pos 2 p)%Z).
  { intros p.
    apply Zpow_facts.Zpower_pos_pos; auto with *. }
  apply Zmult_lt_0_compat;
    destruct e'; simpl; auto with *;
    rewrite Qpower_decomp; simpl; auto with *.
  unfold Qinv; simpl.
  specialize (Hp p).
  destruct (Z.pow_pos 2 p)%Z; try discriminate; auto with *.
Qed.

(** [Dcompare] is antisymmetric: swapping the arguments flips the comparison result. *)
Lemma Dcompare_antisym : forall x y, Dcompare y x = CompOpp (Dcompare x y).
Proof.
  intros x y.
  rewrite !Dcompare_Q, Qcompare_antisym.
  reflexivity.
Qed.

(** [Dcompare] is transitive: two comparisons agreeing on [c] compose to a third agreeing on [c]. *)
Lemma Dcompare_trans : forall c x y z,
 Dcompare x y = c -> Dcompare y z = c -> Dcompare x z = c.
Proof.
  intros c x y z <-.
  rewrite !Dcompare_Q.
  destruct (Qcompare_spec x y).
  - rewrite H; auto.
  - rewrite <- !Qlt_alt.
    eauto using Qlt_trans.
  - rewrite <- !Qgt_alt.
    eauto using Qlt_trans.
Qed.

(** [D_as_OrderedTypeAlt] packages [D] with [Dcompare] as an [OrderedTypeAlt]. *)
Module D_as_OrderedTypeAlt <: OrderedTypeAlt.
  Definition t := D.
  Definition compare := Dcompare.
  Definition compare_sym := Dcompare_antisym.
  Definition compare_trans := Dcompare_trans.
End D_as_OrderedTypeAlt.

(** [D_as_OT] upgrades [D_as_OrderedTypeAlt] to the standard [OrderedType] interface. *)
Module D_as_OT <: OrderedType := OT_from_Alt D_as_OrderedTypeAlt.
(** [D_as_OTF] upgrades [D_as_OT] to the total-order [OrderedTypeFull] interface. *)
Module D_as_OTF <: OrderedTypeFull := OT_to_Full D_as_OT.
(** [D_as_TTLT] exposes [D]'s order as a boolean [leb], for [Dltb]. *)
Module D_as_TTLT <: TotalTransitiveLeBool := OTF_to_TTLB D_as_OTF.

(** [Dltb a b] is the strict-less-than boolean test on dyadic rationals. *)
Definition Dltb (a b : D) := negb (D_as_TTLT.leb b a).

(** [DDOrder] orders pairs of dyadic rationals lexicographically. *)
Module DDOrder <: OrderedType := PairOrderedType D_as_OT D_as_OT.

(** [DD] is a pair of dyadic rationals, a point in the (rational) plane. *)
Definition DD := DDOrder.t.

(* ================================================================= *)
(** ** Convex hull over 2D dyadic points -- [orientation] / [convex_hull]. *)

(* | x1 y1 1 |
 * | x2 y2 1 | ?= 0
 * | x3 y3 1 |
 *)
(** [orientation p1 p2 p3] is the sign of the determinant testing the turn direction of the three points. *)
Definition orientation (p1 p2 p3 : DD) : comparison :=
  let (x1, y1) := p1 in
  let (x2, y2) := p2 in
  let (x3, y3) := p3 in
  (* (x1*y2 - y1*x2) + (x2*y3 - y2*x3) ?= x1*y3-y1*x3. *)
  Dcompare (Dmult (Dsub x1  x3) (Dsub y2 y3)) (Dmult (Dsub y1 y3) (Dsub x2 x3)).

(** [add_lower_point] inserts [p] into a lower convex-hull chain [l], dropping points [p] makes non-convex. *)
Fixpoint add_lower_point (p : DD) (l : list DD) : list DD :=
  match l with
  | [] => [p]
  | q :: l0 =>
    match l0 with
    | [] =>
      match DDOrder.compare p q with
      | Eq => [p]
      | _ => [p; q]
      end
    | r :: _ =>
      match orientation p q r with
      | Lt => p :: l
      | _ => add_lower_point p l0
      end
    end
  end.

(** [add_upper_point] inserts [p] into an upper convex-hull chain [l], dropping points [p] makes non-convex. *)
Fixpoint add_upper_point (p : DD) (l : list DD) : list DD :=
  match l with
  | [] => [p]
  | q :: l0 =>
    match l0 with
    | [] =>
      match DDOrder.compare p q with
      | Eq => [p]
      | _ => [p; q]
      end
    | r :: _ =>
      match orientation p q r with
      | Gt => p :: l
      | _ => add_upper_point p l0
      end
    end
  end.

(** [DDSet] is a finite-set implementation over [DD] points, ordered by [DDOrder]. *)
Module DDSet := MSetAVL.Make DDOrder.
(** [DDSet_from_list] builds a [DDSet] from a list of points, folding in each one. *)
Definition DDSet_from_list (l : list DD) :=
  fold_left (fun s a => DDSet.add a s) l DDSet.empty.
(** [DDSet_map] applies [f] to every point of [s], rebuilding the result as a fresh [DDSet]. *)
Definition DDSet_map (f : DD -> DD) (s : DDSet.t) :=
  DDSet.fold (fun a s => DDSet.add (f a) s) s DDSet.empty.

(** [convex_hull s] is the convex hull of [s], assembled from its upper and lower chains via [add_upper_point]/[add_lower_point]. *)
Definition convex_hull (s : DDSet.t) : DDSet.t :=
  DDSet_from_list
    ((DDSet.fold add_upper_point s []) ++ (DDSet.fold add_lower_point s [])).

(** [narrow M s] tests whether every point of [s], scaled by [M], lies strictly inside [(-1, 1)]. *)
Definition narrow (M : Z) (s : DDSet.t) : bool :=
  match (DDSet.min_elt s, DDSet.max_elt s) with
  | (Some (l, _), Some (h, _)) => andb (Dltb (-1)%Z (Dmult M l)) (Dltb (Dmult M h) 1%Z)
  | _ => true
  end.

(* ================================================================= *)
(** ** Divstep transforms and the [process_divstep] state machine. *)

(** [odd_pos_trans] is the point transform for an odd divstep with [delta] positive: [(g,f) |-> ((g-f)/2, g)]. *)
Definition odd_pos_trans (p : DD) : DD :=
  let (g, f) := p in
  (Dred (Dhalf (Dsub g f)), g) (* ((g - f) / 2), g) *).
(** [odd_nonpos_trans] is the point transform for an odd divstep with [delta] nonpositive: [(g,f) |-> ((g+f)/2, f)]. *)
Definition odd_nonpos_trans (p : DD) : DD :=
  let (g, f) := p in
  (Dred (Dhalf (Dadd g f)), f) (* ((g + f) / 2), f) *).
(** [even_trans] is the point transform for an even divstep: [(g,f) |-> (g/2, f)]. *)
Definition even_trans (p : DD) : DD :=
  let (g, f) := p in
  (Dhalf g, f) (* (g / 2), f) *).

(** [even_map] advances a [(delta, points)] pair through the even-[g] divstep branch. *)
Definition even_map (kv : Z * DDSet.t) : Z * DDSet.t :=
  let (k, v) := kv in ((INC + k)%Z, DDSet_map even_trans v).
(** [odd_map] advances a [(delta, points)] pair through the odd-[g] divstep branch, choosing [odd_pos_trans]/[odd_nonpos_trans] by the sign of [delta]. *)
Definition odd_map (kv : Z * DDSet.t) : Z * DDSet.t :=
  let (k, v) := kv in
  if (0 <? k)%Z
  then ((INC - k)%Z, DDSet_map odd_pos_trans v)
  else ((INC + k)%Z, DDSet_map odd_nonpos_trans v).

Require FMapAVL.

(** [ZMap] is a finite-map implementation keyed by [Z], used to index hull sets by [delta]. *)
Module ZMap := FMapAVL.Make OrderedTypeEx.Z_as_OT.

(** [State] maps each reachable [delta] value to its current set of hull points. *)
Definition State := ZMap.t DDSet.t.
(** [empty] is the [State] with no tracked [delta] values. *)
Definition empty : State := ZMap.empty DDSet.t.
(** [State_join k v m] merges point set [v] into whatever [m] already tracks at key [k], by union. *)
Definition State_join (k : Z) (v : DDSet.t) (m : State) : State :=
  ZMap.add k (match ZMap.find k m with
              | None =>  v
              | Some v0 => DDSet.union v v0
              end)
           m.
(** [State_from_list] rebuilds a [State] from a list of [(delta, points)] pairs, joining duplicates via [State_join]. *)
Definition State_from_list (l : list (Z * DDSet.t)) :=
  fold_left (fun s kv => State_join (fst kv) (snd kv) s) l empty.

(** [process_divstep M] advances every tracked [delta]/point set one divstep ([even_map]/[odd_map]), then re-narrows each set to its [convex_hull] whenever it is not already [narrow] for modulus [M]. *)
Definition process_divstep (M : Z) (s : State) : State :=
  let f kv := [even_map kv; odd_map kv] in
  let s1 := (State_from_list (flat_map f (ZMap.elements s))) in
  let g kv := let (k, v) := kv : Z * DDSet.t in
              if narrow M v then [] else [(k, convex_hull v)]
  in State_from_list (flat_map g (ZMap.elements s1)).

(** [set0] is the initial hull point set {(0,1), (1,1)}. *)
Definition set0 : DDSet.t := DDSet_from_list [(0:D,1:D); (1:D,1:D)]%Z.
(** [state0] is the initial [State]: [set0] tracked at [delta] = 1. *)
Definition state0 : State := ZMap.add 1%Z set0 empty.

(* ================================================================= *)
(** ** Worked examples -- small-modulus [vm_compute] sanity checks. *)

(** Sanity check: modulus [0x34688] empties (converges) within 50 divsteps. *)
Lemma example_0x34688_50 : ZMap.Empty (N.iter 50 (process_divstep 0x34688) state0).
Proof.
  apply ZMap.is_empty_2.
  Time vm_compute.
  auto.
Qed.

(** Sanity check: modulus [0x34689] does not yet empty within 50 divsteps. *)
Lemma example_0x34689_50 : ~ZMap.Empty (N.iter 50 (process_divstep 0x34689) state0).
Proof.
  intros H.
  apply ZMap.is_empty_1 in H.
  Time vm_compute in H.
  discriminate.
Qed.

(** Sanity check: modulus [0x34688] does not yet empty within 49 divsteps (50 is needed). *)
Lemma example_0x34688_49 : ~ZMap.Empty (N.iter 49 (process_divstep 0x34688) state0).
Proof.
  intros H.
  apply ZMap.is_empty_1 in H.
  Time vm_compute in H.
  discriminate.
Qed.
