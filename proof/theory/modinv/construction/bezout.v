(** * theory.modinv.construction.bezout: Bezout-witness machinery for the [mod_inv] construction. *)
(** Copyright (C) 2026 remix7531
    Ported from BlockstreamResearch/simplicity Coq/C/modinv.v
    (commit c1dddedd), Copyright (c) 2018 Blockstream, originally MIT.
    Upstream notice reproduced in proof/README.md.
    SPDX-License-Identifier: MIT *)

(** The gcd/Bezout-coefficient apparatus underlying the constructive [mod_inv];
    hoisted into its own file to keep [theory.modinv.construction.inverse] focused.
    Referenced only by [theory.modinv.construction.inverse].

    Adapted for Rocq 9.0 / VST 2.16 in this repository's layered proof tree. *)

Require Import ZArith.
Require Import Coq.ZArith.Znumtheory.
Require Import Lia.
Require Import Coq.Logic.Eqdep_dec.

Open Scope Z_scope.
Arguments Z.add !x !y.
Arguments Z.sub !m !n.
Arguments Z.mul !x !y.

(* ================================================================= *)
(** ** Bezout witnesses -- [Bezout a b d] / smart constructors. *)

(** A Bezout witness: coefficients [u], [v] with [u*a + v*b = d]. *)
Record Bezout (a b d : Z) :=
{ u_bezout : Z
; v_bezout : Z
; h_bezout : u_bezout * a + v_bezout * b = d
}.
Arguments u_bezout [a b d].
Arguments v_bezout [a b d].

(** Normalize the equation proof so it is irrelevant (via [UIP_dec]). *)
Definition Bezout_normalize [a b d] (H: Bezout a b d) : Bezout a b d.
Proof.
  exists (u_bezout H) (v_bezout H).
  match goal with
   |- ?x = ?y => destruct (Z.eq_dec x y);[assumption|]
  end.
  abstract (destruct H;contradiction).
Defined.

(** Normalizing a witness leaves it propositionally equal to itself. *)
Lemma Bezout_normalize_eq a b d (H: Bezout a b d) : Bezout_normalize H = H.
Proof.
  destruct H as [u v H].
  unfold Bezout_normalize.
  destruct (Z.eq_dec _ _);try contradiction.
  replace e with H; try reflexivity.
  apply UIP_dec.
  apply Z.eq_dec.
Qed.

(** Bezout for [0] and [b]: gcd is [Z.abs b]. *)
Definition Bezout_0b b : Bezout 0 b (Z.abs b).
Proof.
  exists 0 (Z.sgn b).
  abstract (rewrite <- Z.sgn_abs;ring).
Defined.

(** Bezout for [a] and [0]: gcd is [Z.abs a]. *)
Definition Bezout_a0 a : Bezout a 0 (Z.abs a).
Proof.
  exists (Z.sgn a) 0.
  abstract (rewrite <- Z.sgn_abs;ring).
Defined.

(** Trivial Bezout witness producing target [a]. *)
Definition Bezout_aba a b : Bezout a b a.
Proof.
  exists 1 0.
  abstract ring.
Defined.

(** Trivial Bezout witness producing target [b]. *)
Definition Bezout_abb a b : Bezout a b b.
Proof.
  exists 0 1.
  abstract ring.
Defined.

(** Lift a witness for [(b - a, a)] to one for [(a, b)]. *)
Definition Bezout_b_minus_a a b d : Bezout (b - a) a d -> Bezout a b d.
Proof.
  intros bezout.
  exists (v_bezout bezout - u_bezout bezout) (u_bezout bezout).
  abstract (destruct bezout as [u v <-];simpl;ring).
Defined.

(** Lift a witness for [(a - b, b)] to one for [(a, b)]. *)
Definition Bezout_a_minus_b a b d : Bezout (a - b) b d -> Bezout a b d.
Proof.
  intros bezout.
  exists (u_bezout bezout) (v_bezout bezout - u_bezout bezout).
  abstract (destruct bezout as [u v <-];simpl;ring).
Defined.

(** Scale a witness for [(a, b)] to one for [(2a, 2b)] with target [2d]. *)
Definition Bezout_even a b d : Bezout a b d -> Bezout (2*a) (2*b) (2*d).
Proof.
  intros bezout.
  exists (u_bezout bezout) (v_bezout bezout).
  abstract (destruct bezout as [u v <-];simpl;ring).
Defined.

(** Swap the two inputs of a Bezout witness. *)
Definition Bezout_flip a b d : Bezout a b d -> Bezout b a d.
Proof.
  intros bezout.
  exists (v_bezout bezout) (u_bezout bezout).
  abstract (destruct bezout as [u v <-];simpl;ring).
Defined.

(** Double the first input ([a -> 2a]) when [b] is odd. *)
Definition Bezout_2a a b d : Z.Odd b -> Bezout a b d -> Bezout (2*a) b d.
Proof.
  intros Hodd [u v Huv].
  destruct (Z.odd u) eqn:H.
  - exists (Z.div2 (u + b)) (v - a).
    abstract (
      rewrite <- Z.odd_spec in Hodd;
      rewrite (Zdiv2_odd_eqn u), (Zdiv2_odd_eqn b) in Huv|-*;
      rewrite <- Huv, H, Hodd;
      rewrite Z.div2_div;
      replace (2 * Z.div2 u + 1 + (2 * Z.div2 b + 1)) with
        ((Z.div2 u + Z.div2 b + 1) * 2) by ring;
      rewrite Z.div_mul by lia;
      ring
    ).
  - exists (Z.div2 u) v.
    abstract (
      rewrite (Zdiv2_odd_eqn u) in Huv;
      rewrite <- Huv, H;
      ring
    ).
Defined.

(** Double the second input ([b -> 2b]) when [a] is odd. *)
Definition Bezout_2b a b d : Z.Odd a -> Bezout a b d -> Bezout a (2*b) d.
Proof.
  intros Hodd bezout.
  apply Bezout_flip.
  apply Bezout_2a; try assumption.
  apply Bezout_flip.
  assumption.
Defined.

(* ----------------------------------------------------------------- *)
(** *** Positive gcd witness -- [Pos_Bezoutn] / [Pos_Bezout]. *)

(** Subtraction does not increase the positive's bit size. *)
Lemma Pos_size_nat_sub a b : (Pos.size_nat (a - b) <= Pos.size_nat a)%nat.
Proof.
  destruct (Pos.lt_total a b) as [H|[->|H]].
  - rewrite (Pos.sub_lt _ _ H); destruct a; simpl; lia.
  - rewrite Pos.sub_diag; destruct b; simpl; lia.
  - apply Pos.size_nat_monotone; apply Pos.sub_decr; assumption.
Qed.

(** Binary-gcd Bezout for two positives, bounded by fuel [n]. *)
Definition Pos_Bezoutn : forall n a b,
  (Pos.size_nat a + Pos.size_nat b <= n)%nat -> Bezout (Z.pos a) (Z.pos b) (Z.pos (Pos.gcdn n a b)).
Proof.
  fix Pos_Bezoutn 1.
  intros [|n].
  - abstract (intros a b Hn; destruct a; destruct b; simpl in Hn; lia).
  - intros [a'|a0|].
    + intros [b'|b0|] Hsize;simpl.
      * destruct (a' ?= b')%positive eqn:Hcmp; simpl.
        apply Bezout_aba.
        apply Bezout_b_minus_a;simpl;apply Bezout_2a.
        { abstract (rewrite <- Z.odd_spec; reflexivity). }
        destruct (Z.eq_dec (Z.pos_sub b' a') (Z.pos (b' - a'))) as [->|Hneq].
        { apply (Pos_Bezoutn n);abstract(assert (H:=Pos_size_nat_sub b' a'); simpl in *;lia). }
        abstract (rewrite Pos.compare_lt_iff in Hcmp;apply Z.pos_sub_gt in Hcmp;contradiction).
        apply Bezout_a_minus_b;simpl;apply Bezout_2a.
        { abstract (rewrite <- Z.odd_spec; reflexivity). }
        destruct (Z.eq_dec (Z.pos_sub a' b') (Z.pos (a' - b'))) as [->|Hneq].
        { apply (Pos_Bezoutn n);abstract(assert (H:=Pos_size_nat_sub a' b'); simpl in *;lia). }
        abstract (rewrite Pos.compare_gt_iff in Hcmp;apply Z.pos_sub_gt in Hcmp;contradiction).
      * change (Z.pos b0~0) with (2*Z.pos b0);apply Bezout_2b.
        { abstract (rewrite <- Z.odd_spec; reflexivity). }
        apply (Pos_Bezoutn n).
        abstract(simpl in *;lia).
      * apply Bezout_abb.
    + intros [b'|b0|] Hsize;simpl.
      * change (Z.pos a0~0) with (2*Z.pos a0);apply Bezout_2a.
        { abstract (rewrite <- Z.odd_spec; reflexivity). }
        apply (Pos_Bezoutn n).
        abstract(simpl in *;lia).
      * apply (Bezout_even (Z.pos a0) (Z.pos b0) (Z.pos (Pos.gcdn n a0 b0))).
        apply (Pos_Bezoutn n).
        abstract(simpl in *;lia).
      * apply Bezout_abb.
    + intros b _.
      apply Bezout_aba.
Defined.

(** Binary-gcd Bezout for two positives (fuel supplied automatically). *)
Definition Pos_Bezout a b : Bezout (Z.pos a) (Z.pos b) (Z.pos (Pos.gcd a b)).
Proof.
  apply Bezout_normalize.
  apply Pos_Bezoutn.
  abstract lia.
Defined.

(* ----------------------------------------------------------------- *)
(** *** Sign-handling wrappers -- [Bezout_neg_a] / [Bezout_gcd]. *)

(** Negate the first input of a Bezout witness. *)
Definition Bezout_neg_a a b d : Bezout (-a) b d -> Bezout a b d.
Proof.
  intros bezout.
  exists (- u_bezout bezout) (v_bezout bezout).
  abstract (destruct bezout as [u v <-];simpl;ring).
Defined.

(** Negate the second input of a Bezout witness. *)
Definition Bezout_neg_b a b d : Bezout a (-b) d -> Bezout a b d.
Proof.
  intros bezout.
  exists (u_bezout bezout) (- v_bezout bezout).
  abstract (destruct bezout as [u v <-];simpl;ring).
Defined.

(** Bezout witness for arbitrary integers, target [Z.gcd a b]. *)
Definition Bezout_gcd a b : Bezout a b (Z.gcd a b).
Proof.
  apply Bezout_normalize.
  destruct a; try apply Bezout_0b; destruct b; try apply Bezout_a0.
  - apply Pos_Bezout.
  - apply Bezout_neg_b; apply Pos_Bezout.
  - apply Bezout_neg_a; apply Pos_Bezout.
  - apply Bezout_neg_a; apply Bezout_neg_b; apply Pos_Bezout.
Defined.
