(** * model.scalar: pure functional model of secp256k1 scalars (mod n). *)
(** Copyright (C) 2026 remix7531
    SPDX-License-Identifier: MIT *)

Require Import ZArith.
Require Import Coq.ZArith.Znumtheory.
Require Import Lia.
Require Export secp256k1.model.types.

Open Scope Z_scope.

(** Deterministic obligation preprocessing: just [intros].  The default
    [program_simpl] auto-solver spins on the [(N - a) mod N] obligation
    shapes now that floyd (which used to override it) is no longer loaded. *)
Local Obligation Tactic := intros.

(* ================================================================= *)
(** ** Scalar operations -- [scalar_mul] = [(a * b) mod N].
    ([Scalar] and the word types live in [model.types]; the group order
    [secp256k1_N] and the GLV constants in [model.constants].) *)

(** Modular scalar multiplication: [a * b mod N]. *)
Program Definition scalar_mul (a b : Scalar) : Scalar :=
  mkScalar ((a * b) mod secp256k1_N) _.
Next Obligation.
  split; apply Z.mod_pos_bound; unfold secp256k1_N; lia.
Qed.

(** Widen a [Scalar] (< N < 2^256) to a [UInt256]. *)
Program Definition scalar_to_u256 (s : Scalar) : UInt256 :=
  mkUInt256 (scalar_val s) _.
Next Obligation.
  destruct s as [v [H0 H1]].
  simpl.
  split.
  - lia.
  - unfold secp256k1_N in H1.
    lia.
Qed.

(* ================================================================= *)
(** ** Distinguished scalars -- [scalar_zero] / [scalar_one]. *)

Program Definition scalar_zero : Scalar := mkScalar 0 _.
Next Obligation.
  unfold secp256k1_N; lia.
Qed.

Program Definition scalar_one : Scalar := mkScalar 1 _.
Next Obligation.
  unfold secp256k1_N; lia.
Qed.

(* ================================================================= *)
(** ** Modular operations -- [scalar_negate] / [scalar_half] / [scalar_add] / [reduce_256]. *)

(** Modular negation: [(N - a) mod N]. *)
Program Definition scalar_negate (a : Scalar) : Scalar :=
  mkScalar ((secp256k1_N - scalar_val a) mod secp256k1_N) _.
Next Obligation.
  split; apply Z.mod_pos_bound; unfold secp256k1_N; lia.
Qed.

(** Modular halving: [a * inv2 mod N], where [inv2 = (N+1)/2 = 1/2 mod N]. *)
Program Definition scalar_half (a : Scalar) : Scalar :=
  mkScalar ((scalar_val a * ((secp256k1_N + 1) / 2)) mod secp256k1_N) _.
Next Obligation.
  split; apply Z.mod_pos_bound; unfold secp256k1_N; lia.
Qed.

(** Modular addition: [(a + b) mod N]. *)
Program Definition scalar_add (a b : Scalar) : Scalar :=
  mkScalar ((scalar_val a + scalar_val b) mod secp256k1_N) _.
Next Obligation.
  split; apply Z.mod_pos_bound; unfold secp256k1_N; lia.
Qed.

(** Reduce a 256-bit unsigned integer modulo the group order. *)
Program Definition reduce_256 (x : UInt256) : Scalar :=
  mkScalar (u256_val x mod secp256k1_N) _.
Next Obligation.
  split; apply Z.mod_pos_bound; unfold secp256k1_N; lia.
Qed.

(** [mul_shift_var]: round [a*b / 2^shift] to the nearest integer.  The C adds
    bit [shift-1] of the 512-bit product [a*b] as the round-half-up term. *)
Definition scalar_mul_shift (a b : Scalar) (shift : Z) : Z :=
  let p := scalar_val a * scalar_val b in
  p / 2 ^ shift + (p / 2 ^ (shift - 1)) mod 2.

(* ================================================================= *)
(** ** Property lemmas -- [scalar_negate_unique] / [scalar_half_prop] / [scalar_negate_prop].
    ([scalar_eq_ext] lives in [model.types].) *)

(** Defining property of [scalar_negate]: it is THE additive inverse mod [N].
    Within [[0, N)] the property [(a + r) mod N = 0] determines [r] uniquely, so
    this is an equivalence with the [(N - a) mod N] construction, not a weakening.
    Used by [secp256k1_scalar_split_lambda] to recover the [scalar_negate] value
    from the property-based [secp256k1_scalar_negate] postcondition. *)
Lemma scalar_negate_unique (a r : Scalar) :
  Z.modulo (Z.add (scalar_val a) (scalar_val r)) secp256k1_N = 0 ->
  r = scalar_negate a.
Proof.
  intros H.
  pose proof (scalar_range a) as Ha.
  pose proof (scalar_range r) as Hr.
  apply scalar_eq_ext.
  replace (scalar_val (scalar_negate a))
    with ((secp256k1_N - scalar_val a) mod secp256k1_N) by reflexivity.
  destruct (Z.eq_dec (scalar_val a) 0) as [Ha0|Ha0].
  - rewrite Ha0 in *. rewrite Z.add_0_l, Z.mod_small in H by lia.
    rewrite Z.sub_0_r, Z_mod_same_full. lia.
  - rewrite Z.mod_small by lia.
    apply Zmod_divides in H;[|lia].
    destruct H as [c Hc]. assert (0 < scalar_val a) by lia.
    assert (c = 1) by nia. subst c. lia.
Qed.

(** Defining property of [scalar_half]: doubling it recovers [a] mod [N] (since
    [2] is a unit mod the odd modulus [N], so [a/2] is the unique solution in
    [[0, N)]).  Equivalent to the [a * 2^{-1} mod N] construction, not weaker. *)
Lemma scalar_half_prop (a : Scalar) :
  Z.modulo (Z.mul 2 (scalar_val (scalar_half a))) secp256k1_N = scalar_val a.
Proof.
  pose proof (scalar_range a) as Ha.
  replace (scalar_val (scalar_half a))
    with ((scalar_val a * ((secp256k1_N + 1) / 2)) mod secp256k1_N) by reflexivity.
  rewrite Zmult_mod_idemp_r.
  assert (Hdiv : secp256k1_N + 1 = 2 * ((secp256k1_N + 1) / 2)).
  { apply Zdivide_Zdiv_eq;[lia|]. rewrite secp256k1_N_as_2H. exists (secp256k1_N_H + 1). ring. }
  replace (2 * (scalar_val a * ((secp256k1_N + 1) / 2)))
    with (scalar_val a * (2 * ((secp256k1_N + 1) / 2))) by ring.
  rewrite <- Hdiv.
  replace (scalar_val a * (secp256k1_N + 1)) with (scalar_val a + scalar_val a * secp256k1_N) by ring.
  rewrite Z.mod_add by lia.
  apply Z.mod_small; lia.
Qed.

(** Forward direction of [scalar_negate_unique], used by the property-based
    [secp256k1_scalar_negate] body proof to discharge its postcondition. *)
Lemma scalar_negate_prop (a : Scalar) :
  Z.modulo (Z.add (scalar_val a) (scalar_val (scalar_negate a))) secp256k1_N = 0.
Proof.
  replace (scalar_val (scalar_negate a))
    with ((secp256k1_N - scalar_val a) mod secp256k1_N) by reflexivity.
  rewrite Zplus_mod_idemp_r.
  replace (scalar_val a + (secp256k1_N - scalar_val a)) with secp256k1_N by ring.
  apply Z_mod_same_full.
Qed.

(* ================================================================= *)
(** ** GLV / split_lambda views -- [c_lambda] / [c_minus_b1] / [c_minus_b2] / [c_g1] / [c_g2]. *)

(** Their [UInt256] views, matching the C structs' stored limbs. *)
Program Definition c_lambda : UInt256 := mkUInt256 secp256k1_lambda _.
Next Obligation.
  unfold secp256k1_lambda; lia.
Qed.

Program Definition c_minus_b1 : UInt256 := mkUInt256 minus_b1_z _.
Next Obligation.
  unfold minus_b1_z; lia.
Qed.

Program Definition c_minus_b2 : UInt256 := mkUInt256 minus_b2_z _.
Next Obligation.
  unfold minus_b2_z; lia.
Qed.

Program Definition c_g1 : UInt256 := mkUInt256 g1_z _.
Next Obligation.
  unfold g1_z; lia.
Qed.

Program Definition c_g2 : UInt256 := mkUInt256 g2_z _.
Next Obligation.
  unfold g2_z; lia.
Qed.
