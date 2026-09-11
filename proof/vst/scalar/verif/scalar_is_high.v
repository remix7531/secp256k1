(** * Verif_scalar_is_high: Proof of body_secp256k1_scalar_is_high *)
(** Copyright (C) 2026 remix7531
    SPDX-License-Identifier: MIT *)

Require Import secp256k1.vst.base.
Require Import secp256k1.vst.helper.notations.
Require Import secp256k1.vst.gprog.
Require Import secp256k1.vst.tactics.core.
Require Import secp256k1.vst.tactics.int128.
Require Import secp256k1.vst.tactics.scalar.

(* ================================================================= *)
(** ** secp256k1_scalar_is_high -- [a > N/2]. *)

(** The C cascade comparison correctly computes [a > floor(N/2)].

    After [repeat forward], the postcondition is a single pure equality
    between an [Int.or/and/not] cascade and the spec.  We name the four
    scalar limbs, recover the limb decomposition via [eval4_limbs],
    unfold [Int64.ltu] to expose [zlt] decisions on concrete [N_H]-limb
    values, destruct all six comparisons (2^6 = 64 branches), let [simpl]
    evaluate the boolean/Int arithmetic, split on the spec [Z_lt_dec],
    and close every branch with [reflexivity], [discriminate], or
    [lia] (after unfolding the [N_H] constants). *)
Lemma body_secp256k1_scalar_is_high:
  semax_body Vprog Gprog
    f_secp256k1_scalar_is_high spec_secp256k1_scalar_is_high.
Proof.
  start_function.

  (* Walk the limb-comparison cascade and the return *)
  repeat forward.
  apply prop_right.
  f_equal.

  (* Expose Int64.ltu under the Int64.cmpu wrappers *)
  unfold Int64.cmpu.

  (* Name the four limbs and establish their ranges *)
  set (d0 := a mod 2^64).
  set (d1 := (a / 2^64) mod 2^64).
  set (d2 := (a / 2^128) mod 2^64).
  set (d3 := (a / 2^192) mod 2^64).
  assert (Hd0 : 0 <= d0 < 2^64) by (subst d0; apply Z.mod_pos_bound; lia).
  assert (Hd1 : 0 <= d1 < 2^64) by (subst d1; apply Z.mod_pos_bound; lia).
  assert (Hd2 : 0 <= d2 < 2^64) by (subst d2; apply Z.mod_pos_bound; lia).
  assert (Hd3 : 0 <= d3 < 2^64) by (subst d3; apply Z.mod_pos_bound; lia).

  (* A scalar is below N < 2^256 *)
  assert (Harange : 0 <= scalar_val a < 2^256).
  { pose proof (scalar_range a) as Hr.
    unfold secp256k1_N in Hr.
    lia. }

  (* Limb decomposition via eval4_limbs *)
  assert (Hdecomp : scalar_val a = d0 + d1 * 2^64 + d2 * 2^128 + d3 * 2^192).
  { subst d0 d1 d2 d3.
    rewrite limb_fold0, limb_fold1, limb_fold2, limb_fold3.
    pose proof (eval4_limbs (2^64) (scalar_val a)) as Heval.
    unfold eval4 in Heval.
    change ((2^64)^2) with (2^128) in Heval.
    change ((2^64)^3) with (2^192) in Heval.
    change ((2^64)^4) with (2^256) in Heval.
    symmetry.
    apply Heval; lia. }

  (* Unfold Int64.ltu to zlt; replace limb unsigned_repr (in range)
     and evaluate the constant unsigned values to N_H limbs *)
  unfold Int64.ltu.
  rewrite ?(Int64.unsigned_repr d0), ?(Int64.unsigned_repr d1),
          ?(Int64.unsigned_repr d2), ?(Int64.unsigned_repr d3) by rep_lia.
  change (Int64.unsigned (Int64.repr 9223372036854775807)) with N_H_3 in *.
  change (Int64.unsigned (Int64.repr (-1))) with N_H_2 in *.
  change (Int64.unsigned (Int64.repr 6725966010171805725)) with N_H_1 in *.
  change (Int64.unsigned (Int64.repr (-2312264954237214560))) with N_H_0 in *.

  (* Destruct all 6 zlt comparisons (N_H_3<d3, d3<N_H_3, N_H_1<d1,
     d2<N_H_2, d1<N_H_1, N_H_0<d0), creating 64 branches with concrete
     Z hypotheses.  Every branch closes by the same uniform chain: evaluate
     Z.b2z/Z.lor to 0 or 1, simplify Int arithmetic on small concrete
     values, split on the spec, and finish by reflexivity, by discriminate,
     or -- where the limb comparisons and Z_lt_dec contradict each other --
     by lia on the unfolded N_H constants. *)
  do 6 match goal with |- context [zlt ?x ?y] => destruct (zlt x y) end;
      simpl Z.b2z;
      simpl Z.lor;
      rewrite ?Int.or_zero_l, ?Int.or_zero, ?Int.and_zero_l, ?Int.and_zero;
      destruct (Z_lt_dec secp256k1_N_H a);
      try reflexivity;
      try discriminate;
      exfalso;
      unfold secp256k1_N_H, N_H_0, N_H_1, N_H_2, N_H_3 in *;
      lia.
Qed.
