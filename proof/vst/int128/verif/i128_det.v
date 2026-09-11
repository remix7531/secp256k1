(** * Verif_i128_det: Proof of body_secp256k1_i128_det *)
(** Copyright (C) 2026 remix7531
    SPDX-License-Identifier: MIT *)

Require Import secp256k1.vst.base.
Require Import secp256k1.vst.helper.notations.
Require Import secp256k1.vst.gprog.
Require Import secp256k1.vst.tactics.core.
Require Import secp256k1.vst.tactics.int128.

(* ================================================================= *)
(** ** secp256k1_i128_det -- [r = a*d - b*c]. *)

(** The C body is two calls: [secp256k1_i128_mul(r, a, d)] sets [*r = a*d],
    then [secp256k1_i128_dissip_mul(r, b, c)] subtracts [b*c], leaving
    [*r = a*d - b*c = i128_det a b c d]. The result repr depends only on
    [i128_val], so the final entailment closes by congruence. *)
Lemma body_secp256k1_i128_det :
  semax_body Vprog Gprog
    f_secp256k1_i128_det spec_secp256k1_i128_det.
Proof.
  start_function.
  (* secp256k1_i128_mul(r, a, d): *r = a*d *)
  forward_call (r_ptr, a, d, sh).
  (* secp256k1_i128_dissip_mul(r, b, c): *r -= b*c *)
  forward_call (r_ptr, mul_i64 a d, b, c, sh).
  - (* dissip_mul precondition: a*d - b*c stays in [-2^127, 2^127) *)
    pose proof (i64_range a).
    pose proof (i64_range b).
    pose proof (i64_range c).
    pose proof (i64_range d).
    change (i128_val (mul_i64 a d)) with (i64_val a * i64_val d).
    nia.
  - (* postcondition: the stored value is i128_det a b c d *)
    Intros vret.
    rename H into Hvret.
    entailer!.
    (* i128_val vret = a*d - b*c = i128_val (i128_det a b c d) *)
    assert (Hval : i128_val vret = i128_val (i128_det a b c d)).
    { rewrite Hvret. reflexivity. }
    (* int128_to_val depends only on i128_val, so the reprs agree *)
    apply derives_refl'.
    unfold int128_to_val.
    rewrite Hval.
    reflexivity.
Qed.
