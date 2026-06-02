(** * Verif_i128_eq_var: Proof of body_secp256k1_i128_eq_var *)
(** Copyright (C) 2026 remix7531
    SPDX-License-Identifier: MIT *)

Require Import secp256k1.vst.base.
Require Import secp256k1.contract.helper.notations.
Require Import secp256k1.contract.gprog.int128.
Require Import secp256k1.tactics.core.
Require Import secp256k1.tactics.int128.

(* ================================================================= *)
(** ** secp256k1_i128_eq_var -- [a = b]. *)

(** A 128-bit value is determined by its (low limb, high word) pair: if
    two integers agree on both [_ / 2^64] and [_ mod 2^64] they are equal.
    The C code first compares the high words (signed [==]) and only on a
    match compares the low words (unsigned [==]); the proof mirrors that as
    a [forward_if] with a then/else/join split.  The pure core
    ([div_mod_unique]) is the [Z.div_mod] identity in [theory/arithmetic.v],
    used here at [M = 2^64]; it is shared with the [i128_check_pow2] limb
    test. *)

Lemma body_secp256k1_i128_eq_var :
  semax_body Vprog Gprog
    f_secp256k1_i128_eq_var spec_secp256k1_i128_eq_var.
Proof.
  start_function.

  (* ===== Phase 1: load both high words and branch on their equality ===== *)

  forward. (* _t'2 = a->hi *)
  forward. (* _t'3 = b->hi *)

  (* C: if (_t'2 == _t'3).  The two branches reconverge on the value of the
     boolean result temp _t'1, which is the spec's [if i128_val a = i128_val b]. *)
  forward_if (temp _t'1
    (Vint (Int.repr (if Z.eq_dec (i128_val a) (i128_val b) then 1 else 0)))).
  - (* ===== Then branch: high words agree; decide equality on the low words ===== *)
    rename H into Hhi_eq.    (* _t'2 == _t'3 succeeded: the high reprs are equal *)
    forward. (* _t'4 = a->lo *)
    forward. (* _t'5 = b->lo *)
    forward. (* _t'1 = (tbool) (_t'4 == _t'5) *)
    entailer!.

    (* Normalise the high-word equality from VST's [Int64.eq .. = true] form
       (with the raw [Z.div_eucl] / [Z.pow_pos 2 64]) to plain [_ / 2^64]. *)
    apply Int64.same_if_eq in Hhi_eq.
    change (Z.pow_pos 2 64) with (2^64) in Hhi_eq.
    fold (Z.div (i128_val a) (2^64)) in Hhi_eq.
    fold (Z.div (i128_val b) (2^64)) in Hhi_eq.

    (* Both high words live in signed-64 range, so equal [Int64.repr] forces
       equal [Z]: lift [Hhi_eq] across [repr] to a Z-level equality of quotients. *)
    assert (Hhi : i128_val a / 2^64 = i128_val b / 2^64).
    { apply repr_inj_signed64.
      - (* a's high word is within [Int64.min_signed, Int64.max_signed] *)
        pose proof (i128_range a).
        change Int64.min_signed with (-2^63).
        change Int64.max_signed with (2^63 - 1).
        split.
        + apply Z.div_le_lower_bound; lia.
        + apply Z.lt_le_pred.
          apply Z.div_lt_upper_bound; lia.
      - (* b's high word is within the same range (symmetric to a) *)
        pose proof (i128_range b).
        change Int64.min_signed with (-2^63).
        change Int64.max_signed with (2^63 - 1).
        split.
        + apply Z.div_le_lower_bound; lia.
        + apply Z.lt_le_pred.
          apply Z.div_lt_upper_bound; lia.
      - exact Hhi_eq. }

    clear Hhi_eq.    (* superseded by the Z-level [Hhi]; drop the repr form *)
    (* The low words are in unsigned-64 range, so the C unsigned [==] reduces
       to [zeq] on the residues; case-split on whether the residues agree. *)
    unfold Int64.cmpu.
    rewrite eq64_repr_zeq.
    { unfold zeq.
      destruct (Z.eq_dec (i128_val a mod 2^64) (i128_val b mod 2^64)) as [Hlo|Hlo].
      - (* Low words agree.  Equal quotients ([Hhi]) and equal residues ([Hlo])
           pin down the value (div_mod_unique), so both sides are 1. *)
        destruct (Z.eq_dec (i128_val a) (i128_val b)) as [Heq|Hneq].
        + reflexivity.
        + exfalso.
          apply Hneq.
          apply (div_mod_unique _ _ (2^64)); [lia | assumption | assumption].
      - (* Low words differ, so the values differ; both sides are 0. *)
        destruct (Z.eq_dec (i128_val a) (i128_val b)) as [Heq|Hneq].
        + exfalso.
          apply Hlo.
          rewrite Heq.
          reflexivity.
        + reflexivity. }
    (* side condition: a's residue is a valid [Int64.repr] argument *)
    { pose proof (Z.mod_pos_bound (i128_val a) (2^64) ltac:(lia)).
      change Int64.max_unsigned with (2^64 - 1).
      lia. }
    (* side condition: b's residue is a valid [Int64.repr] argument *)
    { pose proof (Z.mod_pos_bound (i128_val b) (2^64) ltac:(lia)).
      change Int64.max_unsigned with (2^64 - 1).
      lia. }
  - (* ===== Else branch: high words differ, so the values differ; result is 0 ===== *)
    rename H into Hhi_neq.    (* _t'2 == _t'3 failed: the high reprs differ *)
    forward. (* _t'1 = 0 *)
    entailer!.

    (* Equal values would force equal high-word reprs, contradicting [Hhi_neq]. *)
    destruct (Z.eq_dec (i128_val a) (i128_val b)) as [Heq|Hneq].
    + exfalso.
      apply Hhi_neq.
      rewrite Heq.
      reflexivity.
    + reflexivity.
  - (* ===== Join: return the boolean result computed by both branches ===== *)
    forward. (* return _t'1 *)
Qed.
