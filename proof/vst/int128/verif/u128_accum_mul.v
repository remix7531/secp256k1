(** * Verif_u128_accum_mul: Proof of body_secp256k1_u128_accum_mul *)
(** Copyright (C) 2026 remix7531
    SPDX-License-Identifier: MIT *)

Require Import secp256k1.vst.base.
Require Import secp256k1.vst.helper.notations.
Require Import secp256k1.vst.gprog.
Require Import secp256k1.vst.tactics.core.
Require Import secp256k1.vst.tactics.int128.

(* ================================================================= *)
(** ** secp256k1_u128_accum_mul -- [r += a * b]. *)

Lemma mk_u128_sum (r : UInt128) (a b : UInt64)
  (H : u128_val r + u64_val a * u64_val b < 2^128) :
  { r' : UInt128 | u128_val r' = u128_val r + u64_val a * u64_val b }.
Proof.
  refine (exist _ (mkUInt128 (u128_val r + u64_val a * u64_val b) _) eq_refl).
  rep_lia.
Defined.

Lemma body_secp256k1_u128_accum_mul:
  semax_body Vprog Gprog
    f_secp256k1_u128_accum_mul spec_secp256k1_u128_accum_mul.
Proof.
  start_function.

  (* lo = secp256k1_umul128(a, b, &hi): the real body returns the low limb and
     writes the high limb to the stack-local [hi]. *)
  forward_call (a, b, v_hi, Tsh).
  Intros result.
  subst result.
  forward. (* lo = _t'1 *)

  (* r->lo += lo *)
  forward. (* _t'5 = r->lo *)
  forward. (* r->lo = _t'5 + lo *)

  (* r->hi += hi + (r->lo < lo) *)
  forward. (* _t'2 = r->hi *)
  forward. (* _t'3 = hi *)
  forward. (* _t'4 = r->lo *)

  (* Provide witness before the final assignment+return (stackframe present). *)
  destruct (mk_u128_sum r a b H) as [r' Hr'].
  Exists r'.
  forward. (* r->hi = _t'2 + (_t'3 + (_t'4 < lo)) *)
  entailer!.

  (* ===== Postcondition: C struct = uint128_to_val of mathematical sum ===== *)
  apply derives_refl'.
  unfold uint128_to_val.
  rewrite Hr'.
  fold_limb.
  do 3 f_equal.
  + (* conjunct 0: limb 0 (low word) *)
    apply Int64.eqm_samerepr.
    apply eqm_of_mod_eq.
    apply limb_add_0; [rep_lia | apply Z.mul_nonneg_nonneg; rep_lia].
  + (* conjunct 1: limb 1 (high word) *)
    apply Int64.eqm_samerepr.
    apply muladd_limb1; [rep_lia | apply Z.mul_nonneg_nonneg; rep_lia].
Qed.
