(** * Verif_scalar_is_even: Proof of body_secp256k1_scalar_is_even *)
(** Copyright (C) 2026 remix7531
    SPDX-License-Identifier: MIT *)

Require Import secp256k1.vst.base.
Require Import secp256k1.contract.helper.notations.
Require Import secp256k1.contract.gprog.scalar.
Require Import secp256k1.tactics.core.
Require Import secp256k1.tactics.int128.
Require Import secp256k1.tactics.scalar.

(* ================================================================= *)
(** ** secp256k1_scalar_is_even -- [a even]. *)

(** The C returns [!(a->d[0] & 1)]: 1 iff the low bit of limb 0 is clear.
    After loading limb 0 and returning, the postcondition reduces to a
    pure equality between [Z.b2z (Int64.eq (low bit) 0)] and the spec's
    [if Z.even (scalar_val a) then 1 else 0].  The bridge is the low-bit
    extraction [Z.land (a mod 2^64) 1 = a mod 2] (limb 0 mod 2 = a mod 2,
    since 2 divides 2^64), after which [Zmod_even] decides the parity. *)
Lemma body_secp256k1_scalar_is_even:
  semax_body Vprog Gprog
    f_secp256k1_scalar_is_even spec_secp256k1_scalar_is_even.
Proof.
  start_function.

  (* _t'1 = a->d[0] *)
  forward.

  (* return !(_t'1 & 1) *)
  forward.
  entailer!.

  (* Reduce the C unop/cast cascade to [Z.b2z (Int64.eq (..) 0)]. *)
  unfold scalar_to_val.
  rewrite Znth_0_cons.
  unfold sem_and, sem_unary_operation, sem_notbool, sem_cast_i2i.
  simpl force_val.

  (* Strip the double negation and the [1] cast. *)
  f_equal.
  f_equal.
  rewrite negb_involutive.
  change (Int.signed (Int.repr 1)) with 1.
  change (Z.pow_pos 2 64) with (2^64).

  (* [a->d[0] & 1] is the low bit [a mod 2]; then decide parity. *)
  rewrite and64_repr.
  assert (Hlow : Z.land (a mod 2^64) 1 = a mod 2).
  { change 1 with (Z.ones 1).
    rewrite Z.land_ones by lia.
    change (2^1) with 2.
    apply Z.mod_mod_divide.
    exists (2^63).
    reflexivity. }
  rewrite Hlow.
  rewrite Zmod_even.
  destruct (Z.even a).
  - reflexivity.
  - reflexivity.
Qed.
