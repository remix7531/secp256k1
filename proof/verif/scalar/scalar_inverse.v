(** * verif.scalar.scalar_inverse: body proof for secp256k1_scalar_inverse. *)
(** Copyright (C) 2026 remix7531
    SPDX-License-Identifier: MIT *)

Require Import secp256k1.vst.base.
Require Import secp256k1.contract.impl.modinv.
Require Import secp256k1.contract.scalar.
Require Import secp256k1.contract.gprog.modinv.

(* ================================================================= *)
(** ** secp256k1_scalar_inverse -- constant-time scalar modular inverse. *)

(** [to_signed62] + the constant-time safegcd driver + [from_signed62], yielding
    the modular inverse of [x] mod [N] -- the POST is the model spec
    [is_modular_inverse (scalar_val x) N (scalar_val r)].  Identical to
    inverse_var but through secp256k1_modinv64 (constant-time, no debruijn
    table).  Proves against modinv64's funspec (its body is proved in
    verif/modinv/modinv64.v). *)
Lemma body_secp256k1_scalar_inverse:
  semax_body Vprog Gprog
    f_secp256k1_scalar_inverse spec_secp256k1_scalar_inverse.
Proof.
  start_function.

  (* ===== Setup: derive the safegcd coprimality precondition ===== *)

  (* [secp256k1_N] is prime ([constants.secp256k1_N_prime]), so the safegcd driver's
     coprimality precondition holds for any scalar (x = 0, or x coprime to N). *)
  assert (Hcoprime : types.scalar_val x = 0
                     \/ rel_prime (types.scalar_val x) constants.secp256k1_N).
  { destruct (Z.eq_dec (types.scalar_val x) 0) as [Hx0|Hx0].
    - (* branch: x = 0 -- the left disjunct holds outright *)
      left.
      exact Hx0.
    - (* branch: x <> 0 -- prime modulus plus 1 <= x < N gives coprimality *)
      right.
      apply rel_prime_le_prime.
      + (* side: N is prime *)
        exact constants.secp256k1_N_prime.
      + (* side: 1 <= scalar_val x < N *)
        pose proof (types.scalar_range x).
        lia. }

  (* ===== Driver: to_signed62 -> modinv64 -> from_signed62 ===== *)

  (* secp256k1_scalar_to_signed62(&s, x): repack into 5-limb signed62. *)
  forward_call (v_s, x_ptr, x, Tsh, sh_x).

  (* secp256k1_modinv64(&s, &secp256k1_const_modinfo_scalar): the constant-time
     safegcd driver, replacing *s with mod_inv (scalar_val x) N. No debruijn. *)
  forward_call (types.scalar_val x, constants.secp256k1_N, v_s,
                gv _secp256k1_const_modinfo_scalar, Tsh, sh_modinfo).
  { (* driver PRE: N odd, x in range, 1 < N < 2^256 (coprimality is in H). *)
    split3.
    - (* PRE 0: N is odd -- N = 2 * N_H + 1 *)
      exists constants.secp256k1_N_H.
      rewrite constants.secp256k1_N_as_2H.
      ring.
    - (* PRE 1: 0 <= scalar_val x < N *)
      apply (types.scalar_range x).
    - (* PRE 2: 1 < N < 2^256 *)
      unfold constants.secp256k1_N.
      lia.
  }

  (* the driver POST is the model spec [is_modular_inverse] on the result value
     [rv], not the opaque [mod_inv] term. *)
  Intros rv.

  (* split it into the range / zero / coprime-case facts the proof uses. *)
  destruct H as (Hbnd & Hzero & Hinv).

  (* secp256k1_scalar_from_signed62(r, &s): repack the reduced result [rv]
     (its range [0 <= rv < N] discharges the PRE). *)
  forward_call (r_ptr, v_s, rv, sh_r, Tsh).
  Intros vret.

  (* ===== Postcondition: is_modular_inverse (scalar_val x) N (scalar_val r) ===== *)

  (* [entailer!!] rewrites the driver's result properties (range, 0->0,
     coprime-case identity) onto [scalar_val vret]. *)
  Exists vret.
  entailer!!.

  (* those three facts are exactly the conjuncts of the model spec. *)
  unfold modinv.is_modular_inverse.
  split3.
  - (* conjunct 0: 0 <= scalar_val r < N *)
    exact Hbnd.
  - (* conjunct 1: x = 0 -> r = 0 *)
    exact Hzero.
  - (* conjunct 2: coprime x -> x * r = 1 mod N *)
    exact Hinv.
Qed.
