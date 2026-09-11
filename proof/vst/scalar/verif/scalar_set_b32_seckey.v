(** * Verif_scalar_set_b32_seckey: Proof of body_secp256k1_scalar_set_b32_seckey *)
(** Copyright (C) 2026 remix7531
    SPDX-License-Identifier: MIT *)

Require Import secp256k1.vst.base.
Require Import secp256k1.vst.helper.notations.
Require Import secp256k1.vst.gprog.
Require secp256k1.specification.
Import specification.Math.
Import specification.Math.integer_bytes.
Require Import secp256k1.vst.tactics.core.
Require Import secp256k1.vst.tactics.int128.
Require Import secp256k1.vst.tactics.scalar.

(* ================================================================= *)
(** ** secp256k1_scalar_set_b32_seckey -- [r = bytes mod N], returns valid-key flag. *)

(** The nonnegativity of a big-endian decode ([Z_of_be_bytes_nonneg])
    lives in [Math.integer_bytes], next to the [Z_of_be_bytes] definition. *)

Lemma body_secp256k1_scalar_set_b32_seckey:
  semax_body Vprog Gprog
    f_secp256k1_scalar_set_b32_seckey spec_secp256k1_scalar_set_b32_seckey.
Proof.
  start_function.

  (* ===== Phase 1: walk the C body ===== *)

  (* secp256k1_scalar_set_b32(r, bin, &overflow) *)
  forward_call (r_ptr, bin_ptr, v_overflow, bs, sh_r, sh_b, Tsh).
  Intros r'.
  rename H1 into Hr'.
  (* t'1 = secp256k1_scalar_is_zero(r) *)
  forward_call (r_ptr, r', sh_r).
  (* t'2 = overflow *)
  forward.
  (* return (!t'2) & (!t'1) *)
  forward.

  (* ===== Phase 2: supply the resulting scalar ===== *)

  Exists r'.
  entailer!.

  (* ===== Phase 3: the return value matches the spec ===== *)

  (* Z_of_be_bytes bs is nonnegative, so [mod N] is well behaved below N. *)
  assert (Hv : 0 <= Z_of_be_bytes bs).
  { apply Z_of_be_bytes_nonneg; assumption. }
  pose proof (scalar_range r') as Hrng.
  f_equal.
  f_equal.
  destruct (Z_lt_dec (Z_of_be_bytes bs) secp256k1_N) as [Hlt|Hlt].
  - (* No overflow: r' = (Z_of_be_bytes bs) mod N = Z_of_be_bytes bs. *)
    assert (Hrv : scalar_val r' = Z_of_be_bytes bs).
    { rewrite Hr'.
      apply Z.mod_small.
      lia. }
    destruct (Z_le_dec secp256k1_N (Z_of_be_bytes bs)) as [Hov|Hov]; [lia|].
    (* r' = 0 iff Z_of_be_bytes bs = 0; the two ifs agree. *)
    destruct (Z.eq_dec r' 0) as [Hz|Hz];
    destruct (Z.eq_dec (Z_of_be_bytes bs) 0) as [Hvz|Hvz];
    cbn; try reflexivity; lia.
  - (* Overflow: the [!overflow] bit is 0, so the bitwise-and is 0. *)
    destruct (Z_le_dec secp256k1_N (Z_of_be_bytes bs)) as [Hov|Hov]; [|lia].
    cbn.
    reflexivity.
Qed.
