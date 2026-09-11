(** * Verif_util_write_be64: Proof of body_secp256k1_write_be64 *)
(** Copyright (C) 2026 remix7531
    SPDX-License-Identifier: MIT *)

Require Import secp256k1.vst.base.
Require secp256k1.specification.
Import specification.Math.
Import specification.Math.integer_bytes.
Require Import secp256k1.vst.helper.notations.
Require Import secp256k1.vst.gprog.
Require Import secp256k1.vst.util.contract.
Require Import secp256k1.vst.tactics.core.

(* ================================================================= *)
(** ** Byte-extraction lemmas -- [zero_ext_8_mod] / [write_be64_byte]. *)

(** A [tulong -> tuchar] store truncates to 8 bits: [Int.zero_ext 8] on
    an [Int.repr] is [Int.repr] of the value taken mod 256. *)
Lemma zero_ext_8_mod : forall v,
  Int.zero_ext 8 (Int.repr v) = Int.repr (v mod 256).
Proof.
  intros v.
  apply Int.same_bits_eq.
  intros i Hi.
  rewrite Int.bits_zero_ext by lia.
  rewrite !Int.testbit_repr by lia.
  change 256 with (2 ^ 8).
  destruct (zlt i 8).
  - rewrite Z.mod_pow2_bits_low by lia.
    reflexivity.
  - rewrite Z.mod_pow2_bits_high by lia.
    reflexivity.
Qed.

(** The value [secp256k1_write_be64] stores at the slot for shift [k]:
    [(uint64_t)(x >> k)] truncated to a byte.  VST presents the loaded
    expression as [Int.zero_ext 8 (Int.repr (Z_mod_modulus (shiftr
    (Z_mod_modulus v) (Z_mod_modulus k))))]; this reduces to the
    big-endian byte [(v / 2^k) mod 256] when [v] is a 64-bit word and
    [0 <= k < 64]. *)
Lemma write_be64_byte : forall v k,
  0 <= v < 2 ^ 64 ->
  0 <= k < 64 ->
  Int.zero_ext 8
    (Int.repr
       (Int64.Z_mod_modulus
          (Z.shiftr (Int64.Z_mod_modulus v) (Int64.Z_mod_modulus k)))) =
  Int.repr ((v / 2 ^ k) mod 256).
Proof.
  intros v k Hv Hk.
  rewrite (Int64.Z_mod_modulus_eq k).
  rewrite (Int64.Z_mod_modulus_eq v).
  change Int64.modulus with (2 ^ 64).
  rewrite (Z.mod_small v (2 ^ 64)) by lia.
  rewrite (Z.mod_small k (2 ^ 64)) by lia.
  rewrite Z.shiftr_div_pow2 by lia.
  rewrite (Int64.Z_mod_modulus_eq (v / 2 ^ k)).
  change Int64.modulus with (2 ^ 64).
  rewrite (Z.mod_small (v / 2 ^ k) (2 ^ 64)).
  - apply zero_ext_8_mod.
  - split.
    + apply Z.div_pos; [lia | apply Z.pow_pos_nonneg; lia].
    + apply Z.div_lt_upper_bound; [apply Z.pow_pos_nonneg; lia |].
      assert (H1 : 1 <= 2 ^ k)
        by (replace 1 with (2 ^ 0) by reflexivity; apply Z.pow_le_mono_r; lia).
      nia.
Qed.

(* ================================================================= *)
(** ** secp256k1_write_be64 -- [p = be_bytes(x)]. *)

(** The C body stores the 8 big-endian bytes of [x]: [p[7] = x],
    [p[6] = x >> 8], ..., [p[0] = x >> 56], each truncated to a
    [tuchar].  After the 8 stores the postcondition reduces to a list
    equality between the [upd_Znth] chain and [bytes_to_val
    (be_bytes_of_Z (u64_val x) 8)]; each slot is discharged by
    [write_be64_byte].

    The [Arguments ... : simpl never] directives are load-bearing:
    without them VST's [forward] for the [(tuchar)(x >> k)] store
    diverges for shift amounts [k >= 24], because the store's
    value-evaluation [simpl]-unfolds [Int64.Z_mod_modulus] (into [_ mod
    2^64]) together with [Z.shiftr] and blows up.  Blocking [simpl] on
    both keeps the stored value in closed form and the stores complete
    in milliseconds. *)
Lemma body_secp256k1_write_be64:
  semax_body Vprog Gprog
    f_secp256k1_write_be64 spec_secp256k1_write_be64.
Proof.
  start_function.
  (* Block the simpl-explosion on the shift/modulus store values. *)
  Arguments Int64.Z_mod_modulus : simpl never.
  Arguments Z.shiftr : simpl never.

  (* ===== Stage 1: the 8 big-endian byte stores ===== *)
  forward.  (* p[7] = x *)
  forward.  (* p[6] = x >> 8 *)
  forward.  (* p[5] = x >> 16 *)
  forward.  (* p[4] = x >> 24 *)
  forward.  (* p[3] = x >> 32 *)
  forward.  (* p[2] = x >> 40 *)
  forward.  (* p[1] = x >> 48 *)
  forward.  (* p[0] = x >> 56 *)

  (* ===== Stage 2: the stored array equals the big-endian encoding ===== *)
  assert (Hr : 0 <= u64_val x < 2 ^ 64) by apply (u64_range x).
  entailer!.
  apply derives_refl'.
  f_equal.

  (* Reduce each stored byte to [(u64_val x / 2^k) mod 256]. *)
  rewrite (write_be64_byte (u64_val x) 8) by lia.
  rewrite (write_be64_byte (u64_val x) 16) by lia.
  rewrite (write_be64_byte (u64_val x) 24) by lia.
  rewrite (write_be64_byte (u64_val x) 32) by lia.
  rewrite (write_be64_byte (u64_val x) 40) by lia.
  rewrite (write_be64_byte (u64_val x) 48) by lia.
  rewrite (write_be64_byte (u64_val x) 56) by lia.
  (* The [p[7] = x] slot has shift [k = 0] (no [Z.shiftr]). *)
  rewrite zero_ext_8_mod.
  rewrite (Int64.Z_mod_modulus_eq (u64_val x)).
  change Int64.modulus with (2 ^ 64).
  rewrite (Z.mod_small (u64_val x) (2 ^ 64)) by lia.

  (* Reduce the big-endian encoding and align the power-of-two divisors. *)
  cbn [integer_bytes.be_bytes_of_Z app].
  unfold bytes_to_val.
  cbn [map].
  change (2 ^ 8) with 256.
  change (2 ^ 16) with 65536.
  change (2 ^ 24) with 16777216.
  change (2 ^ 32) with 4294967296.
  change (2 ^ 40) with 1099511627776.
  change (2 ^ 48) with 281474976710656.
  change (2 ^ 56) with 72057594037927936.
  rewrite !(Z.div_div (u64_val x)) by lia.
  change (256 * 256) with 65536.
  change (65536 * 256) with 16777216.
  change (16777216 * 256) with 4294967296.
  change (4294967296 * 256) with 1099511627776.
  change (1099511627776 * 256) with 281474976710656.
  change (281474976710656 * 256) with 72057594037927936.
  reflexivity.
Qed.
