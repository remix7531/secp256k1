(** * Verif_u128_check_bits: Proof of body_secp256k1_u128_check_bits *)
(** Copyright (C) 2026 remix7531
    SPDX-License-Identifier: MIT *)

Require Import secp256k1.vst.base.
Require Import secp256k1.vst.helper.notations.
Require Import secp256k1.vst.gprog.
Require Import secp256k1.vst.tactics.core.
Require Import secp256k1.vst.tactics.int128.

(* ================================================================= *)
(** ** Local arithmetic helpers -- [shru_b2z_eq0] / [hi_lt_iff] (file-local). *)

(** The C compares an unsigned shift against zero: [x >> k == 0].  For
    [x] in [[0, 2^64)] and [0 <= k < 64] the shift is [x / 2^k], so the
    comparison flag is [1] exactly when [x < 2^k].  Both branches of the
    body reduce to this fact (with [x] the [hi] limb and [k = n-64] for
    [n >= 64], and [x] the [lo] limb and [k = n] for [n < 64]). *)
Lemma shru_b2z_eq0 : forall x k,
  0 <= x < 2 ^ 64 ->
  0 <= k < 64 ->
  Z.b2z
    (Int64.cmpu Ceq
       (Int64.shru (Int64.repr x) (Int64.repr k)) (Int64.repr 0)) =
  (if Z_lt_dec x (2 ^ k) then 1 else 0).
Proof.
  intros x k Hx Hk.
  unfold Int64.cmpu.
  rewrite Int64.shru_div_two_p.
  rewrite (Int64.unsigned_repr x) by rep_lia.
  rewrite (Int64.unsigned_repr k) by rep_lia.

  rewrite two_p_correct.
  assert (Hd : 0 <= x / 2 ^ k <= Int64.max_unsigned).
  { split.
    - apply Z.div_pos; lia.
    - assert (x / 2 ^ k <= x) by (apply Z.div_le_upper_bound; [lia | nia]).
      rep_lia. }

  rewrite eq64_repr_zeq by rep_lia.
  unfold zeq.

  destruct (Z.eq_dec (x / 2 ^ k) 0) as [He | He];
    destruct (Z_lt_dec x (2 ^ k)) as [Hl | Hl]; simpl.
  - (* x / 2^k = 0 and x < 2^k: both sides 1 *)
    reflexivity.
  - (* x / 2^k = 0 forces x < 2^k, contradicting x >= 2^k *)
    exfalso; apply Z.div_small_iff in He; lia.
  - (* x < 2^k forces x / 2^k = 0, contradicting x / 2^k <> 0 *)
    exfalso; apply He; apply Z.div_small; lia.
  - (* x / 2^k <> 0 and x >= 2^k: both sides 0 *)
    reflexivity.
Qed.

(** Recombination for the [n >= 64] branch: the [hi] limb of a 128-bit
    value [u] is [(u / 2^64) mod 2^64], and [hi < 2^(m-64)] is equivalent
    to [u < 2^m].  Since [u < 2^128] the inner [mod] is a no-op. *)
Lemma hi_lt_iff : forall u m,
  0 <= u < 2 ^ 128 ->
  64 <= m < 128 ->
  ((u / 2 ^ 64) mod 2 ^ 64 < 2 ^ (m - 64)) <-> (u < 2 ^ m).
Proof.
  intros u m Hu Hm.

  assert (Hdiv : u / 2 ^ 64 < 2 ^ 64).
  { apply Z.div_lt_upper_bound; [lia | ].
    replace (2 ^ 64 * 2 ^ 64) with (2 ^ 128)
      by (rewrite <- Z.pow_add_r; [reflexivity | lia | lia]).
    lia. }
  assert (Hdiv0 : 0 <= u / 2 ^ 64) by (apply Z.div_pos; lia).

  rewrite (Z.mod_small (u / 2 ^ 64) (2 ^ 64)) by lia.
  replace (2 ^ m) with (2 ^ (m - 64) * 2 ^ 64)
    by (rewrite <- Z.pow_add_r by lia; f_equal; lia).

  split; intro Hlt.
  - (* u / 2^64 < 2^(m-64) -> u < 2^(m-64) * 2^64 *)
    pose proof (Z.div_mod u (2 ^ 64) ltac:(lia)) as Hdm.
    pose proof (Z.mod_pos_bound u (2 ^ 64) ltac:(lia)) as Hmb.
    nia.
  - (* u < 2^(m-64) * 2^64 -> u / 2^64 < 2^(m-64) *)
    apply Z.div_lt_upper_bound; [lia | ].
    lia.
Qed.

(* ================================================================= *)
(** ** secp256k1_u128_check_bits -- [r < 2^n]. *)

(** The body branches on [n >= 64]; the returned flag is [1] iff
    [u128_val r < 2^n].  For [n < 64] the C checks [hi = 0 && lo >> n = 0]
    (a short-circuit [&&], compiled as a nested [if]); for [n >= 64] it
    checks [hi >> (n-64) = 0]. *)

Lemma body_secp256k1_u128_check_bits :
  semax_body Vprog Gprog
    f_secp256k1_u128_check_bits spec_secp256k1_u128_check_bits.
Proof.
  start_function.

  (* The whole [if] computes [_t'1]; couple it to the returned flag. *)
  forward_if
    (PROP ()
     LOCAL (temp _t'1
              (Vint (Int.repr (if Z_lt_dec (u128_val r) (2 ^ n) then 1 else 0)));
            temp _r r_ptr; temp _n (Vint (Int.repr n)))
     SEP (u128_at sh r_ptr r)).
  - (* ===== Branch n >= 64: hi >> (n-64) == 0 ===== *)
    forward. (* _t'4 = r->hi *)
    forward. (* _t'1 = (tint)(_t'4 >> (n - 64) == 0) *)
    + (* typecheck: shift amount n - 64 is below the word size *)
      entailer!.
      change (Int.unsigned Int64.iwordsize') with 64.
      rep_lia.
    + (* the returned flag matches [u128_val r < 2^n] *)
      entailer!.
      pose proof (u128_range r) as Hrr.
      f_equal.
      f_equal.

      (* side goals of [shru_b2z_eq0]: the hi limb and the shift amount are in range *)
      assert (Hhi_bnd : 0 <= (u128_val r / 2 ^ 64) mod 2 ^ 64 < 2 ^ 64)
        by (apply Z.mod_pos_bound; lia).
      assert (Hn_bnd : 0 <= n - 64 < 64) by lia.
      rewrite shru_b2z_eq0 by assumption.

      (* both [if]s agree by the hi-limb recombination *)
      destruct (Z_lt_dec ((u128_val r / 2 ^ 64) mod 2 ^ 64) (2 ^ (n - 64)))
        as [Ha | Ha];
        destruct (Z_lt_dec (u128_val r) (2 ^ n)) as [Hb | Hb].
      * reflexivity.
      * exfalso; apply Hb; apply hi_lt_iff; [lia | lia | assumption].
      * exfalso; apply Ha; apply hi_lt_iff; [lia | lia | assumption].
      * reflexivity.
  - (* ===== Branch n < 64: hi == 0 && lo >> n == 0 ===== *)
    forward. (* _t'2 = r->hi *)
    forward_if. (* if (_t'2 == 0) *)
    + (* then: hi == 0, so the result is [lo >> n == 0] *)
      forward. (* _t'3 = r->lo *)
      forward. (* _t'1 = (tbool)(_t'3 >> n == 0) *)
      forward. (* _t'1 = (tint)_t'1 *)
      entailer!.

      (* H2 says the hi limb is zero; unfold the div notation it carries *)
      change (Z.pow_pos 2 64) with (2 ^ 64) in H2.
      change (let (q, _) := Z.div_eucl (u128_val r) (2 ^ 64) in q)
        with (u128_val r / 2 ^ 64) in H2.
      pose proof (u128_range r) as Hrr.

      assert (Hhi0 : (u128_val r / 2 ^ 64) mod 2 ^ 64 = 0).
      { apply (f_equal Int64.unsigned) in H2.
        rewrite Int64.unsigned_repr in H2
          by (split;
              [ apply Z.mod_pos_bound; lia
              | pose proof
                  (Z.mod_pos_bound (u128_val r / 2 ^ 64) (2 ^ 64) ltac:(lia));
                rep_lia ]).
        change (Int64.unsigned Int64.zero) with 0 in H2.
        exact H2. }

      assert (Hdivlt : u128_val r / 2 ^ 64 < 2 ^ 64).
      { apply Z.div_lt_upper_bound; [lia | ].
        replace (2 ^ 64 * 2 ^ 64) with (2 ^ 128)
          by (rewrite <- Z.pow_add_r; [reflexivity | lia | lia]).
        lia. }
      assert (Hdiv0 : 0 <= u128_val r / 2 ^ 64) by (apply Z.div_pos; lia).
      rewrite Z.mod_small in Hhi0 by lia.
      assert (Hsmall : u128_val r < 2 ^ 64)
        by (apply Z.div_small_iff in Hhi0; lia).

      (* hi = 0 means [lo = u128_val r], so [lo >> n == 0 <-> r < 2^n] *)
      rewrite (Z.mod_small (u128_val r) (2 ^ 64)) by lia.
      f_equal.
      f_equal.
      symmetry.
      apply shru_b2z_eq0; lia.
    + (* else: hi <> 0, so [u128_val r >= 2^64 > 2^n] and the result is 0 *)
      forward. (* _t'1 = (tint)0 *)
      entailer!.

      change (Z.pow_pos 2 64) with (2 ^ 64) in H2.
      change (let (q, _) := Z.div_eucl (u128_val r) (2 ^ 64) in q)
        with (u128_val r / 2 ^ 64) in H2.
      pose proof (u128_range r) as Hrr.

      assert (Hdivlt : u128_val r / 2 ^ 64 < 2 ^ 64).
      { apply Z.div_lt_upper_bound; [lia | ].
        replace (2 ^ 64 * 2 ^ 64) with (2 ^ 128)
          by (rewrite <- Z.pow_add_r; [reflexivity | lia | lia]).
        lia. }
      assert (Hdiv0 : 0 <= u128_val r / 2 ^ 64) by (apply Z.div_pos; lia).
      assert (Hbig : u128_val r >= 2 ^ 64).
      { destruct (Z_le_gt_dec (2 ^ 64) (u128_val r)) as [Hle | Hgt]; [lia | ].
        exfalso.
        apply H2.
        rewrite (Z.div_small (u128_val r) (2 ^ 64)) by lia.
        reflexivity. }

      assert (Hpn : 2 ^ n < 2 ^ 64) by (apply Z.pow_lt_mono_r; lia).
      destruct (Z_lt_dec (u128_val r) (2 ^ n)) as [Hlt | Hge]; [lia | reflexivity].
  - (* ===== Join: return the computed flag _t'1 ===== *)
    forward. (* return _t'1 *)
Qed.
