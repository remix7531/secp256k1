(** * Verif_i128_check_pow2: Proof of body_secp256k1_i128_check_pow2 *)
(** Copyright (C) 2026 remix7531
    SPDX-License-Identifier: MIT *)

Require Import secp256k1.vst.base.
Require Import secp256k1.contract.helper.notations.
Require Import secp256k1.contract.gprog.int128.
Require Import secp256k1.tactics.core.
Require Import secp256k1.tactics.int128.

(* ================================================================= *)
(** ** secp256k1_i128_check_pow2 -- [r = sign*2^n]. *)

(** The C body reads the two limbs of [r] and returns a flag that is 1
    exactly when [i128_val r = sign * 2^n].  It branches on [n >= 64]:
    for the high branch it checks [hi == (uint64_t)sign << (n-64)] and
    [lo == 0]; for the low branch it checks [hi == (uint64_t)(sign>>1)]
    and [lo == (uint64_t)sign << n].

    The proof factors three pure helper lemmas (kept local to this file):
    [i128_check_pow2_shl] evaluates a C left-shift of a signed constant,
    [i128_check_pow2_eq64] turns an [Int64.eq] of two in-range values
    into a [Z]-equality, and [i128_check_pow2_decomp] is the injectivity
    of the [(quotient, remainder)] limb decomposition. *)

(** A C [(uint64_t)s << m] left-shift, for [0 <= m < 64], is the bit
    pattern of [s * 2^m]. *)
Lemma i128_check_pow2_shl :
  forall s m,
  0 <= m < 64 ->
  Int64.shl (Int64.repr s) (Int64.repr m) = Int64.repr (s * 2 ^ m).
Proof.
  intros s m Hm.
  rewrite Int64.shl_mul_two_p.
  rewrite Int64.unsigned_repr by rep_lia.
  rewrite two_p_equiv.
  rewrite mul64_repr.
  reflexivity.
Qed.

(** Two values that fit the signed-64 window and whose [Int64.repr]s are
    [Int64.eq] are equal as integers. *)
Lemma i128_check_pow2_eq64 :
  forall a b,
  -2^63 <= a < 2^63 ->
  -2^63 <= b < 2^63 ->
  Int64.eq (Int64.repr a) (Int64.repr b) = true ->
  a = b.
Proof.
  intros a b Ha Hb Heq.
  apply Int64.same_if_eq in Heq.
  apply (f_equal Int64.signed) in Heq.
  rewrite !Int64.signed_repr in Heq
    by (change Int64.min_signed with (-2^63);
        change Int64.max_signed with (2^63 - 1); rep_lia).
  exact Heq.
Qed.

(** A value is determined by its high word [/ 2^64] and low word
    [mod 2^64].  The forward direction is congruence; the backward
    direction is the pure-Z [div_mod_unique] ([theory/arithmetic.v])
    at [M = 2^64], shared with the [i128_eq_var] limb test. *)
Lemma i128_check_pow2_decomp :
  forall a b,
  a = b <-> (a / 2^64 = b / 2^64 /\ a mod 2^64 = b mod 2^64).
Proof.
  intros a b.
  split.
  - intros ->.
    split; reflexivity.
  - intros [Hq Hr].
    apply (div_mod_unique _ _ (2^64)); [lia | exact Hq | exact Hr].
Qed.

Lemma body_secp256k1_i128_check_pow2 :
  semax_body Vprog Gprog
    f_secp256k1_i128_check_pow2 spec_secp256k1_i128_check_pow2.
Proof.
  start_function.
  (* PRE bounds [0 <= n] / [n < 127] stay as auto-named [H] / [H0] (only *)
  (* read by [lia]/[rep_lia], never by name); name the sign disjunction, *)
  (* which the case splits below use explicitly. *)
  rename H1 into Hsign.       (* sign = 1 \/ sign = -1 *)

  (* ===== Stage 0: limb-window bounds (shared by both branches) ===== *)
  (* Bound the high word [/2^64] and low word [mod 2^64] of [r] so the *)
  (* later [Int64.eq]/[Int64.cmpu] reductions stay in-window. *)
  pose proof (i128_range r) as Hvr.
  assert (Hlo : 0 <= i128_val r mod 2^64 < 2^64) by (apply Z.mod_pos_bound; lia).
  assert (Hhi : -2^63 <= i128_val r / 2^64 < 2^63).
  { split.
    - apply Z.div_le_lower_bound; [lia | change (2^63 * 2^64) with (2^127); lia].
    - apply Z.div_lt_upper_bound; [lia | change (2^63 * 2^64) with (2^127); lia]. }

  (* ===== Stage 1: outer if (n >= 64) ===== *)
  (* Both branches converge on the same join postcondition, which pins  *)
  (* [_t'1] to the spec flag; the third subgoal then just returns it.    *)
  forward_if (PROP () LOCAL (temp _t'1 (Vint (Int.repr
    (if Z.eq_dec (i128_val r) (sign * 2^n) then 1 else 0)))) SEP (i128_at sh r_ptr r)).

  - (* ===== Stage 2a: high branch (n >= 64) ===== *)
    (* Here [sign * 2^n] lives entirely in the high limb, so the flag is *)
    (* [hi == sign << (n-64)] conjoined with [lo == 0].                  *)
    forward. (* _t'4 = r->hi *)
    forward_if (PROP () LOCAL (temp _t'1 (Vint (Int.repr
      (if Z.eq_dec (i128_val r) (sign * 2^n) then 1 else 0)))) SEP (i128_at sh r_ptr r)).
    { (* shift-amount typecheck: n - 64 < 64 *)
      entailer!.
      unfold Int64.iwordsize'.
      rewrite Int.unsigned_repr by rep_lia.
      rep_lia. }
    + (* branch: high/then -- hi == sign << (n-64); flag is [lo == 0] *)
      forward. (* _t'5 = r->lo *)
      forward. (* _t'1 = (_t'5 == 0) *)
      forward. (* _t'1 = (tint) _t'1 *)
      entailer!.
      rename H2 into Hhi_eq.    (* hi-word [Int64.eq] test succeeded *)
      f_equal.
      f_equal.
      (* extract the [Z]-level hi = sign * 2^(n-64) from the limb test *)
      replace (let (q, _) := Z.div_eucl (i128_val r) (Z.pow_pos 2 64) in q)
        with (i128_val r / 2^64) in Hhi_eq by reflexivity.
      rewrite Int.unsigned_repr in Hhi_eq by rep_lia.
      rewrite i128_check_pow2_shl in Hhi_eq by lia.
      (* side goal: sign * 2^(n-64) stays inside the signed-64 window *)
      assert (Hexp_bnd : - 2 ^ 63 <= sign * 2 ^ (n - 64) < 2 ^ 63).
      { assert (0 <= 2^(n-64) <= 2^62)
          by (split; [apply Z.pow_nonneg; lia | apply Z.pow_le_mono_r; lia]).
        destruct Hsign; subst sign; change (2^63) with (2 * 2^62); nia. }
      apply (i128_check_pow2_eq64 _ _ Hhi Hexp_bnd) in Hhi_eq.
      (* with the hi word fixed, the spec equality reduces to [lo = 0] *)
      unfold Int64.cmpu.
      unfold Int64.eq.
      rewrite !Int64.unsigned_repr by (change Int64.max_unsigned with (2^64-1); rep_lia).
      assert (Hpow : sign * 2^n = (sign * 2^(n - 64)) * 2^64).
      { rewrite <- Z.mul_assoc.
        rewrite <- Z.pow_add_r by lia.
        f_equal.
        f_equal.
        lia. }
      assert (Hequiv : i128_val r = sign * 2^n <-> i128_val r mod 2^64 = 0).
      { rewrite (i128_check_pow2_decomp (i128_val r) (sign * 2^n)).
        rewrite Hpow.
        rewrite Z.div_mul by lia.
        rewrite Z.mod_mul by lia.
        rewrite Hhi_eq.
        split.
        - intros [_ Hm]. exact Hm.
        - intros Hm. split; [reflexivity | exact Hm]. }
      (* the C [lo == 0] test and the spec flag agree on every case *)
      destruct (Z.eq_dec (i128_val r) (sign * 2 ^ n)) as [He|Hne];
        destruct (zeq (i128_val r mod 2^64) 0) as [Hz|Hnz];
        simpl;
        try reflexivity;
        [ apply Hequiv in He; contradiction | apply Hequiv in Hz; contradiction ].
    + (* branch: high/else -- hi <> sign << (n-64); flag is 0 *)
      forward. (* _t'1 = 0 *)
      entailer!.
      rename H2 into Hhi_neq.   (* hi-word [Int64.eq] test failed *)
      replace (let (q, _) := Z.div_eucl (i128_val r) (Z.pow_pos 2 64) in q)
        with (i128_val r / 2^64) in Hhi_neq by reflexivity.
      rewrite Int.unsigned_repr in Hhi_neq by rep_lia.
      rewrite i128_check_pow2_shl in Hhi_neq by lia.
      destruct (Z.eq_dec (i128_val r) (sign * 2 ^ n)) as [He|Hne].
      2: reflexivity.
      (* if [r = sign*2^n] then its hi word *is* sign << (n-64): absurd *)
      exfalso.
      apply Hhi_neq.
      f_equal.
      assert (Hpow : sign * 2^n = (sign * 2^(n - 64)) * 2^64).
      { rewrite <- Z.mul_assoc.
        rewrite <- Z.pow_add_r by lia.
        f_equal.
        f_equal.
        lia. }
      rewrite He.
      rewrite Hpow.
      rewrite Z.div_mul by lia.
      reflexivity.

  - (* ===== Stage 2b: low branch (n < 64) ===== *)
    (* Here [sign * 2^n] splits across both limbs: the expected hi word  *)
    (* is [sign>>1] (0 for sign=1, -1 for sign=-1, i.e. sign/2) and the  *)
    (* expected lo word is [sign << n].                                  *)
    forward. (* _t'2 = r->hi *)
    forward_if (PROP () LOCAL (temp _t'1 (Vint (Int.repr
      (if Z.eq_dec (i128_val r) (sign * 2^n) then 1 else 0)))) SEP (i128_at sh r_ptr r)).
    + (* branch: low/then -- hi == sign>>1; flag is [lo == sign << n] *)
      forward. (* _t'3 = r->lo *)
      forward. (* _t'1 = (_t'3 == sign << n) *)
      forward. (* _t'1 = (tint) _t'1 *)
      entailer!.
      rename H2 into Hhi_eq.    (* hi-word [Int64.eq] test succeeded *)
      f_equal.
      f_equal.
      (* extract the [Z]-level hi = sign / 2 from the hi-word test *)
      replace (let (q, _) := Z.div_eucl (i128_val r) (Z.pow_pos 2 64) in q)
        with (i128_val r / 2^64) in Hhi_eq by reflexivity.
      assert (Hsr : Int.signed (Int.shr (Int.repr sign) (Int.repr 1)) = sign / 2)
        by (destruct Hsign; subst sign; reflexivity).
      rewrite Hsr in Hhi_eq.
      (* side goal: the expected hi limb [sign / 2] is in the signed-64 window *)
      assert (Hhalf_bnd : - 2 ^ 63 <= sign / 2 < 2 ^ 63)
        by (destruct Hsign; subst sign; cbn; rep_lia).
      apply (i128_check_pow2_eq64 _ _ Hhi Hhalf_bnd) in Hhi_eq.
      (* the expected hi limb of [sign * 2^n] is exactly [sign / 2] *)
      assert (Hq : sign * 2^n / 2^64 = sign / 2).
      { destruct Hsign; subst sign.
        - (* sign = 1: 2^n < 2^64, so the hi word is 0 = 1/2 *)
          rewrite Z.mul_1_l.
          apply Z.div_small.
          split; [apply Z.pow_nonneg; lia | apply Z.pow_lt_mono_r; lia].
        - (* sign = -1: -2^n in (-2^64, 0), so the hi word is -1 *)
          replace (-1 * 2^n) with (- (2^n)) by ring.
          rewrite Z.div_opp_l_nz.
          + rewrite Z.div_small.
            * reflexivity.
            * split; [apply Z.pow_nonneg; lia | apply Z.pow_lt_mono_r; lia].
          + lia.
          + rewrite Z.mod_small.
            * apply Z.pow_nonzero; lia.
            * split; [apply Z.pow_nonneg; lia | apply Z.pow_lt_mono_r; lia]. }
      (* with the hi word fixed, the spec equality reduces to the lo test *)
      rewrite i128_check_pow2_shl by lia.
      unfold Int64.cmpu.
      unfold Int64.eq.
      rewrite !Int64.unsigned_repr_eq.
      change Int64.modulus with (2^64).
      rewrite (Z.mod_small (i128_val r mod 2^64) (2^64)) by lia.
      assert (Hequiv : i128_val r = sign * 2^n <-> i128_val r mod 2^64 = sign * 2^n mod 2^64).
      { rewrite (i128_check_pow2_decomp (i128_val r) (sign * 2^n)).
        rewrite Hq, Hhi_eq.
        split.
        - intros [_ Hm]. exact Hm.
        - intros Hm. split; [reflexivity | exact Hm]. }
      (* the C [lo == sign<<n] test and the spec flag agree on every case *)
      destruct (Z.eq_dec (i128_val r) (sign * 2 ^ n)) as [He|Hne];
        destruct (zeq (i128_val r mod 2^64) (sign * 2^n mod 2^64)) as [Hz|Hnz];
        simpl;
        try reflexivity;
        [ apply Hequiv in He; contradiction | apply Hequiv in Hz; contradiction ].
    + (* branch: low/else -- hi <> sign>>1; flag is 0 *)
      forward. (* _t'1 = 0 *)
      entailer!.
      rename H2 into Hhi_neq.   (* hi-word [Int64.eq] test failed *)
      replace (let (q, _) := Z.div_eucl (i128_val r) (Z.pow_pos 2 64) in q)
        with (i128_val r / 2^64) in Hhi_neq by reflexivity.
      assert (Hsr : Int.signed (Int.shr (Int.repr sign) (Int.repr 1)) = sign / 2)
        by (destruct Hsign; subst sign; reflexivity).
      rewrite Hsr in Hhi_neq.
      assert (Hq : sign * 2^n / 2^64 = sign / 2).
      { destruct Hsign; subst sign.
        - (* sign = 1: 2^n < 2^64, so the hi word is 0 = 1/2 *)
          rewrite Z.mul_1_l.
          apply Z.div_small.
          split; [apply Z.pow_nonneg; lia | apply Z.pow_lt_mono_r; lia].
        - (* sign = -1: -2^n in (-2^64, 0), so the hi word is -1 *)
          replace (-1 * 2^n) with (- (2^n)) by ring.
          rewrite Z.div_opp_l_nz.
          + rewrite Z.div_small.
            * reflexivity.
            * split; [apply Z.pow_nonneg; lia | apply Z.pow_lt_mono_r; lia].
          + lia.
          + rewrite Z.mod_small.
            * apply Z.pow_nonzero; lia.
            * split; [apply Z.pow_nonneg; lia | apply Z.pow_lt_mono_r; lia]. }
      destruct (Z.eq_dec (i128_val r) (sign * 2 ^ n)) as [He|Hne].
      2: reflexivity.
      (* if [r = sign*2^n] then its hi word *is* sign/2: absurd *)
      exfalso.
      apply Hhi_neq.
      f_equal.
      rewrite He.
      rewrite Hq.
      reflexivity.

  - (* ===== Stage 3: return the flag pinned by the join ===== *)
    forward. (* return _t'1 *)
Qed.
