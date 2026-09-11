(** * theory.integers.bits: generic bit / limb-fold lemmas (pure Z). *)
(** Copyright (C) 2026 remix7531
    SPDX-License-Identifier: MIT *)

(** The designated home for project-authored generic bit/shift/limb lemmas
    (the frozen vendored [theory.extra_math] is never extended).  Founding
    content: the [limb_fold*] family -- folding inline splits
    [(v / B^k) mod B] to [limb B v k] -- for the base-[2^64] word limbs and
    the base-[2^52] field limbs, plus the reverse [limb_at_0].  Hoisted
    verif-side pure cores: the variable-shift limb-extraction family
    ([dls_core] / [limb_shift_combine] / [limb_shift_high_zero], from
    [scalar_shift_limb]) and the 62->64-bit repack identity
    ([from62_zlimb], from [scalar_from_signed62]); the power-of-two
    divisibility / parity facts and the branchless sign-mask vocabulary
    shared by the safegcd bodies ([divide_2_pow] .. [mod62_range]). *)

From Stdlib Require Import ZArith Lia Znumtheory Zpow_facts.
Require Import secp256k1.theory.integers.arithmetic.
Require Import secp256k1.theory.integers.limb_window.

Open Scope Z_scope.

(* ================================================================= *)
(** *** limb fold lemmas

    The C-representation definitions in [Impl_scalar_4x64] use inline
    splits [(x / 2^k) mod 2^64] (matching the spec style).  These
    lemmas fold each inline split to [limb (2^64) x i] so the
    limb-based proof machinery applies.

    A side condition [2^64 = (2^64)^Z.of_nat i] is needed to align
    the exponent shape; we discharge it with [reflexivity] via
    [vm_compute] where needed. *)

Lemma limb_fold0 : forall v, v mod 2^64 = limb (2^64) v 0.
Proof. intros. unfold limb. rewrite Z.pow_0_r, Z.div_1_r. reflexivity. Qed.
Lemma limb_fold1 : forall v, (v / 2^64) mod 2^64 = limb (2^64) v 1.
Proof. intros. unfold limb. rewrite Z.pow_1_r. reflexivity. Qed.
Lemma limb_fold2 : forall v, (v / 2^128) mod 2^64 = limb (2^64) v 2.
Proof. intros. unfold limb. change ((2^64)^Z.of_nat 2) with (2^128). reflexivity. Qed.
Lemma limb_fold3 : forall v, (v / 2^192) mod 2^64 = limb (2^64) v 3.
Proof. intros. unfold limb. change ((2^64)^Z.of_nat 3) with (2^192). reflexivity. Qed.
Lemma limb_fold4 : forall v, (v / 2^256) mod 2^64 = limb (2^64) v 4.
Proof. intros. unfold limb. change ((2^64)^Z.of_nat 4) with (2^256). reflexivity. Qed.
Lemma limb_fold5 : forall v, (v / 2^320) mod 2^64 = limb (2^64) v 5.
Proof. intros. unfold limb. change ((2^64)^Z.of_nat 5) with (2^320). reflexivity. Qed.
Lemma limb_fold6 : forall v, (v / 2^384) mod 2^64 = limb (2^64) v 6.
Proof. intros. unfold limb. change ((2^64)^Z.of_nat 6) with (2^384). reflexivity. Qed.
Lemma limb_fold7 : forall v, (v / 2^448) mod 2^64 = limb (2^64) v 7.
Proof. intros. unfold limb. change ((2^64)^Z.of_nat 7) with (2^448). reflexivity. Qed.

(** Base-generic fold -- the single source the base-[2^64] [limb_fold0..7] and the
    base-[2^52] field [limb_fold52_*] families both specialize.  It is just the
    definition of [limb], stated as a left-to-right rewrite (generalizes the
    family over the base [B], per the field 5x52 work). *)
Lemma limb_fold_gen : forall B v (k : nat),
  (v / B ^ Z.of_nat k) mod B = limb B v k.
Proof. intros. unfold limb. reflexivity. Qed.

(** Base-[2^52] instances for the 5-limb field representation (the [>> 52] / [& M]
    limb extraction of [fe_mul] / [fe_normalize]); same shape as [limb_fold0..7]. *)
Lemma limb_fold52_0 : forall v, v mod 2^52 = limb (2^52) v 0.
Proof. intros. unfold limb. rewrite Z.pow_0_r, Z.div_1_r. reflexivity. Qed.
Lemma limb_fold52_1 : forall v, (v / 2^52) mod 2^52 = limb (2^52) v 1.
Proof. intros. unfold limb. rewrite Z.pow_1_r. reflexivity. Qed.
Lemma limb_fold52_2 : forall v, (v / 2^104) mod 2^52 = limb (2^52) v 2.
Proof. intros. unfold limb. change ((2^52)^Z.of_nat 2) with (2^104). reflexivity. Qed.
Lemma limb_fold52_3 : forall v, (v / 2^156) mod 2^52 = limb (2^52) v 3.
Proof. intros. unfold limb. change ((2^52)^Z.of_nat 3) with (2^156). reflexivity. Qed.
Lemma limb_fold52_4 : forall v, (v / 2^208) mod 2^52 = limb (2^52) v 4.
Proof. intros. unfold limb. change ((2^52)^Z.of_nat 4) with (2^208). reflexivity. Qed.

(* ================================================================= *)
(** Unfold [limb (2^64) v 0] back to [v mod 2^64] -- the reverse of
    [limb_fold0].  Used as a lemma replacement for the [norm_limb_0]
    Ltac. *)
Lemma limb_at_0 : forall v, limb (2^64) v 0 = v mod 2^64.
Proof. intros. symmetry. exact (limb_fold0 v). Qed.

(* ================================================================= *)
(** ** Variable-shift limb extraction -- [dls_core] / [limb_shift_combine]
       / [limb_shift_high_zero].

    The pure-Z core of [secp256k1_scalar_shift_limb] (extract limb [j] of
    [l / 2^shift]): the cross-limb recombination, the limb-aligned
    whole-limb drop, and the vanishing high limb.  Relatives of the
    [theory.limb_window] window family ([shifted_pair_window] /
    [adjacent_limbs_fold]), phrased on explicit divisions / [limb (2^64)]
    as the body proof consumes them. *)

(** The cross-limb recombination identity at the heart of the
    variable-shift limb extraction.  For a uint64 base [B = 2^64] and
    [0 < s < 64], the C expression [(x mod 2^64) >> s | ((x / 2^64) << (64 - s))]
    -- with the high half taken [mod 2^s] by the truncating left shift,
    and the [or] turned into a [+] because the halves are disjoint --
    equals limb 0 of [x / 2^s]. *)
Lemma dls_core : forall x s,
  0 <= x ->
  0 < s < 64 ->
  (x mod 2^64) / 2^s + ((x / 2^64) mod 2^s) * 2^(64-s) = (x / 2^s) mod 2^64.
Proof.
  intros x s Hx Hs.
  (* Setup: factor 2^64 = 2^s * 2^(64-s) both ways. *)
  assert (Hpow : 2^64 = 2^s * 2^(64-s)) by (rewrite <- Z.pow_add_r by lia; f_equal; lia).
  assert (Hpow2 : 2^64 = 2^(64-s) * 2^s) by (rewrite <- Z.pow_add_r by lia; f_equal; lia).

  (* Main: split x / 2^s into its high (limb-shifted) and low parts. *)
  assert (Hxs : x / 2^s = (x / 2^64) * 2^(64-s) + (x mod 2^64) / 2^s).
  {
    rewrite (Z.div_mod x (2^64)) at 1 by lia.
    rewrite Hpow at 1.
    rewrite <- Z.mul_assoc.
    rewrite (Z.mul_comm (2^s)).
    rewrite Z.div_add_l by (apply Z.pow_nonzero; lia).
    ring.
  }
  rewrite Hxs.

  (* the low part fits in the [2^(64-s)] window, so the [+ _ * 2^(64-s)] is the high limb *)
  assert (Hq : 0 <= (x mod 2^64) / 2^s < 2^(64-s)).
  {
    split.
    apply Z.div_pos.
    apply Z.mod_pos_bound; lia.
    apply Z.pow_pos_nonneg; lia.
    apply Z.div_lt_upper_bound.
    apply Z.pow_pos_nonneg; lia.
    rewrite <- Hpow.
    apply Z.mod_pos_bound; lia.
  }

  (* Closeout: take everything mod 2^64; the high contribution distributes out. *)
  rewrite (Z.mul_comm (x / 2^64) (2^(64-s))).
  rewrite Hpow2 at 3.
  rewrite Hpow2 at 4.
  rewrite Z.add_mul_mod_distr_l.
  rewrite <- Hpow2; lia.
  apply Z.div_pos.
  lia.
  rewrite <- Hpow2; apply Z.pow_pos_nonneg; lia.
  apply Z.pow_pos_nonneg; lia.
  exact Hq.
Qed.

(** Limb-aligned shift: when [shiftlow = 0], dividing by [2^(64*sl)] just
    drops [sl] whole limbs, so limb [j] of [M / 2^(64*sl)] is limb [j+sl]
    of [M]. *)
Lemma limb_shift_combine : forall M sl j,
  0 <= M ->
  0 <= sl ->
  limb (2^64) (M / 2^(64*sl)) j = limb (2^64) M (j + Z.to_nat sl).
Proof.
  intros M sl j HM Hsl.
  unfold limb.
  (* collapse the two nested divisions into one division by 2^(64*(j+sl)) *)
  rewrite Nat2Z.inj_add.
  rewrite Z2Nat.id by lia.
  rewrite Z.pow_add_r by lia.
  rewrite Z.pow_mul_r by lia.
  rewrite Z.div_div.
  f_equal.
  f_equal.
  ring.
  apply Z.pow_nonzero; lia.
  apply Z.pow_pos_nonneg; lia.
Qed.

(** High limbs vanish: if [M < 2^k] and the limb window [[64*j, ..)] of
    [M / 2^shift] lies at or above bit [k], the limb is 0.  (The shifted
    generalization of the bounded-value [limb_high_zero] exported by the
    automation layer, hence the distinct name.) *)
Lemma limb_shift_high_zero : forall M k shift j,
  0 <= M ->
  M < 2^k ->
  0 <= shift ->
  k <= shift + 64 * Z.of_nat j ->
  limb (2^64) (M / 2^shift) j = 0.
Proof.
  intros M k shift j HM Hk Hs Hkj.
  unfold limb.
  (* merge the divisions into one division by 2^(shift + 64*j) *)
  rewrite Z.div_div.
  rewrite <- Z.pow_mul_r by lia.
  rewrite <- Z.pow_add_r by lia.

  (* the divisor already exceeds M, so the quotient is 0 *)
  assert (Hz : M / 2^(shift + 64 * Z.of_nat j) = 0).
  {
    apply Z.div_small.
    split; [lia | ].
    apply Z.lt_le_trans with (2^k); [lia | ].
    apply Z.pow_le_mono_r; lia.
  }
  rewrite Hz.
  reflexivity.
  apply Z.pow_nonzero; lia.
  apply Z.pow_pos_nonneg; lia.
Qed.

(* ================================================================= *)
(** ** 62->64-bit repack -- [from62_zlimb]. *)

(** The pure-[Z] limb identity of [secp256k1_scalar_from_signed62]:
    combining limb 0 of [z] (shifted down by [c]) with the wrap-in of
    limb 1 of [z] reconstructs the [64]-bit slice [(z / 2^c) mod 2^64].
    Instantiated with [z = x / 2^(62*i)] and [c = 2*i] to discharge each
    of the four scalar limbs.  (A [w = 62] relative of
    [shifted_pair_window].) *)
Lemma from62_zlimb : forall z c, 0 <= z -> 0 <= c <= 6 ->
  (z mod 2 ^ 62) / 2 ^ c
  + (((z / 2 ^ 62) mod 2 ^ 62) mod 2 ^ (c + 2)) * 2 ^ (62 - c)
  = (z / 2 ^ c) mod 2 ^ 64.
Proof.
  intros z c Hz Hc.
  assert (Hdvd : (2 ^ (c + 2) | 2 ^ 62))
    by (exists (2 ^ (60 - c)); rewrite <- Z.pow_add_r by lia; f_equal; lia).
  rewrite (Z.mod_mod_divide (z / 2 ^ 62) (2 ^ 62) (2 ^ (c + 2))) by exact Hdvd.
  assert (Hpc : 2 ^ c <> 0) by (apply Z.pow_nonzero; lia).
  assert (Hlobd : 0 <= (z mod 2 ^ 62) / 2 ^ c < 2 ^ (62 - c)).
  { split; [apply Z.div_pos; [apply Z.mod_pos_bound; apply Z.pow_pos_nonneg; lia | lia] |].
    apply Z.div_lt_upper_bound; [lia |].
    rewrite <- Z.pow_add_r by lia.
    replace (c + (62 - c)) with 62 by lia.
    apply Z.mod_pos_bound; apply Z.pow_pos_nonneg; lia. }
  (* [z / 2^c] splits into the same low/high pieces (over [Z], no truncation). *)
  assert (Hzc : z / 2 ^ c = (z mod 2 ^ 62) / 2 ^ c + (z / 2 ^ 62) * 2 ^ (62 - c)).
  { rewrite (Z_div_mod_eq_full z (2 ^ 62)) at 1.
    replace (2 ^ 62) with (2 ^ c * 2 ^ (62 - c)) at 1
      by (rewrite <- Z.pow_add_r by lia; f_equal; lia).
    rewrite <- Z.mul_assoc.
    rewrite (Z.mul_comm (2 ^ (62 - c)) (z / 2 ^ 62)).
    rewrite (Z.mul_comm (2 ^ c) (z / 2 ^ 62 * 2 ^ (62 - c))).
    rewrite Z.div_add_l by exact Hpc.
    lia. }
  rewrite Hzc.
  replace (2 ^ 64) with (2 ^ (c + 2) * 2 ^ (62 - c))
    by (rewrite <- Z.pow_add_r by lia; f_equal; lia).
  rewrite (zmod_recombine ((z mod 2 ^ 62) / 2 ^ c + (z / 2 ^ 62) * 2 ^ (62 - c))
                          (2 ^ (c + 2)) (2 ^ (62 - c)))
    by (apply Z.pow_pos_nonneg; lia).
  rewrite Z.div_add by (apply Z.pow_nonzero; lia).
  rewrite (Z.div_small ((z mod 2 ^ 62) / 2 ^ c) (2 ^ (62 - c))) by exact Hlobd.
  rewrite Z.mod_add by (apply Z.pow_nonzero; lia).
  rewrite (Z.mod_small ((z mod 2 ^ 62) / 2 ^ c) (2 ^ (62 - c))) by exact Hlobd.
  rewrite Z.add_0_l.
  ring.
Qed.

(* ================================================================= *)
(** ** Powers of two -- [divide_2_pow] / [divide_pow2_pow2] / [gcd_odd_pow2_1]. *)

(** Every positive power of two is even.  Used by the [divsteps_59] parity
    bridge to weaken a [2^k] congruence to a congruence mod [2]. *)
Lemma divide_2_pow : forall k, 1 <= k -> (2 | 2 ^ k).
Proof.
  intros k Hk.
  replace k with (1 + (k - 1)) by lia.
  rewrite Z.pow_add_r by lia.
  apply Z.divide_factor_l.
Qed.

(** A power of two divides every larger power of two.  Instantiated at
    [k = 64] (via [change Int64.modulus with (2^64)]) to weaken a word-level
    congruence to the [2^(64-j)] window the divstep invariant tracks. *)
Lemma divide_pow2_pow2 : forall j k, 0 <= j <= k -> (2 ^ j | 2 ^ k).
Proof.
  intros j k Hjk.
  exists (2 ^ (k - j)).
  rewrite <- Z.pow_add_r by lia.
  f_equal.
  lia.
Qed.

(** An odd number is coprime to every power of two -- the invertibility of
    [2^a] modulo an odd modulus that the variable-time divsteps body relies
    on. *)
Lemma gcd_odd_pow2_1 : forall z a, Zodd z -> 0 <= a -> Z.gcd z (2 ^ a) = 1.
Proof.
  intros z a Hz Ha.
  apply Zgcd_1_rel_prime.
  apply Zpow_facts.rel_prime_Zpower_r.

  - (* side: the exponent is nonnegative *)
    lia.
  - apply rel_prime_mod_rev.

    + (* side: the modulus 2 is positive *)
      lia.
    + rewrite Zmod_odd.
      replace (Z.odd z) with true.
      * apply rel_prime_1.
      * symmetry.
        apply Zodd_bool_iff.
        assumption.
Qed.

(* ================================================================= *)
(** ** Branchless sign-mask vocabulary -- [shiftr_sign_mask_eq] .. [mod62_range]. *)

(** The pure-[Z] half of the constant-time masking idiom [mask = x >> 63]:
    once the shift is known to land in [[-1, 0]] it IS the sign of [a].
    (The [Int64] realization is [vst.integers.Int64_shr_sign_mask].) *)
Lemma shiftr_sign_mask_eq : forall a n, 0 <= n -> -1 <= Z.shiftr a n <= 0 ->
  Z.shiftr a n = if a <? 0 then -1 else 0.
Proof.
  intros a n Hn Hb.
  destruct (Z.ltb_spec a 0).
  - (* branch: a < 0 -- the shift is negative, hence -1 *)
    assert (Z.shiftr a n < 0) by (rewrite Z.shiftr_neg; assumption).
    lia.
  - (* branch: 0 <= a -- the shift is nonnegative, hence 0 *)
    assert (0 <= Z.shiftr a n) by (rewrite Z.shiftr_nonneg; assumption).
    lia.
Qed.

(** [x & mask] selects [x] when [mask = -1], else [0]. *)
Lemma land_sign_mask_eq : forall (b : bool) x, Z.land x (if b then -1 else 0) = if b then x else 0.
Proof.
  intros [|] x.
  - (* branch: mask = -1 -- [land] with all ones is the identity *)
    rewrite Z.land_m1_r.
    reflexivity.
  - (* branch: mask = 0 -- [land] with zero is zero *)
    rewrite Z.land_0_r.
    reflexivity.
Qed.

(** [x ^ mask] is the complement [-x-1] when [mask = -1], else [x]. *)
Lemma lxor_sign_mask_eq : forall (b : bool) x, Z.lxor x (if b then -1 else 0) = if b then - x - 1 else x.
Proof.
  intros [|] x.
  - (* branch: mask = -1 -- [lxor] with all ones is [Z.lnot] *)
    rewrite Z.lxor_m1_r.
    unfold Z.lnot.
    lia.
  - (* branch: mask = 0 -- [lxor] with zero is the identity *)
    rewrite Z.lxor_0_r.
    reflexivity.
Qed.

(** Subtracting the mask fuses the two branches of the [(x ^ mask) - mask]
    conditional negation back into one [if]. *)
Lemma sub_sign_mask_eq : forall (b : bool) x y,
  (if b then x - 1 else y) - (if b then -1 else 0) = if b then x else y.
Proof.
  intros [|] x y; ring.
Qed.

(** The 62-bit window of any [Z] is a 62-bit residue -- the range fact the
    safegcd limb proofs re-pose for every limb. *)
Lemma mod62_range : forall a, 0 <= a mod 2 ^ 62 < 2 ^ 62.
Proof.
  intros a.
  apply Z.mod_pos_bound.
  lia.
Qed.
