(** * theory.limb_window: pure-Z 62/64-bit limb window / pack / unpack lemmas. *)
(** Copyright (C) 2026 remix7531
    SPDX-License-Identifier: MIT *)

From Stdlib Require Import ZArith.
From Stdlib Require Import Lia.
From Stdlib Require Import Bool.

Open Scope Z_scope.

(* ================================================================= *)
(** ** Disjoint-bit OR is addition -- [lor_disjoint_is_add]. *)

(** A low piece [lo < 2^k] and a [2^k]-aligned high piece occupy disjoint
    bit ranges, so their bitwise [Z.land] is zero.  Private helper. *)
Lemma land_low_aligned_zero : forall lo hi k,
  0 <= k -> 0 <= lo < 2 ^ k -> 0 <= hi ->
  Z.land lo (hi * 2 ^ k) = 0.
Proof.
  intros lo hi k Hk Hlo Hhi.
  apply Z.bits_inj'.
  intros n Hn.
  rewrite Z.land_spec, Z.bits_0.
  destruct (Z.lt_ge_cases n k) as [Hlt | Hge].
  - (* low bits of the aligned high piece are zero *)
    rewrite (Z.mul_pow2_bits_low _ k n) by lia.
    apply andb_false_r.
  - (* high bits of the bounded low piece are zero *)
    assert (Hlobit : Z.testbit lo n = false).
    { apply Z.testbit_false; [lia |].
      rewrite Z.div_small; [reflexivity |].
      split; [lia | apply Z.lt_le_trans with (2 ^ k); [lia |]].
      apply Z.pow_le_mono_r; lia. }
    rewrite Hlobit.
    apply andb_false_l.
Qed.

(** A low piece [lo < 2^k] [or]-ed with a [2^k]-aligned high piece equals
    their sum, since the two bit ranges are disjoint.  This is the shared
    core of the [Hland]/[Hlor] blocks in [scalar_to_signed62], of
    [comb_lor_disjoint] in [get_bits_var], and of [from62_comb]'s
    [Int64.add_is_or] side-goal in [scalar_from_signed62]. *)
Lemma lor_disjoint_is_add : forall lo hi k,
  0 <= k -> 0 <= lo < 2 ^ k -> 0 <= hi ->
  Z.lor lo (hi * 2 ^ k) = lo + hi * 2 ^ k.
Proof.
  intros lo hi k Hk Hlo Hhi.
  pose proof (Z.add_lor_land lo (hi * 2 ^ k)) as Hadd.
  rewrite (land_low_aligned_zero lo hi k Hk Hlo Hhi) in Hadd.
  lia.
Qed.

(** Reassembling the low [s] bits of [z] with the next [h] bits (aligned at
    [2^s]) and truncating to [2^m] (for [m <= s + h]) recovers [z mod 2^m]:
    the two pieces are the low [s+h] bits of [z], and [2^m] keeps a prefix of
    them.  This is the [ARITH] recombination from [scalar_to_signed62] (there
    with [s2], [h = 64], [m = 62]).  Private helper. *)
Lemma low_aligned_recombine : forall z s h m,
  0 <= z -> 0 <= s -> 0 <= h -> 0 <= m <= s + h ->
  ((z mod 2 ^ s) + (z / 2 ^ s mod 2 ^ h) * 2 ^ s) mod 2 ^ m = z mod 2 ^ m.
Proof.
  intros z s h m Hz Hs Hh Hm.
  assert (Hps : 0 < 2 ^ s) by (apply Z.pow_pos_nonneg; lia).
  assert (Hph : 0 < 2 ^ h) by (apply Z.pow_pos_nonneg; lia).
  (* the two pieces reassemble to the low [s+h] bits of [z] *)
  assert (Hreassemble : (z mod 2 ^ s) + (z / 2 ^ s mod 2 ^ h) * 2 ^ s = z mod 2 ^ (s + h)).
  { rewrite Z.pow_add_r by lia.
    rewrite Z.rem_mul_r by lia.
    ring. }
  rewrite Hreassemble.
  (* truncating those low [s+h] bits to [2^m] keeps [z mod 2^m] *)
  assert (Hdvd : (2 ^ m | 2 ^ (s + h)))
    by (exists (2 ^ (s + h - m)); rewrite <- Z.pow_add_r by lia; f_equal; lia).
  apply (Z.mod_mod_divide z (2 ^ (s + h)) (2 ^ m) Hdvd).
Qed.

(* ================================================================= *)
(** ** Mixed div/mod helper -- [zdiv_mod_mult]. *)

(** Dividing the [b*c]-residue by [b] selects the digit [(a / b) mod c].
    The stdlib analogue of compcert's [Zdiv_mod_mult]; derived from
    [Z.rem_mul_r].  Private helper. *)
Lemma zdiv_mod_mult : forall a b c,
  0 < b -> 0 < c ->
  (a mod (b * c)) / b = (a / b) mod c.
Proof.
  intros a b c Hb Hc.
  rewrite Z.rem_mul_r by lia.
  rewrite (Z.mul_comm b ((a / b) mod c)).
  rewrite Z.div_add by lia.
  rewrite (Z.div_small (a mod b) b) by (apply Z.mod_pos_bound; lia).
  lia.
Qed.

(** Two-factor residue split (high digit times low base plus low residue):
    the stdlib analogue of compcert's [Zmod_recombine], derived from
    [Z.rem_mul_r].  Private helper. *)
Lemma zmod_recombine : forall x a b,
  0 < a -> 0 < b ->
  x mod (a * b) = (x / b) mod a * b + x mod b.
Proof.
  intros x a b Ha Hb.
  rewrite (Z.mul_comm a b).
  rewrite Z.rem_mul_r by lia.
  ring.
Qed.

(* ================================================================= *)
(** ** Single-limb window selection -- [limb_window]. *)

(** Selecting a [c]-bit slice at shift [s] of limb [k] of [z] equals the
    [c]-bit slice at absolute shift [64*k + s].  ([WIN] in
    [get_bits_limb32].) *)
Lemma limb_window : forall z s c k,
  0 <= z -> 0 <= k -> 0 <= s -> 0 < c -> s + c <= 64 ->
  (((z / 2 ^ (64 * k)) mod 2 ^ 64) / 2 ^ s) mod 2 ^ c
  = (z / 2 ^ (64 * k + s)) mod 2 ^ c.
Proof.
  intros z s c k Hz Hk Hs Hc Hsc.
  set (w := z / 2 ^ (64 * k)).
  assert (Hw : 0 <= w)
    by (subst w; apply Z.div_pos; [lia | apply Z.pow_pos_nonneg; lia]).
  assert (Hrhs : z / 2 ^ (64 * k + s) = w / 2 ^ s).
  { subst w.
    rewrite Z.pow_add_r by lia.
    rewrite <- Z.div_div by (try apply Z.pow_nonzero; try apply Z.pow_pos_nonneg; lia).
    reflexivity. }
  rewrite Hrhs.
  assert (Hsplit : 2 ^ 64 = 2 ^ s * 2 ^ (64 - s))
    by (rewrite <- Z.pow_add_r by lia; f_equal; lia).
  rewrite Hsplit.
  rewrite zdiv_mod_mult by (apply Z.pow_pos_nonneg; lia).
  rewrite Z.mod_mod_divide.
  - reflexivity.
  - exists (2 ^ (64 - s - c)).
    rewrite <- Z.pow_add_r by lia.
    f_equal.
    lia.
Qed.

(* ================================================================= *)
(** ** Adjacent-limb folding -- [adjacent_limbs_fold]. *)

(** Two adjacent base-[2^w] limbs [k] and [k+1] of [z] fold to the
    [2*w]-bit slice at shift [w*k].  ([comb_limbs] in [get_bits_var],
    generalized from [w = 64] to arbitrary width [w].) *)
Lemma adjacent_limbs_fold : forall z w k,
  0 <= z -> 0 <= w -> 0 <= k ->
  (z / 2 ^ (w * k)) mod 2 ^ w
  + ((z / 2 ^ (w * (k + 1))) mod 2 ^ w) * 2 ^ w
  = (z / 2 ^ (w * k)) mod 2 ^ (2 * w).
Proof.
  intros z w k Hz Hw Hk.
  set (q := z / 2 ^ (w * k)).
  assert (Hq : 0 <= q)
    by (subst q; apply Z.div_pos; [lia | apply Z.pow_pos_nonneg; lia]).
  assert (Hhi : z / 2 ^ (w * (k + 1)) = q / 2 ^ w).
  { subst q.
    rewrite Z.div_div by (try apply Z.pow_nonzero; try apply Z.pow_pos_nonneg; lia).
    rewrite <- Z.pow_add_r by lia.
    f_equal.
    f_equal.
    lia. }
  rewrite Hhi.
  replace (2 ^ (2 * w)) with (2 ^ w * 2 ^ w)
    by (rewrite <- Z.pow_add_r by lia; f_equal; lia).
  assert (Hpw : 0 < 2 ^ w) by (apply Z.pow_pos_nonneg; lia).
  rewrite Z.rem_mul_r by lia.
  ring.
Qed.

(* ================================================================= *)
(** ** Shifted-pair window -- [shifted_pair_window]. *)

(** The disjoint-add combine [dlo / 2^s + (dhi mod 2^s) * 2^(w - s)] is the
    [w]-bit window at shift [s] of the two adjacent limbs [dlo] (bits
    [[0, w)]) and [dhi] (bits [[w, 2w)]).  ([comb_window64] at [w = 64];
    [from62_zlimb] is a [w = 62] relative.) *)
Lemma shifted_pair_window : forall dlo dhi s w,
  0 <= dlo < 2 ^ w -> 0 <= dhi < 2 ^ w -> 0 < s < w ->
  dlo / 2 ^ s + (dhi mod 2 ^ s) * 2 ^ (w - s)
  = ((dlo + dhi * 2 ^ w) / 2 ^ s) mod 2 ^ w.
Proof.
  intros dlo dhi s w Hlo Hhi Hs.
  assert (Hps : 0 < 2 ^ s) by (apply Z.pow_pos_nonneg; lia).
  assert (Hsplit : 2 ^ w = 2 ^ s * 2 ^ (w - s))
    by (rewrite <- Z.pow_add_r by lia; f_equal; lia).
  (* low piece: [dlo / 2^s < 2^(w-s)] *)
  assert (Hlodiv : 0 <= dlo / 2 ^ s < 2 ^ (w - s)).
  { split; [apply Z.div_pos; lia |].
    apply Z.div_lt_upper_bound; [lia |].
    rewrite <- Hsplit; lia. }
  (* the full shifted pair: [(dlo + dhi*2^w)/2^s = dlo/2^s + dhi*2^(w-s)] *)
  assert (Hshift : (dlo + dhi * 2 ^ w) / 2 ^ s = dlo / 2 ^ s + dhi * 2 ^ (w - s)).
  { rewrite Hsplit.
    rewrite (Z.mul_comm (2 ^ s) (2 ^ (w - s))).
    rewrite Z.mul_assoc.
    rewrite Z.div_add by lia.
    reflexivity. }
  rewrite Hshift.
  (* reduce mod 2^w = 2^s * 2^(w-s): low part stays, [dhi] keeps its low [s] bits *)
  rewrite Hsplit.
  rewrite zmod_recombine by (apply Z.pow_pos_nonneg; lia).
  rewrite Z.div_add by lia.
  rewrite (Z.div_small (dlo / 2 ^ s) (2 ^ (w - s))) by exact Hlodiv.
  rewrite Z.add_0_l.
  rewrite Z.mod_add by (apply Z.pow_nonzero; lia).
  rewrite (Z.mod_small (dlo / 2 ^ s) (2 ^ (w - s))) by exact Hlodiv.
  ring.
Qed.
