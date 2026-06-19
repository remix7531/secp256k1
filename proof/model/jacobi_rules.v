(** * model.jacobi_rules: the Jacobi-symbol rule characterisation. *)
(** Copyright (C) 2026 remix7531
    SPDX-License-Identifier: MIT *)

(** [model.modinv]'s [jacobi_symbol] is an ALGORITHM -- a fuelled binary /
    Euclidean recursion -- so on its own it says nothing a reviewer can check
    against a textbook.  This file supplies the missing meaning:

    - [JacobiRules J] collects the five textbook rules for [(a | n)] plus the
      two base values, as a predicate on an abstract [J];
    - [jacobi_symbol_rules] proves the model's algorithm satisfies them;
    - [jacobi_unique] proves the rules pin down ONE function on the whole
      domain the proof uses ([0 <= a], [0 < n], [n] odd), so satisfying them
      is not a weak property;
    - [jacobi_pm1] records that a coprime numerator gives a sign.

    The C bridge for [secp256k1_jacobi64_maybe_var] is expected to use the
    rules (one per positive-divstep branch), never the fuel recursion; the
    fuel is plumbing and is confined to [jacobi_fuel_stable] and the lemmas
    above it.

    Multiplicativity of the symbol is deliberately absent: the bridge does not
    need it, and it is not proved here.

    Two side conditions differ from the plainest reading of the rules, both
    for good reason and both recorded here for the reviewer:

    - the two-supplement is stated for a numerator already below [n / 2]
      ([0 <= a] and [2 * a < n]).  That is the shape the divstep bridge uses
      (its numerator is always the reduced one), it is what the algorithm
      supports without a periodicity theorem, and it is still strong enough
      for [jacobi_unique];
    - reciprocity is stated WITHOUT a coprimality hypothesis, for all odd
      positive [a] and [n].  It is true in that generality (both sides vanish
      when [gcd(a,n) <> 1]), the algorithm satisfies it in that generality,
      and it is REQUIRED: with coprimality added the rules no longer
      determine [J] (nothing then constrains, say, [J 3 9]) and
      [jacobi_unique] would be false. *)

Require Import ZArith.
Require Import Coq.ZArith.Znumtheory.
Require Import Lia.

Require Import secp256k1.model.modinv.

Open Scope Z_scope.

(* ================================================================= *)
(** ** The two signs -- [eps8] / [eps4]. *)

(** The [(2 | n)] supplement sign: for odd [n] it is [1] when [n] is
    [1] or [7] mod [8] and [-1] when [n] is [3] or [5] mod [8].  The form
    below is literally the branch [jacobi_twos] takes. *)
Definition eps8 (n : Z) : Z :=
  if ((n mod 8 =? 3) || (n mod 8 =? 5))%bool then -1 else 1.

(** The quadratic-reciprocity sign [(-1)^(((a-1)/2)*((n-1)/2))]: [-1] exactly
    when [a] and [n] are both [3] mod [4].  The form below is literally the
    branch [jacobi_loop] takes. *)
Definition eps4 (a n : Z) : Z :=
  if ((a mod 4 =? 3) && (n mod 4 =? 3))%bool then -1 else 1.

(** [eps8] is a sign. *)
Lemma eps8_pm1 : forall n, eps8 n = 1 \/ eps8 n = -1.
Proof.
  intros n.
  unfold eps8.
  destruct ((n mod 8 =? 3) || (n mod 8 =? 5))%bool.
  - right.
    reflexivity.
  - left.
    reflexivity.
Qed.

(** [eps4] is a sign. *)
Lemma eps4_pm1 : forall a n, eps4 a n = 1 \/ eps4 a n = -1.
Proof.
  intros a n.
  unfold eps4.
  destruct ((a mod 4 =? 3) && (n mod 4 =? 3))%bool.
  - right.
    reflexivity.
  - left.
    reflexivity.
Qed.

(** [eps4] is symmetric: the reciprocity sign does not depend on which of the
    two odd numbers is the numerator. *)
Lemma eps4_comm : forall a n, eps4 a n = eps4 n a.
Proof.
  intros a n.
  unfold eps4.
  destruct (a mod 4 =? 3), (n mod 4 =? 3); reflexivity.
Qed.

(** A product of two signs is a sign. *)
Lemma pm1_mul : forall x y,
  (x = 1 \/ x = -1) -> (y = 1 \/ y = -1) -> (x * y = 1 \/ x * y = -1).
Proof.
  intros x y Hx Hy.
  destruct Hx as [Hx | Hx], Hy as [Hy | Hy]; subst; [left | right | right | left]; reflexivity.
Qed.

(** A nonnegative power of a sign is a sign. *)
Lemma pm1_pow : forall x k, 0 <= k -> (x = 1 \/ x = -1) -> (x ^ k = 1 \/ x ^ k = -1).
Proof.
  intros x k Hk Hx.
  pattern k.
  apply natlike_ind; [| | exact Hk].
  - rewrite Z.pow_0_r.
    left.
    reflexivity.
  - intros j Hj IHj.
    rewrite Z.pow_succ_r by exact Hj.
    apply pm1_mul; assumption.
Qed.

(** [jacobi_twos]'s sign branch is multiplication by [eps8 n]. *)
Lemma eps8_flip : forall n s,
  (if ((n mod 8 =? 3) || (n mod 8 =? 5))%bool then - s else s) = eps8 n * s.
Proof.
  intros n s.
  unfold eps8.
  destruct ((n mod 8 =? 3) || (n mod 8 =? 5))%bool; ring.
Qed.

(** [jacobi_loop]'s sign branch is multiplication by [eps4 a n]. *)
Lemma eps4_flip : forall a n s,
  (if ((a mod 4 =? 3) && (n mod 4 =? 3))%bool then - s else s) = eps4 a n * s.
Proof.
  intros a n s.
  unfold eps4.
  destruct ((a mod 4 =? 3) && (n mod 4 =? 3))%bool; ring.
Qed.

(* ================================================================= *)
(** ** Arithmetic plumbing -- two-adic splitting and the Euclid halving. *)

(** Fuelled helper for [two_adic_decomp]: [f] counts down on the value. *)
Lemma two_adic_aux : forall (f : nat) (a : Z),
  0 < a -> a <= Z.of_nat f ->
  exists k a1, 0 <= k /\ 0 < a1 /\ Z.Odd a1 /\ a = 2 ^ k * a1.
Proof.
  induction f as [| f IH].
  - intros a Ha Hf.
    simpl in Hf.
    lia.
  - intros a Ha Hf.
    destruct (Z.Even_or_Odd a) as [Hev | Hod].
    + (* [a] is even: split [a / 2] and put the two back *)
      destruct Hev as [b Hb].
      assert (Hb0 : 0 < b) by lia.
      assert (Hble : b <= Z.of_nat f) by lia.
      destruct (IH b Hb0 Hble) as [k [a1 [Hk [Ha1 [Hodd1 Heq]]]]].
      exists (k + 1), a1.
      split; [lia |].
      split; [lia |].
      split; [assumption |].
      rewrite Hb.
      rewrite Heq.
      rewrite Z.pow_add_r by lia.
      rewrite Z.pow_1_r.
      ring.
    + (* [a] is already odd *)
      exists 0, a.
      split; [lia |].
      split; [lia |].
      split; [assumption |].
      rewrite Z.pow_0_r.
      ring.
Qed.

(** Every positive [a] splits as [2 ^ k * a1] with [a1] odd; both components
    are bounded by [a] (this is the form the fuel bounds need). *)
Lemma two_adic_decomp : forall a, 0 < a ->
  exists k a1, 0 <= k /\ 0 < a1 /\ Z.Odd a1 /\ a = 2 ^ k * a1
               /\ k <= Z.log2 a /\ a1 <= a.
Proof.
  intros a Ha.
  assert (Hf : a <= Z.of_nat (Z.to_nat a)) by (rewrite Z2Nat.id by lia; lia).
  destruct (two_adic_aux (Z.to_nat a) a Ha Hf) as [k [a1 [Hk [Ha1 [Hodd Heq]]]]].
  exists k, a1.
  assert (Hpow : 0 < 2 ^ k) by (apply Z.pow_pos_nonneg; lia).
  assert (Hple : 2 ^ k <= a) by nia.
  split; [assumption |].
  split; [assumption |].
  split; [assumption |].
  split; [assumption |].
  split.
  - rewrite <- (Z.log2_pow2 k) by exact Hk.
    apply Z.log2_le_mono.
    assumption.
  - nia.
Qed.

(** One Euclid step at least halves the numerator: for [0 < b < n] the
    remainder [n mod b] is below [n / 2]. *)
Lemma mod_lt_half : forall n b, 0 < b -> b < n -> 2 * (n mod b) < n.
Proof.
  intros n b Hb Hbn.
  destruct (Z.le_gt_cases (2 * b) n) as [Hle | Hgt].
  - assert (H : n mod b < b) by (apply Z.mod_pos_bound; lia).
    lia.
  - assert (H : n mod b = n - b).
    { replace n with ((n - b) + 1 * b) at 1 by ring.
      rewrite Z_mod_plus_full.
      apply Z.mod_small.
      lia. }

    lia.
Qed.

(** [mod_lt_half] in the [Z.log2] measure the fuel bounds are stated in. *)
Lemma log2_mod_lt : forall n b, 0 < b -> b < n -> Z.log2 (n mod b) + 1 <= Z.log2 n.
Proof.
  intros n b Hb Hbn.
  assert (Hhalf : 2 * (n mod b) < n) by (apply mod_lt_half; lia).
  assert (Hnn : 0 <= n mod b) by (apply Z.mod_pos_bound; lia).
  assert (H2 : Z.log2 2 <= Z.log2 n) by (apply Z.log2_le_mono; lia).
  change (Z.log2 2) with 1 in H2.
  destruct (Z.eq_dec (n mod b) 0) as [Hz | Hz].
  - rewrite Hz.
    change (Z.log2 0) with 0.
    lia.
  - assert (H : Z.log2 (2 * (n mod b)) <= Z.log2 n) by (apply Z.log2_le_mono; lia).
    rewrite Z.log2_double in H by lia.
    lia.
Qed.

(* ================================================================= *)
(** ** The fuelled recursion -- [jacobi_twos] / [jacobi_loop]. *)

(** [jacobi_twos] strips the twos: given fuel at least the two-adic valuation
    [k] of [a], it returns the odd part [a1] together with the accumulated
    [eps8 n ^ k] sign, whatever surplus fuel it was handed. *)
Lemma jacobi_twos_val : forall (f : nat) (k a1 a n s : Z),
  0 <= k -> 0 < a1 -> Z.Odd a1 -> a = 2 ^ k * a1 -> k <= Z.of_nat f ->
  jacobi_twos f a n s = (a1, eps8 n ^ k * s).
Proof.
  induction f as [| f IH].
  - intros k a1 a n s Hk Ha1 Hodd Heq Hf.
    simpl in Hf.
    assert (Hk0 : k = 0) by lia.
    subst k.
    rewrite Z.pow_0_r in Heq.
    rewrite Z.pow_0_r.
    cbn [jacobi_twos].
    f_equal; lia.
  - intros k a1 a n s Hk Ha1 Hodd Heq Hf.
    rewrite Nat2Z.inj_succ in Hf.
    cbn [jacobi_twos].
    destruct (Z.eq_dec k 0) as [Hk0 | Hk0].
    + (* no twos left: [a = a1] is odd, so the [Z.even] test fails *)
      subst k.
      rewrite Z.pow_0_r in Heq.
      assert (Ha : a = a1) by lia.
      rewrite Ha.

      assert (Heven : Z.even a1 = false).
      { destruct (Z.even a1) eqn:E; [| reflexivity].
        exfalso.
        apply Z.even_spec in E.
        destruct E as [x Hx].
        destruct Hodd as [y Hy].
        lia. }

      rewrite Heven.
      rewrite Z.pow_0_r.
      f_equal; lia.
    + (* [a] is even: peel one two, flip by [eps8 n], recurse *)
      assert (Hk2 : 2 ^ k = 2 * 2 ^ (k - 1)).
      { replace k with (Z.succ (k - 1)) at 1 by lia.
        apply Z.pow_succ_r.
        lia. }

      assert (Heven : Z.even a = true).
      { apply Z.even_spec.
        exists (2 ^ (k - 1) * a1).
        rewrite Heq, Hk2.
        ring. }

      rewrite Heven.
      rewrite eps8_flip.

      assert (Hdiv : a / 2 = 2 ^ (k - 1) * a1).
      { rewrite Heq, Hk2.
        replace (2 * 2 ^ (k - 1) * a1) with ((2 ^ (k - 1) * a1) * 2) by ring.
        apply Z.div_mul.
        lia. }

      rewrite Hdiv.
      rewrite (IH (k - 1) a1 (2 ^ (k - 1) * a1) n (eps8 n * s)); [| lia | lia | assumption | reflexivity | lia].

      assert (Hpow : eps8 n ^ k = eps8 n * eps8 n ^ (k - 1)).
      { replace k with (Z.succ (k - 1)) at 1 by lia.
        apply Z.pow_succ_r.
        lia. }

      rewrite Hpow.
      f_equal.
      ring.
Qed.

(** [jacobi_twos] is linear in the sign it carries. *)
Lemma jacobi_twos_scale : forall (f : nat) (a n c s : Z),
  jacobi_twos f a n (c * s) =
  (fst (jacobi_twos f a n s), c * snd (jacobi_twos f a n s)).
Proof.
  induction f as [| f IH].
  - intros a n c s.
    cbn [jacobi_twos fst snd].
    reflexivity.
  - intros a n c s.
    cbn [jacobi_twos].
    destruct (Z.even a).
    + rewrite !eps8_flip.
      replace (eps8 n * (c * s)) with (c * (eps8 n * s)) by ring.
      apply IH.
    + cbn [fst snd].
      reflexivity.
Qed.

(** One [jacobi_loop] round, with the sign branch named [eps4]. *)
Lemma jacobi_loop_S : forall (f : nat) (a n s : Z),
  jacobi_loop (S f) a n s =
  if a =? 0 then (if n =? 1 then s else 0)
  else let '(a1, s1) := jacobi_twos (S f) a n s in
       jacobi_loop f (n mod a1) a1 (eps4 a1 n * s1).
Proof.
  intros f a n s.
  cbn [jacobi_loop].
  destruct (a =? 0).
  - reflexivity.
  - destruct (jacobi_twos (S f) a n s) as [a1 s1].
    rewrite eps4_flip.
    reflexivity.
Qed.

(** [jacobi_loop] is linear in the sign it carries. *)
Lemma jacobi_loop_scale : forall (f : nat) (a n c s : Z),
  jacobi_loop f a n (c * s) = c * jacobi_loop f a n s.
Proof.
  induction f as [| f IH].
  - intros a n c s.
    cbn [jacobi_loop].
    ring.
  - intros a n c s.
    rewrite !jacobi_loop_S.
    destruct (a =? 0).
    + destruct (n =? 1).
      * reflexivity.
      * ring.
    + rewrite (jacobi_twos_scale (S f) a n c s).
      destruct (jacobi_twos (S f) a n s) as [a1 s1].
      cbn [fst snd].
      replace (eps4 a1 n * (c * s1)) with (c * (eps4 a1 n * s1)) by ring.
      apply IH.
Qed.

(** Once the fuel exceeds the measure [Z.log2 a + Z.log2 n] by [2] the loop's
    value stops depending on it.  [m] is any bound on that measure; each
    Euclid round drops it by at least one, because the new modulus is the old
    numerator's odd part and the new numerator is below half the old modulus.
    This is the plumbing that lets the reciprocity proof compare two runs
    started with different fuel. *)
Lemma jacobi_fuel_stable : forall (m f1 f2 : nat) (a n s : Z),
  0 < n -> Z.Odd n -> 0 <= a < n ->
  Z.log2 a + Z.log2 n <= Z.of_nat m ->
  Z.of_nat m + 2 <= Z.of_nat f1 -> Z.of_nat m + 2 <= Z.of_nat f2 ->
  jacobi_loop f1 a n s = jacobi_loop f2 a n s.
Proof.
  induction m as [| m IH].
  - (* measure [0]: [n = 1], hence [a = 0], and both runs return [s] *)
    intros f1 f2 a n s Hn Hodd Ha Hm H1 H2.

    assert (Hln : Z.log2 n = 0).
    { pose proof (Z.log2_nonneg a).
      pose proof (Z.log2_nonneg n).
      lia. }

    apply Z.log2_null in Hln.
    assert (Hn1 : n = 1) by lia.
    assert (Ha0 : a = 0) by lia.
    subst a n.
    destruct f1 as [| f1']; [simpl in H1; lia |].
    destruct f2 as [| f2']; [simpl in H2; lia |].
    rewrite !jacobi_loop_S.
    rewrite !Z.eqb_refl.
    reflexivity.
  - intros f1 f2 a n s Hn Hodd Ha Hm H1 H2.
    destruct f1 as [| f1']; [simpl in H1; lia |].
    destruct f2 as [| f2']; [simpl in H2; lia |].
    rewrite !jacobi_loop_S.
    destruct (a =? 0) eqn:Ea.
    + reflexivity.
    + (* one Euclid round: same odd part, same sign, smaller measure *)
      apply Z.eqb_neq in Ea.
      assert (Hapos : 0 < a) by lia.
      destruct (two_adic_decomp a Hapos)
        as [k [a1 [Hk [Hpos [Hoddp [Heq [Hklog Hle]]]]]]].
      assert (Hlogan : Z.log2 a <= Z.log2 n) by (apply Z.log2_le_mono; lia).
      pose proof (Z.log2_nonneg a) as Hla.
      pose proof (Z.log2_nonneg n) as Hln.
      assert (Hf1 : k <= Z.of_nat (S f1')) by (rewrite Nat2Z.inj_succ; lia).
      assert (Hf2 : k <= Z.of_nat (S f2')) by (rewrite Nat2Z.inj_succ; lia).
      rewrite (jacobi_twos_val (S f1') k a1 a n s Hk Hpos Hoddp Heq Hf1).
      rewrite (jacobi_twos_val (S f2') k a1 a n s Hk Hpos Hoddp Heq Hf2).
      cbn [jacobi_loop].
      assert (Hbnd : 0 <= n mod a1 < a1) by (apply Z.mod_pos_bound; lia).
      assert (Hstep : Z.log2 (n mod a1) + 1 <= Z.log2 n)
        by (apply log2_mod_lt; lia).
      assert (Hloga1 : Z.log2 a1 <= Z.log2 a) by (apply Z.log2_le_mono; lia).
      apply (IH f1' f2' (n mod a1) a1 (eps4 a1 n * (eps8 n ^ k * s))).
      * lia.
      * assumption.
      * lia.
      * rewrite Nat2Z.inj_succ in Hm.
        lia.
      * rewrite Nat2Z.inj_succ in H1.
        lia.
      * rewrite Nat2Z.inj_succ in H2.
        lia.
Qed.

(** A coprime numerator makes the run end at modulus [1], so the value is the
    carried sign up to a sign: the Euclid recursion preserves [Z.gcd]. *)
Lemma jacobi_loop_pm1 : forall (m f : nat) (a n s : Z),
  0 < n -> Z.Odd n -> 0 <= a < n -> Z.gcd a n = 1 ->
  Z.log2 a + Z.log2 n <= Z.of_nat m -> Z.of_nat m + 2 <= Z.of_nat f ->
  jacobi_loop f a n s = s \/ jacobi_loop f a n s = - s.
Proof.
  induction m as [| m IH].
  - intros f a n s Hn Hodd Ha Hgcd Hm Hf.
    assert (Hln : Z.log2 n = 0).
    { pose proof (Z.log2_nonneg a).
      pose proof (Z.log2_nonneg n).
      lia. }

    apply Z.log2_null in Hln.
    assert (Hn1 : n = 1) by lia.
    assert (Ha0 : a = 0) by lia.
    subst a n.
    destruct f as [| f']; [simpl in Hf; lia |].
    rewrite jacobi_loop_S.
    rewrite !Z.eqb_refl.
    left.
    reflexivity.
  - intros f a n s Hn Hodd Ha Hgcd Hm Hf.
    destruct f as [| f']; [simpl in Hf; lia |].
    rewrite jacobi_loop_S.
    destruct (a =? 0) eqn:Ea.
    + (* [gcd 0 n = n], so a coprime run has already reached modulus [1] *)
      apply Z.eqb_eq in Ea.
      subst a.
      rewrite Z.gcd_0_l in Hgcd.
      assert (Hn1 : n = 1) by lia.
      subst n.
      rewrite Z.eqb_refl.
      left.
      reflexivity.
    + apply Z.eqb_neq in Ea.
      assert (Hapos : 0 < a) by lia.
      destruct (two_adic_decomp a Hapos)
        as [k [a1 [Hk [Hpos [Hoddp [Heq [Hklog Hle]]]]]]].
      assert (Hlogan : Z.log2 a <= Z.log2 n) by (apply Z.log2_le_mono; lia).
      pose proof (Z.log2_nonneg a) as Hla.
      pose proof (Z.log2_nonneg n) as Hln.
      assert (Hfk : k <= Z.of_nat (S f')) by (rewrite Nat2Z.inj_succ; lia).
      rewrite (jacobi_twos_val (S f') k a1 a n s Hk Hpos Hoddp Heq Hfk).
      cbn [jacobi_loop].
      assert (Hbnd : 0 <= n mod a1 < a1) by (apply Z.mod_pos_bound; lia).
      assert (Hstep : Z.log2 (n mod a1) + 1 <= Z.log2 n)
        by (apply log2_mod_lt; lia).
      assert (Hloga1 : Z.log2 a1 <= Z.log2 a) by (apply Z.log2_le_mono; lia).
      (* the odd part inherits coprimality, and one Euclid step preserves it *)
      assert (Hg1 : Z.gcd a1 n = 1).
      { assert (Hd : (Z.gcd a1 n | Z.gcd a n)).
        { apply Z.gcd_greatest.
          - apply Z.divide_trans with a1.
            + apply Z.gcd_divide_l.
            + rewrite Heq.
              apply Z.divide_factor_r.
          - apply Z.gcd_divide_r. }

        rewrite Hgcd in Hd.
        pose proof (Z.gcd_nonneg a1 n).
        destruct (Z.divide_1_r _ Hd) as [Hd1 | Hd1]; lia. }

      assert (Hgnew : Z.gcd (n mod a1) a1 = 1).
      { rewrite Z.gcd_mod by lia.
        assumption. }

      set (c := eps4 a1 n * eps8 n ^ k).

      assert (Hc : c = 1 \/ c = -1).
      { unfold c.
        apply pm1_mul; [apply eps4_pm1 |].
        apply pm1_pow; [lia | apply eps8_pm1]. }

      replace (eps4 a1 n * (eps8 n ^ k * s)) with (c * s) by (unfold c; ring).
      assert (Hrec : jacobi_loop f' (n mod a1) a1 (c * s) = c * s
                     \/ jacobi_loop f' (n mod a1) a1 (c * s) = - (c * s)).
      { rewrite Nat2Z.inj_succ in Hm, Hf.
        apply (IH f' (n mod a1) a1 (c * s)); try assumption; lia. }

      destruct Hrec as [Hr | Hr]; rewrite Hr; destruct Hc as [Hc | Hc]; rewrite Hc.
      * left.
        ring.
      * right.
        ring.
      * right.
        ring.
      * left.
        ring.
Qed.

(* ================================================================= *)
(** ** [jacobi_symbol] satisfies the rules -- the six clause lemmas. *)

(** The fuel [jacobi_symbol] starts with, in the shape the round lemmas want:
    one round's worth peeled off, and the remainder measured in [Z]. *)
Lemma jacobi_fuel_shape : forall n, 0 < n -> exists f : nat,
  (2 * S (Z.to_nat (Z.log2 (Z.abs n + 2))))%nat = S f
  /\ Z.of_nat f = 2 * Z.log2 (n + 2) + 1.
Proof.
  intros n Hn.
  exists (2 * Z.to_nat (Z.log2 (Z.abs n + 2)) + 1)%nat.
  split.
  - lia.
  - rewrite Z.abs_eq by lia.
    pose proof (Z.log2_nonneg (n + 2)).
    lia.
Qed.

(** Periodicity: [jacobi_symbol] reduces its numerator before it starts, so
    the rule holds by construction. *)
Lemma jacobi_symbol_mod : forall a n, 0 < n -> Z.Odd n ->
  jacobi_symbol a n = jacobi_symbol (a mod n) n.
Proof.
  intros a n Hn Hodd.
  unfold jacobi_symbol.
  rewrite Zmod_mod.
  reflexivity.
Qed.

(** The [(2 | n)] supplement, on a numerator already below [n / 2]: doubling
    adds exactly one two for [jacobi_twos] to strip, and both runs then
    continue with the same fuel on the same pair. *)
Lemma jacobi_symbol_double : forall a n,
  0 < n -> Z.Odd n -> 0 <= a -> 2 * a < n ->
  jacobi_symbol (2 * a) n = eps8 n * jacobi_symbol a n.
Proof.
  intros a n Hn Hodd Ha Hlt.
  unfold jacobi_symbol.
  rewrite (Z.mod_small a n) by lia.
  rewrite (Z.mod_small (2 * a) n) by lia.
  destruct (jacobi_fuel_shape n Hn) as [f [HF Hf]].
  rewrite HF.
  rewrite !jacobi_loop_S.
  destruct (Z.eq_dec a 0) as [Ha0 | Ha0].
  - (* [a = 0]: both runs stop on the spot *)
    subst a.
    rewrite Z.mul_0_r.
    rewrite Z.eqb_refl.
    destruct (n =? 1) eqn:En.
    + apply Z.eqb_eq in En.
      subst n.
      reflexivity.
    + cbv iota.
      ring.
  - (* [a > 0]: one extra two, hence one extra [eps8 n] *)
    assert (Hapos : 0 < a) by lia.
    destruct (two_adic_decomp a Hapos)
      as [k [a1 [Hk [Hpos [Hoddp [Heq [Hklog Hle]]]]]]].
    assert (E1 : (2 * a =? 0) = false) by (apply Z.eqb_neq; lia).
    assert (E2 : (a =? 0) = false) by (apply Z.eqb_neq; lia).
    rewrite E1, E2.
    assert (Hlogan : Z.log2 a <= Z.log2 n) by (apply Z.log2_le_mono; lia).
    assert (Hlog2 : Z.log2 n <= Z.log2 (n + 2)) by (apply Z.log2_le_mono; lia).
    pose proof (Z.log2_nonneg a).
    pose proof (Z.log2_nonneg n).
    assert (Hfk1 : k + 1 <= Z.of_nat (S f)) by (rewrite Nat2Z.inj_succ; lia).

    assert (Heq2 : 2 * a = 2 ^ (k + 1) * a1).
    { rewrite Heq.
      rewrite Z.pow_add_r by lia.
      rewrite Z.pow_1_r.
      ring. }

    rewrite (jacobi_twos_val (S f) (k + 1) a1 (2 * a) n 1) by (try lia; assumption).
    rewrite (jacobi_twos_val (S f) k a1 a n 1) by (try lia; assumption).
    cbn [jacobi_loop].
    assert (Hsign : eps4 a1 n * (eps8 n ^ (k + 1) * 1)
                    = eps8 n * (eps4 a1 n * (eps8 n ^ k * 1))).
    { rewrite Z.pow_add_r by lia.
      rewrite Z.pow_1_r.
      ring. }

    rewrite Hsign.
    apply jacobi_loop_scale.
Qed.

(** Reciprocity for a numerator below the modulus: the first round of
    [jacobi_symbol a n] is exactly the [eps4] flip followed by the run that
    [jacobi_symbol n a] performs, once the two fuels are reconciled. *)
Lemma jacobi_symbol_step : forall a n, 0 < a -> a < n -> Z.Odd a -> Z.Odd n ->
  jacobi_symbol a n = eps4 a n * jacobi_symbol n a.
Proof.
  intros a n Ha Han Hodda Hoddn.
  unfold jacobi_symbol.
  rewrite (Z.mod_small a n) by lia.
  destruct (jacobi_fuel_shape n) as [f [HF Hf]]; [lia |].
  destruct (jacobi_fuel_shape a) as [g [HG Hg]]; [lia |].
  rewrite HF, HG.
  rewrite jacobi_loop_S.
  assert (E : (a =? 0) = false) by (apply Z.eqb_neq; lia).
  rewrite E.
  rewrite (jacobi_twos_val (S f) 0 a a n 1);
    [| lia | lia | assumption | (rewrite Z.pow_0_r; ring) | lia].
  cbn [jacobi_loop].
  assert (Hsign : eps4 a n * (eps8 n ^ 0 * 1) = eps4 a n * 1)
    by (rewrite Z.pow_0_r; ring).
  rewrite Hsign.
  rewrite jacobi_loop_scale.
  f_equal.
  (* both runs continue on [(n mod a, a)]; only the fuel differs *)
  assert (Hb : 0 <= n mod a < a) by (apply Z.mod_pos_bound; lia).
  assert (Hstep : Z.log2 (n mod a) + 1 <= Z.log2 n) by (apply log2_mod_lt; lia).
  assert (Hlogan : Z.log2 a <= Z.log2 n) by (apply Z.log2_le_mono; lia).
  assert (Hlogma : Z.log2 (n mod a) <= Z.log2 a) by (apply Z.log2_le_mono; lia).
  assert (Hlogn2 : Z.log2 n <= Z.log2 (n + 2)) by (apply Z.log2_le_mono; lia).
  assert (Hloga2 : Z.log2 a <= Z.log2 (a + 2)) by (apply Z.log2_le_mono; lia).
  pose proof (Z.log2_nonneg (n mod a)).
  pose proof (Z.log2_nonneg a).
  assert (Hid : Z.of_nat (Z.to_nat (Z.log2 (n mod a) + Z.log2 a))
                = Z.log2 (n mod a) + Z.log2 a) by (apply Z2Nat.id; lia).
  apply (jacobi_fuel_stable (Z.to_nat (Z.log2 (n mod a) + Z.log2 a)) f (S g)
           (n mod a) a 1).
  - lia.
  - assumption.
  - lia.
  - lia.
  - lia.
  - rewrite Nat2Z.inj_succ.
    lia.
Qed.

(** Quadratic reciprocity, in the generality the divstep bridge needs: no
    coprimality hypothesis (both sides vanish when [gcd(a,n) <> 1]).  The
    three cases are [a < n] ([jacobi_symbol_step]), [a = n] (both sides are
    [0] unless [n = 1]), and [a > n] (the step lemma on the swapped pair,
    with [eps4] squaring to [1]). *)
Lemma jacobi_symbol_reciprocity : forall a n,
  0 < a -> 0 < n -> Z.Odd a -> Z.Odd n ->
  jacobi_symbol a n = eps4 a n * jacobi_symbol n a.
Proof.
  intros a n Ha Hn Hodda Hoddn.
  destruct (Z.lt_trichotomy a n) as [Hlt | [Heq | Hgt]].
  - apply jacobi_symbol_step; assumption.
  - (* [a = n]: the numerator reduces to [0] *)
    subst a.
    destruct (Z.eq_dec n 1) as [Hn1 | Hn1].
    + subst n.
      vm_compute.
      reflexivity.
    + unfold jacobi_symbol.
      rewrite Z.mod_same by lia.
      destruct (jacobi_fuel_shape n Hn) as [f [HF Hf]].
      rewrite HF.
      rewrite jacobi_loop_S.
      rewrite Z.eqb_refl.
      assert (E : (n =? 1) = false) by (apply Z.eqb_neq; lia).
      rewrite E.
      ring.
  - (* [a > n]: swap and cancel the doubled sign *)
    rewrite (jacobi_symbol_step n a); [| lia | lia | assumption | assumption].
    rewrite (eps4_comm a n).

    assert (Hsq : eps4 n a * eps4 n a = 1).
    { destruct (eps4_pm1 n a) as [H | H]; rewrite H; reflexivity. }
    rewrite Z.mul_assoc.
    rewrite Hsq.
    ring.
Qed.

(** [(1 | n) = 1]: the run strips no twos, takes no [eps4] flip, and lands on
    modulus [1]. *)
Lemma jacobi_symbol_1 : forall n, 0 < n -> Z.Odd n -> jacobi_symbol 1 n = 1.
Proof.
  intros n Hn Hodd.
  unfold jacobi_symbol.
  destruct (jacobi_fuel_shape n Hn) as [f [HF Hf]].
  rewrite HF.
  pose proof (Z.log2_nonneg (n + 2)).
  destruct (Z.eq_dec n 1) as [Hn1 | Hn1].
  - subst n.
    rewrite Zmod_1_r.
    rewrite jacobi_loop_S.
    rewrite !Z.eqb_refl.
    reflexivity.
  - rewrite (Z.mod_small 1 n) by lia.
    rewrite jacobi_loop_S.
    assert (E : (1 =? 0) = false) by reflexivity.
    rewrite E.
    rewrite (jacobi_twos_val (S f) 0 1 1 n 1);
      [| lia | lia | (exists 0; lia) | (rewrite Z.pow_0_r; ring) | lia].
    cbn [jacobi_loop].
    rewrite Zmod_1_r.
    destruct f as [| f']; [lia |].
    rewrite jacobi_loop_S.
    rewrite !Z.eqb_refl.
    reflexivity.
Qed.

(** [(0 | n) = 0] for [n > 1]: the run stops at once on a modulus above [1]. *)
Lemma jacobi_symbol_0 : forall n, 1 < n -> Z.Odd n -> jacobi_symbol 0 n = 0.
Proof.
  intros n Hn Hodd.
  unfold jacobi_symbol.
  rewrite Zmod_0_l.
  destruct (jacobi_fuel_shape n) as [f [HF Hf]]; [lia |].
  rewrite HF.
  rewrite jacobi_loop_S.
  rewrite Z.eqb_refl.
  assert (E : (n =? 1) = false) by (apply Z.eqb_neq; lia).
  rewrite E.
  reflexivity.
Qed.

(** [(0 | 1) = 1]: the empty product. *)
Lemma jacobi_symbol_0_1 : jacobi_symbol 0 1 = 1.
Proof.
  vm_compute.
  reflexivity.
Qed.

(* ================================================================= *)
(** ** The rule set -- [JacobiRules]. *)

(** The five textbook rules for [(a | n)] plus the two base values, as a
    predicate on an abstract symbol [J].  In order: periodicity in the
    numerator; the [(2 | n)] supplement; quadratic reciprocity; [(1 | n) = 1];
    [(0 | n) = 0] for [n > 1]; [(0 | 1) = 1].  The file header records why the
    supplement is restricted to a reduced numerator and why reciprocity
    carries no coprimality hypothesis. *)
Definition JacobiRules (J : Z -> Z -> Z) : Prop :=
  (forall a n, 0 < n -> Z.Odd n -> J a n = J (a mod n) n)
  /\ (forall a n, 0 < n -> Z.Odd n -> 0 <= a -> 2 * a < n ->
        J (2 * a) n = eps8 n * J a n)
  /\ (forall a n, 0 < a -> 0 < n -> Z.Odd a -> Z.Odd n ->
        J a n = eps4 a n * J n a)
  /\ (forall n, 0 < n -> Z.Odd n -> J 1 n = 1)
  /\ (forall n, 1 < n -> Z.Odd n -> J 0 n = 0)
  /\ J 0 1 = 1.

(** The model's algorithmic [jacobi_symbol] satisfies every rule. *)
Theorem jacobi_symbol_rules : JacobiRules jacobi_symbol.
Proof.
  unfold JacobiRules.
  split; [exact jacobi_symbol_mod |].
  split; [exact jacobi_symbol_double |].
  split; [exact jacobi_symbol_reciprocity |].
  split; [exact jacobi_symbol_1 |].
  split; [exact jacobi_symbol_0 |].
  exact jacobi_symbol_0_1.
Qed.

(* ================================================================= *)
(** ** Uniqueness -- [jacobi_unique]. *)

(** Inner induction of [jacobi_unique]: on a numerator [b] already reduced
    below the modulus, the rules force the value, given that they already
    force it at every smaller odd modulus.  [e] bounds [b]: halving with the
    supplement rule shrinks it, and an odd [b > 1] hands the goal to the
    smaller modulus [b] by reciprocity. *)
Lemma jacobi_unique_num : forall (e : nat) (J1 J2 : Z -> Z -> Z),
  JacobiRules J1 -> JacobiRules J2 ->
  forall n, 0 < n -> Z.Odd n ->
  (forall m b, 0 < m -> Z.Odd m -> m < n -> 0 <= b -> J1 b m = J2 b m) ->
  forall b, 0 < b -> b < n -> b <= Z.of_nat e -> J1 b n = J2 b n.
Proof.
  induction e as [| e IH].
  - intros J1 J2 R1 R2 n Hn Hodd Houter b Hb Hbn Hbe.
    simpl in Hbe.
    lia.
  - intros J1 J2 R1 R2 n Hn Hodd Houter b Hb Hbn Hbe.
    pose proof R1 as R1c.
    pose proof R2 as R2c.
    destruct R1c as [R1p [R1d [R1r [R1one [R1zero R1z1]]]]].
    destruct R2c as [R2p [R2d [R2r [R2one [R2zero R2z1]]]]].
    rewrite Nat2Z.inj_succ in Hbe.
    destruct (Z.Even_or_Odd b) as [Hev | Hod].
    + (* even: halve it with the supplement rule *)
      destruct Hev as [c Hc].
      assert (Hc0 : 0 < c) by lia.
      rewrite Hc.
      rewrite (R1d c n Hn Hodd) by lia.
      rewrite (R2d c n Hn Hodd) by lia.
      f_equal.
      apply (IH J1 J2 R1 R2 n Hn Hodd Houter c); lia.
    + (* odd: either the base value, or reciprocity down to modulus [b] *)
      destruct (Z.eq_dec b 1) as [Hb1 | Hb1].
      * subst b.
        rewrite (R1one n Hn Hodd).
        rewrite (R2one n Hn Hodd).
        reflexivity.
      * rewrite (R1r b n Hb Hn Hod Hodd).
        rewrite (R2r b n Hb Hn Hod Hodd).
        f_equal.
        apply Houter; try assumption; lia.
Qed.

(** Outer induction of [jacobi_unique]: [d] bounds the modulus.  The rules
    reduce the numerator, dispatch the zero case on the two base values, and
    otherwise hand over to [jacobi_unique_num]. *)
Lemma jacobi_unique_mod : forall (d : nat) (J1 J2 : Z -> Z -> Z),
  JacobiRules J1 -> JacobiRules J2 ->
  forall n, 0 < n -> Z.Odd n -> n <= Z.of_nat d ->
  forall a, 0 <= a -> J1 a n = J2 a n.
Proof.
  induction d as [| d IH].
  - intros J1 J2 R1 R2 n Hn Hodd Hnd a Ha.
    simpl in Hnd.
    lia.
  - intros J1 J2 R1 R2 n Hn Hodd Hnd a Ha.
    pose proof R1 as R1c.
    pose proof R2 as R2c.
    destruct R1c as [R1p [R1d [R1r [R1one [R1zero R1z1]]]]].
    destruct R2c as [R2p [R2d [R2r [R2one [R2zero R2z1]]]]].
    rewrite Nat2Z.inj_succ in Hnd.
    rewrite (R1p a n Hn Hodd).
    rewrite (R2p a n Hn Hodd).
    assert (Hb : 0 <= a mod n < n) by (apply Z.mod_pos_bound; lia).
    destruct (Z.eq_dec (a mod n) 0) as [Hz | Hz].
    + rewrite Hz.
      destruct (Z.eq_dec n 1) as [Hn1 | Hn1].
      * subst n.
        rewrite R1z1, R2z1.
        reflexivity.
      * rewrite (R1zero n ltac:(lia) Hodd).
        rewrite (R2zero n ltac:(lia) Hodd).
        reflexivity.
    + apply (jacobi_unique_num (Z.to_nat (a mod n)) J1 J2 R1 R2 n Hn Hodd).
      * intros m b Hm Hoddm Hmn Hb0.
        apply (IH J1 J2 R1 R2 m Hm Hoddm); [lia | assumption].
      * lia.
      * lia.
      * rewrite Z2Nat.id by lia.
        lia.
Qed.

(** The rules determine the symbol: any two functions satisfying
    [JacobiRules] agree on every numerator and every odd positive modulus.
    So [jacobi_symbol_rules] is not a weak property -- it pins the model's
    algorithm down to the textbook symbol. *)
Theorem jacobi_unique : forall J1 J2, JacobiRules J1 -> JacobiRules J2 ->
  forall a n, 0 <= a -> 0 < n -> Z.Odd n -> J1 a n = J2 a n.
Proof.
  intros J1 J2 R1 R2 a n Ha Hn Hodd.
  apply (jacobi_unique_mod (Z.to_nat n) J1 J2 R1 R2 n Hn Hodd).
  - rewrite Z2Nat.id by lia.
    lia.
  - assumption.
Qed.

(* ================================================================= *)
(** ** Coprime numerators give a sign -- [jacobi_pm1]. *)

(** For a numerator coprime to the modulus the symbol is [1] or [-1] (it is
    [0] exactly on the non-coprime numerators, which the C function is allowed
    to report as "unknown"). *)
Lemma jacobi_pm1 : forall a n, 0 < n -> Z.Odd n -> Zis_gcd a n 1 ->
  jacobi_symbol a n = 1 \/ jacobi_symbol a n = -1.
Proof.
  intros a n Hn Hodd Hg.
  assert (Hgcd : Z.gcd a n = 1) by (apply Zis_gcd_gcd; [lia | assumption]).
  unfold jacobi_symbol.
  destruct (jacobi_fuel_shape n Hn) as [f [HF Hf]].
  rewrite HF.
  assert (Hb : 0 <= a mod n < n) by (apply Z.mod_pos_bound; lia).

  assert (Hgx : Z.gcd (a mod n) n = 1).
  { rewrite Z.gcd_mod by lia.
    rewrite Z.gcd_comm.
    assumption. }

  assert (Hlog : Z.log2 (a mod n) <= Z.log2 n) by (apply Z.log2_le_mono; lia).
  assert (Hlog2 : Z.log2 n <= Z.log2 (n + 2)) by (apply Z.log2_le_mono; lia).
  pose proof (Z.log2_nonneg (a mod n)).
  pose proof (Z.log2_nonneg n).
  assert (Hid : Z.of_nat (Z.to_nat (Z.log2 (a mod n) + Z.log2 n))
                = Z.log2 (a mod n) + Z.log2 n) by (apply Z2Nat.id; lia).
  assert (Hfuel : Z.of_nat (Z.to_nat (Z.log2 (a mod n) + Z.log2 n)) + 2
                  <= Z.of_nat (S f)) by (rewrite Nat2Z.inj_succ; lia).
  destruct (jacobi_loop_pm1 (Z.to_nat (Z.log2 (a mod n) + Z.log2 n)) (S f)
              (a mod n) n 1 Hn Hodd Hb Hgx ltac:(lia) Hfuel) as [Hr | Hr].
  - left.
    lia.
  - right.
    lia.
Qed.
