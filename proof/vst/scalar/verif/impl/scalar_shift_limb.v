(** * Verif_shift_limb: Proof of body_secp256k1_scalar_shift_limb *)
(** Copyright (C) 2026 remix7531
    SPDX-License-Identifier: MIT *)

Require Import secp256k1.vst.base.
Require Import secp256k1.vst.helper.notations.
Require Import secp256k1.vst.gprog.
Require Import secp256k1.vst.scalar.impl.
Require Import secp256k1.vst.tactics.core.
Require Import secp256k1.vst.tactics.int128.
Require Import secp256k1.vst.tactics.scalar.

(* ================================================================= *)
(** ** Hoisted pure cores -- [theory.bits] / [vst/helper/repr.v]. *)

(** The pure-Z limb-extraction cores -- [dls_core] (cross-limb
    recombination), [limb_shift_combine] (limb-aligned whole-limb drop),
    and [limb_shift_high_zero] (vanishing high limb) -- live in
    [theory.bits] (in scope via [tactics.core]).  [uint512_to_val_Znth]
    (each element of [uint512_to_val l] is limb [i] of [u512_val l])
    lives in [vst/helper/repr.v], next to its [uint256] analogue; it
    is shared with [scalar_mul_shift_var]. *)

(* ================================================================= *)
(** ** File-local Int64 shift/combine bridges. *)

(** Logical right shift by a variable amount [0 <= s < 64] is division
    by [2^s] (unsigned-range argument). *)
Lemma Int64_shru_var : forall v s,
  0 <= v < 2^64 ->
  0 <= s < 64 ->
  Int64.shru (Int64.repr v) (Int64.repr s) = Int64.repr (v / 2^s).
Proof.
  intros v s Hv Hs.
  rewrite Int64.shru_div_two_p.
  rewrite (Int64.unsigned_repr v) by rep_lia.
  rewrite (Int64.unsigned_repr s) by rep_lia.
  rewrite two_p_correct.
  reflexivity.
Qed.

(** Left shift by a variable amount [0 <= s < 64] keeps the low [64 - s]
    bits, lifted up by [s] (the high bits overflow [mod 2^64]). *)
Lemma Int64_shl_var : forall v s,
  0 <= v < 2^64 ->
  0 <= s < 64 ->
  Int64.shl (Int64.repr v) (Int64.repr s) = Int64.repr ((v mod 2^(64-s)) * 2^s).
Proof.
  intros v s Hv Hs.
  rewrite Int64.shl_mul_two_p.
  rewrite (Int64.unsigned_repr s) by rep_lia.
  rewrite two_p_correct.
  unfold Int64.mul.
  rewrite (Int64.unsigned_repr v) by rep_lia.
  rewrite (Int64.unsigned_repr (2^s))
    by (assert (2^s < 2^64) by (apply Z.pow_lt_mono_r; lia); rep_lia).
  apply Int64.eqm_samerepr.
  exists (v / 2^(64-s)).
  change Int64.modulus with (2^64).
  assert (Hsplit : 2^64 = 2^(64-s) * 2^s)
    by (rewrite <- Z.pow_add_r by lia; f_equal; lia).
  rewrite (Z_div_mod_eq_full v (2^(64-s))) at 1.
  rewrite Hsplit.
  ring.
Qed.

(** The C cross-limb combine [(v0 >> s) | (v1 << (64 - s))] is, as a [Z],
    [v0 / 2^s + (v1 mod 2^s) * 2^(64-s)] (the two bit ranges are disjoint,
    so the OR is addition). *)
Lemma Int64_combine : forall v0 v1 s,
  0 <= v0 < 2^64 ->
  0 <= v1 < 2^64 ->
  0 < s < 64 ->
  Int64.or (Int64.shru (Int64.repr v0) (Int64.repr s))
           (Int64.shl (Int64.repr v1) (Int64.repr (64 - s)))
  = Int64.repr (v0 / 2^s + (v1 mod 2^s) * 2^(64-s)).
Proof.
  intros v0 v1 s Hv0 Hv1 Hs.
  rewrite Int64_shru_var by lia.
  rewrite Int64_shl_var by lia.
  replace (64 - (64 - s)) with s by lia.
  rewrite <- Int64.add_is_or.
  - apply add64_repr.
  - apply Int64.same_bits_eq.
    intros i Hi.
    rewrite Int64.bits_and by lia.
    rewrite Int64.bits_zero.
    rewrite !(Int64.testbit_repr) by lia.
    assert (Hlo : 0 <= v0 / 2^s < 2^(64-s)).
    { split; [apply Z.div_pos; [lia | apply Z.pow_pos_nonneg; lia] | ].
      apply Z.div_lt_upper_bound; [apply Z.pow_pos_nonneg; lia | ].
      rewrite <- Z.pow_add_r by lia.
      replace (s + (64 - s)) with 64 by lia.
      lia. }
    assert (Hmod : 0 <= v1 mod 2^s < 2^s)
      by (apply Z.mod_pos_bound; apply Z.pow_pos_nonneg; lia).
    destruct (Z.lt_ge_cases i (64 - s)) as [Hilt|Hige].
    + assert (Hhi0 : Z.testbit ((v1 mod 2^s) * 2^(64-s)) i = false).
      { rewrite Z.mul_pow2_bits by lia.
        rewrite Z.testbit_neg_r by lia.
        reflexivity. }
      rewrite Hhi0.
      apply andb_false_r.
    + assert (Hlo0 : Z.testbit (v0 / 2^s) i = false).
      { apply Z.testbit_false; [lia | ].
        rewrite Z.div_small; [reflexivity | ].
        split; [apply Z.div_pos; [lia | apply Z.pow_pos_nonneg; lia] | ].
        apply Z.lt_le_trans with (2^(64-s)); [lia | apply Z.pow_le_mono_r; lia]. }
      rewrite Hlo0.
      apply andb_false_l.
Qed.

(** The cross-limb combine, lifted to limb extraction: with shift split as
    [shift = 64*sl + s] ([0 < s < 64]), combining limb [j+sl] of [p]
    (shifted down by [s]) with limb [j+1+sl] of [p] (the wrap-around high
    half) yields limb [j] of [p / 2^shift].  [dls_core] phrased on [limb]. *)
Lemma dls_limb : forall p s sl j,
  0 <= p ->
  0 < s < 64 ->
  0 <= sl ->
  limb (2^64) p (j + Z.to_nat sl) / 2^s
  + (limb (2^64) p (j + 1 + Z.to_nat sl) mod 2^s) * 2^(64-s)
  = limb (2^64) (p / 2^(64*sl + s)) j.
Proof.
  intros p s sl j Hp Hs Hsl.
  (* Setup: [x] is [p] with the [sl] low limbs (and [j] more) already dropped. *)
  set (x := p / 2^(64 * (Z.of_nat j + sl))).
  assert (Hx : 0 <= x) by (subst x; apply Z.div_pos; [lia | apply Z.pow_pos_nonneg; lia]).
  assert (Hdiv : (2^s | 2^64)).
  { exists (2^(64-s)).
    rewrite <- Z.pow_add_r by lia.
    f_equal. lia. }

  (* Main: re-express the two source limbs as limb 0 and limb 1 of [x]. *)
  assert (Hv0 : limb (2^64) p (j + Z.to_nat sl) = x mod 2^64).
  { unfold limb, x.
    rewrite <- Z.pow_mul_r by lia.
    do 3 f_equal.
    rewrite Nat2Z.inj_add, Z2Nat.id by lia.
    lia. }
  assert (Hv1 : limb (2^64) p (j + 1 + Z.to_nat sl) = (x / 2^64) mod 2^64).
  { unfold limb, x.
    rewrite Z.div_div by (try apply Z.pow_nonzero; try apply Z.pow_pos_nonneg; lia).
    rewrite <- Z.pow_add_r by lia.
    rewrite <- Z.pow_mul_r by lia.
    do 3 f_equal.
    rewrite !Nat2Z.inj_add, Z2Nat.id by lia.
    simpl Z.of_nat.
    lia. }
  rewrite Hv0, Hv1.

  (* discharge the combine via [dls_core] (the [mod_mod_divide] aligns the [mod 2^s]) *)
  rewrite Z.mod_mod_divide by exact Hdiv.
  rewrite dls_core by lia.

  (* Closeout: limb 0 of [x / 2^s] is limb [j] of [p / 2^(64*sl + s)]. *)
  unfold limb, x.
  rewrite Z.div_div by (try apply Z.pow_nonzero; try apply Z.pow_pos_nonneg; lia).
  rewrite <- Z.pow_add_r by lia.
  rewrite <- Z.pow_mul_r by lia.
  rewrite Z.div_div by (try apply Z.pow_nonzero; try apply Z.pow_pos_nonneg; lia).
  rewrite <- Z.pow_add_r by lia.
  do 3 f_equal.
  lia.
Qed.

(** The combine, packaged at the C-value level (the [Int64.or] of a shifted
    limb [j+sl] and the wrap-in of limb [j+1+sl]) for use directly inside the
    [forward] cascade.  Specialises [dls_limb] + [Int64_combine]. *)
Lemma combine_at : forall (ll : UInt512) (sft : Z) (j : nat),
  0 <= u512_val ll ->
  0 <= sft ->
  sft mod 64 <> 0 ->
  Int64.or
    (Int64.shru (Int64.repr (limb (2^64) (u512_val ll) (j + Z.to_nat (sft / 64))))
                (Int64.repr (sft mod 64)))
    (Int64.shl (Int64.repr (limb (2^64) (u512_val ll) (j + 1 + Z.to_nat (sft / 64))))
               (Int64.repr (64 - sft mod 64)))
  = Int64.repr (limb (2^64) (u512_val ll / 2^sft) j).
Proof.
  intros ll sft j Hll Hsft Hpos.
  assert (Hb : 0 <= sft / 64) by (apply Z.div_pos; lia).
  pose proof (Z.mod_pos_bound sft 64 ltac:(lia)) as Hm.
  rewrite Int64_combine by (try apply Z.mod_pos_bound; lia).
  f_equal.
  pose proof (dls_limb (u512_val ll) (sft mod 64) (sft / 64) j Hll ltac:(lia) Hb) as Hd.
  rewrite <- (Z.div_mod sft 64) in Hd by lia.
  exact Hd.
Qed.

(* ================================================================= *)
(** ** shift_limb -- [secp256k1_scalar_shift_limb]. *)

(** Extract limb [j] of [l / 2^shift].  The C reads limb [j + shift/64] of
    [l] (shifted down by [shift mod 64]), optionally OR-ing in the wrap-around
    high half from limb [j + 1 + shift/64].  The guards [shift < lo] /
    [shift < hi] / [shiftlow != 0] select whether each piece contributes; the
    pure facts [combine_at] / [limb_shift_combine] / [limb_shift_high_zero]
    discharge the three resulting cases. *)
Lemma body_secp256k1_scalar_shift_limb:
  semax_body Vprog Gprog f_secp256k1_scalar_shift_limb spec_secp256k1_scalar_shift_limb.
Proof.
  start_function.

  rename H into Hslo.
  rename H0 into Hshi.
  rename H1 into Hj0.
  rename H2 into Hj3.

  (* uint64_t result = 0 *)
  forward.

  assert_PROP (Zlength (uint512_to_val l) = 8) as Hlen by entailer!.

  (* ===== Outer guard: if (shift < lo) -- nonzero result, else 0 ===== *)
  (* if (shift < lo): join postcondition fixes _result to the limb *)
  forward_if (PROP ( )
     LOCAL (temp _result (Vlong (Int64.repr (limb (2^64) (u512_val l / 2^shift) (Z.to_nat j))));
     temp _l l_ptr; temp _shift (Vint (Int.repr shift));
     temp _shiftlimbs (Vint (Int.repr (shift / 64)));
     temp _shiftlow (Vint (Int.repr (shift mod 64)));
     temp _shifthigh (Vint (Int.repr (64 - shift mod 64)));
     temp _j (Vint (Int.repr j)); temp _lo (Vint (Int.repr (512 - 64 * j)));
     temp _hi (Vint (Int.repr (448 - 64 * j))))
     SEP (u512_at sh l_ptr l)).
  - (* branch: shift < lo -- the load + shift (+ optional combine) *)
    assert (Hdiv : (let (q, _) := Z.div_eucl shift 64 in q) = shift / 64) by reflexivity.
    rewrite Hdiv.
    assert (Hsl_bnd : 0 <= shift / 64) by (apply Z.div_pos; lia).
    assert (Hidx : j + shift / 64 < 8).
    {
      assert (shift / 64 < 8 - j) by (apply Z.div_lt_upper_bound; lia).
      lia.
    }

    (* t'3 = l->v[j + shiftlimbs] *)
    forward.
    {
      rewrite Hdiv.
      rewrite uint512_to_val_Znth by lia.
      entailer!.
    }
    rewrite Hdiv.
    rewrite uint512_to_val_Znth by lia.

    (* result = t'3 >> shiftlow *)
    forward.
    {
      entailer!.
      assert (Hmod : 0 <= shift mod 64 < 64) by (apply Z.mod_pos_bound; lia).
      rewrite Int.unsigned_repr by rep_lia.
      change (Int.unsigned Int64.iwordsize') with 64.
      lia.
    }

    (* ===== Phase: inner if (shift < hi) -- compute t'1, the && operand ===== *)
    forward_if (PROP ( )
       LOCAL (temp _t'1 (Vint (Int.repr (if ((shift <? 448 - 64 * j) && negb (shift mod 64 =? 0))%bool then 1 else 0)));
       temp _result
         (Vlong (Int64.shru (Int64.repr (limb (2^64) (u512_val l) (Z.to_nat (j + shift / 64))))
                            (Int64.repr (Int.unsigned (Int.repr (shift mod 64))))));
       temp _t'3 (Vlong (Int64.repr (limb (2^64) (u512_val l) (Z.to_nat (j + shift / 64)))));
       temp _l l_ptr; temp _shift (Vint (Int.repr shift));
       temp _shiftlimbs (Vint (Int.repr (shift / 64)));
       temp _shiftlow (Vint (Int.repr (shift mod 64)));
       temp _shifthigh (Vint (Int.repr (64 - shift mod 64)));
       temp _j (Vint (Int.repr j)); temp _lo (Vint (Int.repr (512 - 64 * j)));
       temp _hi (Vint (Int.repr (448 - 64 * j))))
       SEP (u512_at sh l_ptr l)).
    + (* branch: shift < hi -- t'1 = (tbool) shiftlow *)
      (* t'1 = (shiftlow != 0) *)
      forward.
      entailer!.
      assert (Hmod : 0 <= shift mod 64 < 64) by (apply Z.mod_pos_bound; lia).
      replace (shift <? 448 - 64 * j)%Z with true by (symmetry; apply Z.ltb_lt; lia).
      simpl andb.
      destruct (Z.eqb_spec (shift mod 64) 0) as [E|E].
      * (* shiftlow = 0 *)
        rewrite E.
        reflexivity.
      * (* shiftlow != 0 *)
        simpl negb.
        assert (Ee : Int.eq (Int.repr (shift mod 64)) Int.zero = false).
        {
          apply Int.eq_false.
          intro Hc.
          apply E.
          apply (f_equal Int.unsigned) in Hc.
          rewrite Int.unsigned_zero in Hc.
          rewrite Int.unsigned_repr in Hc by rep_lia.
          exact Hc.
        }
        rewrite Ee.
        reflexivity.
    + (* branch: shift >= hi -- t'1 = 0 *)
      (* t'1 = 0 *)
      forward.
      entailer!.
      replace (shift <? 448 - 64 * j)%Z with false by (symmetry; apply Z.ltb_ge; lia).
      reflexivity.
    + (* ===== Phase: inner if (t'1) -- the cross-limb combine ===== *)
      forward_if (PROP ( )
         LOCAL (temp _result (Vlong (Int64.repr (limb (2^64) (u512_val l / 2^shift) (Z.to_nat j))));
         temp _l l_ptr; temp _shift (Vint (Int.repr shift));
         temp _shiftlimbs (Vint (Int.repr (shift / 64)));
         temp _shiftlow (Vint (Int.repr (shift mod 64)));
         temp _shifthigh (Vint (Int.repr (64 - shift mod 64)));
         temp _j (Vint (Int.repr j)); temp _lo (Vint (Int.repr (512 - 64 * j)));
         temp _hi (Vint (Int.repr (448 - 64 * j))))
         SEP (u512_at sh l_ptr l)).
      * (* branch: t'1 != 0 -- combine limb (j+sl) with the high half limb (j+1+sl) *)
        assert (Htrue : ((shift <? 448 - 64 * j) && negb (shift mod 64 =? 0))%bool = true).
        {
          destruct (((shift <? 448 - 64 * j) && negb (shift mod 64 =? 0))%bool) eqn:E.
          reflexivity.
          exfalso.
          apply H0'.
          reflexivity.
        }
        apply andb_true_iff in Htrue.
        destruct Htrue as [Hhi Hlow].
        apply Z.ltb_lt in Hhi.
        apply negb_true_iff in Hlow.
        apply Z.eqb_neq in Hlow.
        assert (Hmod : 0 <= shift mod 64 < 64) by (apply Z.mod_pos_bound; lia).
        assert (Hidx2 : j + 1 + shift / 64 < 8).
        {
          assert (shift / 64 < 7 - j) by (apply Z.div_lt_upper_bound; lia).
          lia.
        }

        (* t'2 = l->v[j + 1 + shiftlimbs] *)
        forward.
        {
          replace (let (q, _) := Z.div_eucl shift 64 in q) with (shift / 64) by reflexivity.
          replace (j + (1 + shift / 64)) with (j + 1 + shift / 64) by lia.
          rewrite uint512_to_val_Znth by lia.
          entailer!.
        }
        replace (let (q, _) := Z.div_eucl shift 64 in q) with (shift / 64) by reflexivity.
        replace (j + (1 + shift / 64)) with (j + 1 + shift / 64) by lia.
        rewrite uint512_to_val_Znth by lia.

        (* result = result | (t'2 << shifthigh) *)
        forward.
        {
          entailer!.
          change (Int.unsigned Int64.iwordsize') with 64.
          lia.
        }
        rewrite (Int.unsigned_repr (shift mod 64)) by rep_lia.
        rewrite (Int.unsigned_repr (64 - shift mod 64)) by rep_lia.
        replace (Z.to_nat (j + shift / 64)) with (Z.to_nat j + Z.to_nat (shift / 64))%nat
          by (rewrite <- Z2Nat.inj_add by lia; reflexivity).
        replace (Z.to_nat (j + 1 + shift / 64)) with (Z.to_nat j + 1 + Z.to_nat (shift / 64))%nat
          by lia.
        rewrite (combine_at l shift (Z.to_nat j)) by (try apply u512_range; lia).
        entailer!.
      * (* branch: t'1 = 0 -- no combine, so either limb-aligned or the high half vanishes *)
        (* skip the OR; result stays t'3 >> shiftlow *)
        forward.
        entailer!.
        assert (Hmod : 0 <= shift mod 64 < 64) by (apply Z.mod_pos_bound; lia).
        assert (Hsl_bnd2 : 0 <= shift / 64) by (apply Z.div_pos; lia).
        assert (Hcond : ((shift <? 448 - 64 * j) && negb (shift mod 64 =? 0))%bool = false).
        {
          destruct (((shift <? 448 - 64 * j) && negb (shift mod 64 =? 0))%bool) eqn:E.
          - exfalso.
            apply (f_equal Int.unsigned) in H0.
            rewrite Int.unsigned_zero in H0.
            rewrite Int.unsigned_repr in H0 by rep_lia.
            discriminate.
          - reflexivity.
        }
        f_equal.
        rewrite (Int.unsigned_repr (shift mod 64)) by rep_lia.
        destruct (Z.eqb_spec (shift mod 64) 0) as [Hz|Hnz].
        {
          (* sub-case: shift mod 64 = 0 -- limb-aligned shift, drop whole limbs *)
          rewrite Hz.
          change (2^0) with 1.
          rewrite Int64.shru_zero.
          f_equal.
          assert (Hshift_eq : shift = 64 * (shift / 64)).
          {
            rewrite (Z.div_mod shift 64) at 1 by lia.
            rewrite Hz.
            lia.
          }
          rewrite Hshift_eq at 1.
          rewrite limb_shift_combine by (try apply u512_range; lia).
          f_equal.
          rewrite <- Z2Nat.inj_add by lia.
          reflexivity.
        }
        (* sub-case: shift mod 64 != 0 and shift >= hi -- the high-half limb is zero *)
        assert (Hge : shift >= 448 - 64 * j).
        {
          simpl negb in Hcond.
          rewrite andb_true_r in Hcond.
          apply Z.ltb_ge in Hcond.
          lia.
        }
        assert (Hslj : (8 <= Z.to_nat j + 1 + Z.to_nat (shift / 64))%nat).
        {
          assert (Hc385 : 64 * (shift / 64) = shift - shift mod 64).
          {
            rewrite (Z.div_mod shift 64) at 2 by lia.
            lia.
          }
          assert (shift / 64 + j >= 7) by lia.
          assert (Z.to_nat j + Z.to_nat (shift / 64) >= 7)%nat.
          {
            rewrite <- Z2Nat.inj_add by lia.
            change 7%nat with (Z.to_nat 7).
            apply Z2Nat.inj_le; lia.
          }
          lia.
        }
        assert (Hhz : limb (2^64) (u512_val l) (Z.to_nat j + 1 + Z.to_nat (shift / 64))%nat = 0).
        {
          replace (u512_val l) with (u512_val l / 2^0) by (rewrite Z.pow_0_r, Z.div_1_r; reflexivity).
          apply (limb_shift_high_zero (u512_val l) 512 0).
          - apply u512_range.
          - apply u512_range.
          - lia.
          - rewrite Nat2Z.inj_add.
            rewrite Nat2Z.inj_add.
            rewrite Z2Nat.id by lia.
            lia.
        }
        replace (Z.to_nat (j + shift / 64)) with (Z.to_nat j + Z.to_nat (shift / 64))%nat
          by (rewrite <- Z2Nat.inj_add by lia; reflexivity).
        assert (Hlimb_rng : 0 <= limb (2^64) (u512_val l) (Z.to_nat j + Z.to_nat (shift / 64)) < 2^64).
        {
          unfold limb.
          apply Z.mod_pos_bound.
          lia.
        }
        rewrite Int64_shru_var by lia.
        f_equal.
        pose proof (dls_limb (u512_val l) (shift mod 64) (shift / 64) (Z.to_nat j)
                      (proj1 (u512_range l)) ltac:(lia) Hsl_bnd2) as Hd.
        rewrite Hhz in Hd.
        rewrite Z.mod_0_l in Hd by (apply Z.pow_nonzero; lia).
        rewrite Z.mul_0_l in Hd.
        rewrite Z.add_0_r in Hd.
        assert (Hsm : 64 * (shift / 64) + shift mod 64 = shift).
        {
          pose proof (Z.div_mod shift 64 ltac:(lia)) as Hdm.
          lia.
        }
        rewrite Hsm in Hd.
        symmetry.
        exact Hd.
  - (* branch: shift >= lo -- result stays 0, the limb is zero *)
    (* fall through with result = 0 *)
    forward.
    entailer!.
    f_equal.
    f_equal.
    apply (limb_shift_high_zero (u512_val l) 512 shift (Z.to_nat j)).
    + apply u512_range.
    + apply u512_range.
    + lia.
    + rewrite Z2Nat.id by lia.
      lia.

  - (* ===== Postcondition: return result ===== *)
    (* return result *)
    forward.
Qed.
