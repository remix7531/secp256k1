(** * Verif_scalar_mul_shift_var: Proof of body_secp256k1_scalar_mul_shift_var *)
(** Copyright (C) 2026 remix7531
    SPDX-License-Identifier: MIT *)

Require Import secp256k1.vst.base.
Require Import secp256k1.contract.helper.structs_scalar.
Require Import secp256k1.contract.helper.notations.
Require Import secp256k1.contract.gprog.scalar.
Require Import secp256k1.tactics.core.
Require Import secp256k1.tactics.int128.
Require Import secp256k1.tactics.scalar.

(* ================================================================= *)
(** ** Pure-Z helpers -- [roundbit_eq] / [mul_shift_bound] (file-local). *)

(** [uint512_to_val_Znth] (each element of [uint512_to_val l] is limb [i]
    of [u512_val l]) lives in [contract.helper.repr], next to its [uint256]
    analogue; it is shared with [shift_limb]. *)

(** The round bit: bit [k] of [p], read by the C as bit [k mod 64] of limb
    [k / 64], is exactly bit [k] of [p].  Used for the [cadd_bit] rounding
    term ([k = shift - 1]). *)
Lemma roundbit_eq : forall (p k : Z),
  0 <= p ->
  0 <= k ->
  (limb (2^64) p (Z.to_nat (k / 64)) / 2^(k mod 64)) mod 2 = (p / 2^k) mod 2.
Proof.
  intros p k Hp Hk.
  unfold limb.
  rewrite Z2Nat.id by (apply Z.div_pos; lia).
  pose proof (Z.mod_pos_bound k 64 ltac:(lia)) as Hm.
  rewrite <- Z.testbit_spec' by lia.
  rewrite Z.mod_pow2_bits_low by lia.
  rewrite Z.testbit_spec' by lia.
  assert (Hnz : (2^64)^(k/64) <> 0) by (apply Z.pow_nonzero; [ lia | apply Z.div_pos; lia ]).
  rewrite Z.div_div by (first [ exact Hnz | apply Z.pow_pos_nonneg; lia ]).
  assert (Hkd : 0 <= k / 64) by (apply Z.div_pos; lia).

  assert (Hpk : (2^64)^(k/64) * 2^(k mod 64) = 2^k).
  { rewrite <- Z.pow_mul_r by lia.
    rewrite <- Z.pow_add_r by lia.
    f_equal.
    pose proof (Z.div_mod k 64 ltac:(lia)).
    lia. }

  rewrite Hpk.
  reflexivity.
Qed.

(** The rounded quotient stays below the group order.  For the 512-bit
    product [p = a*b < N^2] and [256 <= shift < 512], both the shifted
    value [p / 2^shift] and the round-half-up term [p/2^shift + (round bit)]
    fit in [[0, N)].  Clean route: [p/2^shift <= p/2^256 <= (N^2-1)/2^256],
    and [(N^2-1)/2^256 + 1 < N] is a closed (vm_compute) numeric fact. *)
Lemma mul_shift_bound : forall p shift,
  0 <= p ->
  p < secp256k1_N * secp256k1_N ->
  256 <= shift ->
  0 <= p / 2 ^ shift < secp256k1_N /\
  p / 2 ^ shift + (p / 2 ^ (shift - 1)) mod 2 < secp256k1_N.
Proof.
  intros p shift Hp Hp_lt Hshift.
  assert (Hq_nonneg : 0 <= p / 2 ^ shift)
    by (apply Z.div_pos; [lia | apply Z.pow_pos_nonneg; lia]).
  assert (Hq_le : p / 2 ^ shift <= (secp256k1_N * secp256k1_N - 1) / 2 ^ 256).
  {
    apply Z.le_trans with (p / 2 ^ 256).
    - apply Z.div_le_compat_l.
      + lia.
      + split.
        * apply Z.pow_pos_nonneg; lia.
        * apply Z.pow_le_mono_r; lia.
    - apply Z.div_le_mono.
      + apply Z.pow_pos_nonneg; lia.
      + lia.
  }
  assert (Htop : (secp256k1_N * secp256k1_N - 1) / 2 ^ 256 + 1 < secp256k1_N)
    by (unfold secp256k1_N; vm_compute; reflexivity).
  assert (Hround_bnd : 0 <= (p / 2 ^ (shift - 1)) mod 2 < 2)
    by (apply Z.mod_pos_bound; lia).
  split; lia.
Qed.

(* ================================================================= *)
(** ** secp256k1_scalar_mul_shift_var -- [r = round(a*b / 2^shift)]. *)

(** Set [*r] to [round(a*b / 2^shift)].  After [mul_512] fills [l] with the
    512-bit product [p = a*b], the four [shift_limb] calls store limbs 0..3
    of [p / 2^shift] into [r->d], and [cadd_bit] adds round bit [shift-1] of
    [p].  The genuine content lives in the [shift_limb] funspec, [roundbit_eq]
    (the round bit), and [mul_shift_bound] (the [< N] range). *)
Lemma body_secp256k1_scalar_mul_shift_var:
  semax_body Vprog Gprog
    f_secp256k1_scalar_mul_shift_var spec_secp256k1_scalar_mul_shift_var.
Proof.
  start_function.

  (* ===== mul_512: fill local l[8] with the 512-bit product a*b ===== *)

  rewrite !scalar_to_val_eq.
  change t_secp256k1_scalar with t_secp256k1_uint256.
  forward_call_scalar_mul_512 v_l a_ptr b_ptr
    (scalar_to_u256 a) (scalar_to_u256 b)
    Tsh sh_a sh_b l Hl.

  (* ===== shiftlimbs / shiftlow / shifthigh ===== *)

  forward. (* shiftlimbs = shift >> 6 *)
  forward. (* shiftlow   = shift & 0x3F *)
  forward. (* shifthigh  = 64 - shiftlow *)

  (* Normalize the C shift temps to Z div/mod and bound them. *)
  assert (Hsl : Int.shru (Int.repr shift) (Int.repr 6) = Int.repr (shift / 64))
    by (rewrite Int.shru_div_two_p; rewrite !Int.unsigned_repr by rep_lia; reflexivity).
  assert (Hsh : Int.and (Int.repr shift) (Int.repr 63) = Int.repr (shift mod 64))
    by (rewrite and_repr; f_equal; change 63 with (Z.ones 6);
        rewrite Z.land_ones by lia; reflexivity).
  rewrite !Hsl, !Hsh.

  assert (Hslow_bnd : 0 <= shift mod 64 < 64) by (apply Z.mod_pos_bound; lia).
  assert (Hsl_bnd : 4 <= shift / 64 <= 7)
    by (assert (shift / 64 < 8) by (apply Z.div_lt_upper_bound; lia);
        assert (4 <= shift / 64) by (apply Z.div_le_lower_bound; lia); lia).

  (* shifthigh is 64 - shiftlow; align it with the shift_limb spec. *)
  assert (Hshigh : Int.sub (Int.repr 64) (Int.repr (shift mod 64)) = Int.repr (64 - shift mod 64))
    by (rewrite sub_repr; reflexivity).
  rewrite Hshigh.

  (* ===== r->d[0..3] = shift_limb(l, ..., j, 512-64j, 448-64j) ===== *)

  forward_call (v_l, l, shift, 0, Tsh).
  forward. (* r->d[0] = t'1 *)
  forward_call (v_l, l, shift, 1, Tsh).
  forward. (* r->d[1] = t'2 *)
  forward_call (v_l, l, shift, 2, Tsh).
  forward. (* r->d[2] = t'3 *)
  forward_call (v_l, l, shift, 3, Tsh).
  forward. (* r->d[3] = t'4 *)

  (* ===== round bit: t'5 = l[(shift-1) >> 6] ===== *)

  assert_PROP (Zlength (uint512_to_val l) = 8) as Hlen by entailer!.
  assert (Hrb_idx : 0 <= (shift - 1) / 64 < 8).
  {
    split.
    - apply Z.div_pos; lia.
    - apply Z.div_lt_upper_bound; lia.
  }
  assert (Hrb : Int.unsigned (Int.shru (Int.repr (shift - 1)) (Int.repr 6)) = (shift - 1) / 64).
  {
    rewrite Int.shru_div_two_p.
    rewrite (Int.unsigned_repr (shift - 1)) by rep_lia.
    rewrite (Int.unsigned_repr 6) by rep_lia.
    rewrite two_p_correct.
    apply Int.unsigned_repr.
    change (two_power_pos _) with 64 in *.
    rep_lia.
  }

  forward.
  - (* tc_val of the loaded round-bit limb (in-bounds is auto-discharged via Hrb) *)
    rewrite Hrb.
    rewrite uint512_to_val_Znth by lia.
    entailer!.
  - (* ===== cadd_bit(r, 0, round bit) ===== *)
    rewrite Hrb.
    rewrite uint512_to_val_Znth by lia.

    (* The 512-bit product, its range, and the rounded-quotient bound. *)
    assert (Hp : u512_val l = scalar_val a * scalar_val b) by (rewrite H1; reflexivity).
    pose proof (scalar_range a) as Ha_rng.
    pose proof (scalar_range b) as Hb_rng.
    assert (Hp_nonneg : 0 <= u512_val l) by (rewrite Hp; apply Z.mul_nonneg_nonneg; lia).
    assert (Hp_lt : u512_val l < secp256k1_N * secp256k1_N)
      by (rewrite Hp; apply Z.mul_lt_mono_nonneg; lia).
    pose proof (mul_shift_bound (u512_val l) shift Hp_nonneg Hp_lt ltac:(lia)) as [Hq_rng Hbound].
    assert (Hround_bnd : 0 <= (u512_val l / 2 ^ (shift - 1)) mod 2 < 2)
      by (apply Z.mod_pos_bound; lia).

    (* Bridge the 4 stored limbs to a [scalar_at] holding [p / 2^shift]. *)
    set (q := u512_val l / 2 ^ shift) in *.
    assert (Hqr : 0 <= q < secp256k1_N) by (subst q; lia).

    assert (Hlist : upd_Znth 3
            (upd_Znth 2
               (upd_Znth 1
                  (upd_Znth 0 (default_val t_secp256k1_uint256)
                     (Vlong (Int64.repr (limb (Z.pow_pos 2 64) q 0))))
                  (Vlong (Int64.repr (limb (Z.pow_pos 2 64) q 1))))
               (Vlong (Int64.repr (limb (Z.pow_pos 2 64) q 2))))
            (Vlong (Int64.repr (limb (Z.pow_pos 2 64) q 3)))
          = scalar_to_val (mkScalar q Hqr)).
    {
      unfold scalar_to_val, limb.
      simpl scalar_val.
      change (Z.pow_pos 2 64) with (2^64).
      cbn [Z.of_nat].
      change ((2^64)^0) with 1.
      change ((2^64)^1) with (2^64).
      change ((2^64)^2) with (2^128).
      change ((2^64)^3) with (2^192).
      rewrite Z.div_1_r.
      reflexivity.
    }

    change (let (q0, _) := Z.div_eucl (u512_val l) (2 ^ shift) in q0) with q.
    match goal with
    | |- context[data_at sh_r t_secp256k1_uint256 ?v r_ptr] =>
        replace v with (scalar_to_val (mkScalar q Hqr)) by (symmetry; apply Hlist)
    end.

    forward_call (r_ptr, mkScalar q Hqr, 0, (u512_val l / 2 ^ (shift - 1)) mod 2, sh_r).
    + (* shift amount of the round bit is < 64 *)
      assert (Hland : Z.land (shift - 1) 63 = (shift - 1) mod 64).
      {
        change 63 with (Z.ones 6).
        rewrite Z.land_ones by lia.
        reflexivity.
      }
      rewrite Hland.
      assert (Hrm : 0 <= (shift - 1) mod 64 < 64) by (apply Z.mod_pos_bound; lia).
      rewrite Int.unsigned_repr by rep_lia.
      change (Int.unsigned Int64.iwordsize') with 64.
      lia.
    + (* the C round-bit expression equals (p / 2^(shift-1)) mod 2 *)
      entailer!.

      simpl firstn.
      unfold eval_cast, sem_cast.
      simpl.
      set (L := limb (Z.pow_pos 2 64) (a * b) (Z.to_nat (let (q0, _) := Z.div_eucl (shift - 1) 64 in q0))).

      assert (HL_rng : 0 <= L < 2^64).
      {
        subst L.
        unfold limb.
        change (Z.pow_pos 2 64) with (2^64).
        apply Z.mod_pos_bound.
        lia.
      }

      assert (Hland : Z.land (shift - 1) 63 = (shift - 1) mod 64).
      {
        change 63 with (Z.ones 6).
        rewrite Z.land_ones by lia.
        reflexivity.
      }
      assert (Hrm : 0 <= (shift - 1) mod 64 < 64) by (apply Z.mod_pos_bound; lia).

      f_equal.
      f_equal.
      f_equal.
      rewrite Hland.
      rewrite (Int.unsigned_repr ((shift - 1) mod 64)) by rep_lia.
      rewrite (Int64.Z_mod_modulus_eq ((shift - 1) mod 64)).
      change Int64.modulus with (2^64).
      rewrite (Zmod_small ((shift - 1) mod 64) (2^64)) by lia.
      rewrite (Int64.Z_mod_modulus_eq L).
      change Int64.modulus with (2^64).
      rewrite (Zmod_small L (2^64)) by lia.
      rewrite Z.shiftr_div_pow2 by lia.
      assert (HLs_rng : 0 <= L / 2^((shift - 1) mod 64) < 2^64).
      {
        split.
        - apply Z.div_pos; [lia | apply Z.pow_pos_nonneg; lia].
        - apply Z.le_lt_trans with L; [apply Z.div_le_upper_bound; [apply Z.pow_pos_nonneg; lia | nia] | lia].
      }
      rewrite (Int64.Z_mod_modulus_eq (L / 2^((shift - 1) mod 64))).
      change Int64.modulus with (2^64).
      rewrite (Zmod_small (L / 2^((shift - 1) mod 64)) (2^64)) by lia.
      rewrite Z.land_ones with (n := 1) by lia.
      change (2^1) with 2.
      rewrite (Int64.Z_mod_modulus_eq ((L / 2^((shift - 1) mod 64)) mod 2)).
      change Int64.modulus with (2^64).
      rewrite (Zmod_small ((L / 2^((shift - 1) mod 64)) mod 2) (2^64))
        by (assert (0 <= (L / 2^((shift - 1) mod 64)) mod 2 < 2) by (apply Z.mod_pos_bound; lia); lia).

      f_equal.
      f_equal.
      subst L.
      change (Z.pow_pos 2 64) with (2^64).
      change (let (q0, _) := Z.div_eucl (shift - 1) 64 in q0) with ((shift - 1) / 64).
      change (let (q0, _) := Z.div_eucl (a * b) (2 ^ (shift - 1)) in q0) with ((a * b) / 2 ^ (shift - 1)).
      apply roundbit_eq.
      * apply Z.mul_nonneg_nonneg; lia.
      * lia.
    + (* postcondition: the returned scalar is scalar_mul_shift a b shift *)
      Intros vret.
      rename H into Hvret.
      Exists vret.
      rewrite !scalar_to_val_eq.
      entailer!.
      rewrite Hvret.
      unfold scalar_mul_shift.
      simpl scalar_val.
      subst q.
      rewrite Hp.
      change (2^0) with 1.
      lia.
Qed.
