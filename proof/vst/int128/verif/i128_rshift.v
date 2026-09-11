(** * Verif_i128_rshift: Proof of body_secp256k1_i128_rshift *)
(** Copyright (C) 2026 remix7531
    SPDX-License-Identifier: MIT *)

Require Import secp256k1.vst.base.
Require Import secp256k1.vst.helper.notations.
Require Import secp256k1.vst.gprog.
Require Import secp256k1.vst.tactics.core.
Require Import secp256k1.vst.tactics.int128.

(* ================================================================= *)
(** ** secp256k1_i128_rshift -- [r = r / 2^n] (arithmetic). *)

(** Arithmetic right shift by a general [n] in [0, 128).  The C body has
    three reachable cases: [n >= 64] (shift the high limb, broadcast the
    sign), [0 < n < 64] (recombine the limbs), and [n = 0] (no-op).  In all
    cases the result is the signed floor division [i128_val r / 2^n].

    The arithmetic primitive is: a signed right shift by [k] equals signed
    floor division by [2^k].  The helper lemmas below capture (1) that the
    result value stays in [Int128] range, (2) the [Int64.shr]-to-[/] bridge,
    and (3) the sign-extension limb collapses to [-1] / [0]. *)

(** The shifted value [v / 2^m] of any in-range [v] stays in [Int128] range:
    dividing by [2^m >= 1] never increases magnitude. *)
Lemma i128_rshift_div_range (v m : Z) :
  -2^127 <= v < 2^127 ->
  0 <= m ->
  -2^127 <= v / 2^m < 2^127.
Proof.
  intros Hv Hm.
  assert (Hp : 1 <= 2^m).
  { change 1 with (2^0).
    apply Z.pow_le_mono_r; lia. }
  split.
  - apply Z.div_le_lower_bound; [lia | nia].
  - assert (v / 2^m <= 2^127 - 1) by (apply Z.div_le_upper_bound; [lia | nia]).
    lia.
Qed.

(** The signed high limb [v / 2^64] of an in-range [Int128] fits in a signed
    64-bit word.  Stated with symbolic powers so [lia] can connect it to the
    [2^64] / [2^63] forms in the body goals. *)
Lemma i128_rshift_hi_range (v : Z) :
  -2^127 <= v < 2^127 ->
  -2^63 <= v / 2^64 < 2^63.
Proof.
  intros Hv.
  split.
  - apply Z.div_le_lower_bound; [lia | ].
    change (2^64 * -2^63) with (-2^127).
    lia.
  - apply Z.div_lt_upper_bound; [lia | ].
    change (2^64 * 2^63) with (2^127).
    lia.
Qed.

(** The signed [Int64.shr]-to-[/] bridge ([Int64_shr_div], a signed
    64-bit arithmetic right shift is signed floor division by [2^k])
    lives in [vst/tactics/core.v]; it is shared with the [int128]
    multiply helpers and [i128_from_i64]. *)

(** Dividing an in-range signed value by a power of two at least as large as
    its magnitude bound collapses to the sign indicator [-1] / [0].  Used to
    show the stored high limb (the broadcast sign) matches the quotient's
    high limb. *)
Lemma i128_rshift_sign_div (z p : Z) :
  0 < p ->
  -p <= z < p ->
  z / p = (if z <? 0 then -1 else 0).
Proof.
  intros Hp Hzp.
  destruct (Z.ltb_spec z 0) as [Hneg | Hpos].
  - replace z with ((z + p) + (-1) * p) by lia.
    rewrite Z.div_add by lia.
    rewrite Z.div_small by lia.
    lia.
  - apply Z.div_small; lia.
Qed.

(** The [n = 0] / [0 < n < 64] / [n >= 64] cascade all yield
    [i128_val r' = i128_val r / 2^n]. *)
Lemma body_secp256k1_i128_rshift :
  semax_body Vprog Gprog
    f_secp256k1_i128_rshift spec_secp256k1_i128_rshift.
Proof.
  start_function.

  (* the shift amount [n] is in [0, 128): [Hn_lo] / [Hn_hi] bound it,
     and the [forward_if] cascade splits on it. *)
  rename H into Hn_lo.
  rename H0 into Hn_hi.
  (* if (n >= 64) *)
  forward_if.
  - (* branch: n >= 64 -- lo = hi >> (n-64), hi = sign-broadcast *)
    rename H into Hn_ge.

    (* ===== Stage 1: walk the C (shift the high limb, broadcast sign) ===== *)

    forward. (* _t'5 = r->hi *)
    forward. (* r->lo = (int64)_t'5 >> (n - 64) *)
    { (* typecheck: shift amount n - 64 in [0, 64) *)
      entailer!.
      change (Int.unsigned Int64.iwordsize') with 64.
      lia. }
    forward. (* _t'4 = r->hi *)
    forward. (* r->hi = (int64)_t'4 >> 63 *)

    (* ===== Stage 2: supply the result witness [v / 2^n] ===== *)

    pose proof (i128_range r) as Hr.
    pose proof (i128_rshift_hi_range (i128_val r) Hr) as Hhi.
    refold_div.
    Exists (mkInt128 (i128_val r / 2^n) (i128_rshift_div_range (i128_val r) n Hr Hn_lo)).
    entailer!.

    (* ===== Stage 3: the stored limbs match the limbs of [v / 2^n] ===== *)

    apply derives_refl'.
    f_equal.
    unfold int128_to_val.
    cbn [i128_val].
    change (Z.pow_pos 2 64) with (2^64).

    (* shifting the high limb by [n-64] is dividing the whole value by [2^n] *)
    assert (Hdiv : i128_val r / 2^64 / 2^(n - 64) = i128_val r / 2^n).
    { rewrite Z.div_div by (try lia; apply Z.pow_pos_nonneg; lia).
      rewrite <- Z.pow_add_r by lia.
      do 2 f_equal.
      lia. }

    f_equal.
    + (* low word: (int64)hi >> (n-64) = (v / 2^n) mod 2^64 *)
      f_equal.
      rewrite Int64_shr_div by lia.
      rewrite Hdiv.
      rewrite Int64.eqm_samerepr
        with (x := i128_val r / 2^n) (y := (i128_val r / 2^n) mod 2^64).
      * reflexivity.
      * unfold Int64.eqm.
        change Int64.modulus with (2^64).
        apply Zbits.eqmod_mod.
        lia.
    + (* high word: (int64)hi >> 63 = sign = (v / 2^n) / 2^64 *)
      f_equal.
      rewrite Int64_shr_div by lia.
      f_equal.

      (* [v / 2^n] fits in a signed 64-bit word, so its sign bit is its
         whole high limb *)
      assert (Hw : -2^63 <= i128_val r / 2^n < 2^63).
      { rewrite <- Hdiv.
        assert (Hp : 0 < 2^(n - 64)) by (apply Z.pow_pos_nonneg; lia).
        split.
        - apply Z.div_le_lower_bound; [lia | nia].
        - apply Z.div_lt_upper_bound; [lia | nia]. }

      rewrite (i128_rshift_sign_div (i128_val r / 2^64) (2^63)) by (try lia; exact Hhi).
      rewrite (i128_rshift_sign_div (i128_val r / 2^n) (2^64)) by (try lia; split; lia).

      (* the two sign indicators agree: dividing further by [2^(n-64)] never
         crosses zero *)
      assert (Hsig : (i128_val r / 2^64 <? 0) = (i128_val r / 2^n <? 0)).
      { rewrite <- Hdiv.
        assert (Hp : 0 < 2^(n - 64)) by (apply Z.pow_pos_nonneg; lia).
        destruct (Z.ltb_spec (i128_val r / 2^64) 0) as [Hlt | Hge];
        destruct (Z.ltb_spec (i128_val r / 2^64 / 2^(n - 64)) 0) as [Hlt2 | Hge2];
        try reflexivity.
        - exfalso.
          assert (i128_val r / 2^64 / 2^(n - 64) < 0)
            by (apply Z.div_lt_upper_bound; [lia | nia]).
          lia.
        - exfalso.
          assert (0 <= i128_val r / 2^64 / 2^(n - 64))
            by (apply Z.div_pos; lia).
          lia. }

      rewrite Hsig.
      reflexivity.
  - (* branch: n < 64 -- split off the no-op [n = 0] *)
    rename H into Hn_lt.
    (* if (n > 0) *)
    forward_if.
    + (* branch: 0 < n < 64 -- recombine the two limbs *)
      rename H into Hn_pos.

      (* ===== Stage 1: walk the C (recombine lo, shift hi) ===== *)

      forward. (* _t'2 = r->hi *)
      forward. (* _t'3 = r->lo *)
      forward. (* r->lo = (hi << (64 - n)) | (lo >> n) *)
      { (* typecheck: shift amounts 64 - n and n in [0, 64) *)
        entailer!.
        change (Int.unsigned Int64.iwordsize') with 64.
        lia. }
      forward. (* _t'1 = r->hi *)
      forward. (* r->hi = (int64)_t'1 >> n *)

      (* ===== Stage 2: supply the result witness [v / 2^n] ===== *)

      pose proof (i128_range r) as Hr.
      pose proof (i128_rshift_hi_range (i128_val r) Hr) as Hhi.
      assert (Hlo : 0 <= i128_val r mod 2^64 < 2^64) by (apply Z.mod_pos_bound; lia).
      refold_div.
      Exists (mkInt128 (i128_val r / 2^n) (i128_rshift_div_range (i128_val r) n Hr Hn_lo)).
      entailer!.

      (* ===== Stage 3: the recombined limbs match the limbs of [v / 2^n] ===== *)

      apply derives_refl'.
      f_equal.
      unfold int128_to_val.
      cbn [i128_val].
      change (Z.pow_pos 2 64) with (2^64).
      f_equal.
      * (* low word: (hi << (64-n)) | (lo >> n) = (v / 2^n) mod 2^64 *)
        (* the shift amounts as plain [Z]s *)
        assert (Hn64 : Int64.unsigned (Int64.repr n) = n)
          by (apply Int64.unsigned_repr;
              change Int64.max_unsigned with (2^64 - 1); lia).
        assert (Hlo64 : Int64.unsigned (Int64.repr (i128_val r mod 2^64))
                        = i128_val r mod 2^64)
          by (apply Int64.unsigned_repr;
              change Int64.max_unsigned with (2^64 - 1); lia).

        (* the low half [(lo >> n)] fits below bit [64 - n] -- the [or] is an add *)
        assert (Hy : Int64.unsigned
                       (Int64.shru (Int64.repr (i128_val r mod 2^64)) (Int64.repr n))
                     < two_p (64 - n)).
        { rewrite Int64.shru_div_two_p.
          rewrite Hn64, Hlo64.
          rewrite ?two_p_correct.
          rewrite Int64.unsigned_repr.
          - apply Z.div_lt_upper_bound.
            + apply Z.pow_pos_nonneg; lia.
            + rewrite <- Z.pow_add_r by lia.
              replace (n + (64 - n)) with 64 by lia.
              lia.
          - change Int64.max_unsigned with (2^64 - 1).
            split.
            + apply Z.div_pos; [lia | apply Z.pow_pos_nonneg; lia].
            + apply Z.le_trans with (i128_val r mod 2^64).
              * apply Z.div_le_upper_bound; [apply Z.pow_pos_nonneg; lia | nia].
              * lia. }

        f_equal.

        (* with the low half below bit [64 - n], the bitwise [or] is an add *)
        rewrite (Int64.shifted_or_is_add _ _ (64 - n))
          by (try (change Int64.zwordsize with 64; lia); exact Hy).
        rewrite Int64.shru_div_two_p.
        rewrite ?two_p_correct.
        rewrite Hn64, Hlo64.
        rewrite Int64.unsigned_repr_eq.
        change Int64.modulus with (2^64).

        (* the [(lo >> n)] limb is already in unsigned range *)
        assert (Hq : Int64.unsigned (Int64.repr (i128_val r mod 2^64 / 2^n))
                     = i128_val r mod 2^64 / 2^n).
        { apply Int64.unsigned_repr.
          change Int64.max_unsigned with (2^64 - 1).
          split.
          - apply Z.div_pos; [lia | apply Z.pow_pos_nonneg; lia].
          - apply Z.le_trans with (i128_val r mod 2^64).
            + apply Z.div_le_upper_bound; [apply Z.pow_pos_nonneg; lia | nia].
            + lia. }

        rewrite Hq.

        (* reduce to an [eqm] (= [eqmod 2^64]) goal *)
        apply Int64.eqm_samerepr.
        unfold Int64.eqm.
        change Int64.modulus with (2^64).

        (* the recombination is exactly the floor-division split of [v / 2^n] *)
        assert (Hsplit : forall v m, 0 < m < 64 ->
                  v / 2^m = v / 2^64 * 2^(64 - m) + (v mod 2^64) / 2^m).
        { clear.
          intros v m Hm.
          assert (Hpm : 2^64 = 2^(64 - m) * 2^m)
            by (rewrite <- Z.pow_add_r by lia; f_equal; lia).
          assert (Hmod : v mod 2^64 = v + (- (2^(64 - m) * (v / 2^64))) * 2^m).
          { rewrite Z.mod_eq by (apply Z.pow_nonzero; lia).
            rewrite Hpm at 1.
            ring. }
          rewrite Hmod.
          rewrite Z.div_add by (apply Z.pow_nonzero; lia).
          rewrite (Z.mul_comm (v / 2^64) (2^(64 - m))).
          lia. }

        rewrite (Hsplit (i128_val r) n) by lia.

        (* the high term only changes by a multiple of [2^64] under [mod] *)
        apply Zbits.eqmod_trans
          with (i128_val r / 2^64 * 2^(64 - n) + i128_val r mod 2^64 / 2^n).
        { apply Zbits.eqmod_add.
          - apply Zbits.eqmod_mult; [ | apply Zbits.eqmod_refl].
            apply Zbits.eqmod_sym.
            apply Zbits.eqmod_mod.
            lia.
          - apply Zbits.eqmod_refl. }

        apply Zbits.eqmod_mod.
        lia.
      * (* high word: (int64)hi >> n = (v / 2^n) / 2^64 *)
        f_equal.
        rewrite Int64_shr_div by lia.
        f_equal.
        (* [(v / 2^64) / 2^n = v / (2^n * 2^64) = (v / 2^n) / 2^64] *)
        rewrite Z.div_div by (try lia; apply Z.pow_pos_nonneg; lia).
        rewrite Z.div_div by (try lia; apply Z.pow_pos_nonneg; lia).
        rewrite (Z.mul_comm (2^64) (2^n)).
        reflexivity.
    + (* branch: n = 0 -- no-op, the value is unchanged *)
      rename H into Hn_zero.
      Intros.
      forward. (* fall-through, no statement *)
      Exists r.
      entailer!.
      (* [n = 0] forces the divisor to [2^0 = 1], so [v / 1 = v] *)
      assert (n = 0) by lia.
      subst n.
      rewrite Z.pow_0_r, Z.div_1_r.
      reflexivity.
Qed.
