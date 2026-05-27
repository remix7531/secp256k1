(** * Verif_i128_dissip_mul: Proof of body_secp256k1_i128_dissip_mul *)
(** Copyright (C) 2026 remix7531
    SPDX-License-Identifier: MIT *)

Require Import secp256k1.vst.base.
Require Import secp256k1.contract.helper.notations.
Require Import secp256k1.contract.gprog.int128.
Require Import secp256k1.contract.impl.int128.
Require Import secp256k1.tactics.core.
Require Import secp256k1.tactics.int128.

(* ================================================================= *)
(** ** secp256k1_i128_dissip_mul -- [r -= a*b]. *)

(** Borrow recombination for the 128-bit limb subtraction
    ([arith_div_sub_borrow]: subtracting [Q] from [R] limb-by-limb, the high
    limb is [R/M - Q/M] decremented by the borrow [R mod M < Q mod M])
    is the pure-Z [theory/arithmetic.v] lemma, used here at [M = 2^64];
    its additive sibling [arith_div_add_carry] serves [i128_accum_mul]. *)

(** The C [hi += r->lo < lo] cannot overflow [int64].  The product
    [a*b] has magnitude at most [2^126], so its high limb [a*b / 2^64]
    lies in [[-2^62, 2^62]], leaving room for the [0, 1] borrow.  The
    borrow is passed abstractly as [d]. *)
Lemma dissip_hi_no_overflow : forall a b d : Z,
  -2^63 <= a < 2^63 ->
  -2^63 <= b < 2^63 ->
  0 <= d <= 1 ->
  Int64.min_signed <= Int64.signed (Int64.repr (a * b / 2^64)) + d
  <= Int64.max_signed.
Proof.
  intros a b d Ha Hb Hd.
  assert (HP : Z.abs (a * b) <= 2^126).
  { assert (Haa : Z.abs a <= 2^63) by (rewrite Z.abs_le; lia).
    assert (Hbb : Z.abs b <= 2^63) by (rewrite Z.abs_le; lia).
    rewrite Z.abs_mul.
    change (2^126) with (2^63 * 2^63).
    apply Z.mul_le_mono_nonneg; try apply Z.abs_nonneg; assumption. }
  assert (Hqb : -2^62 <= a * b / 2^64 <= 2^62).
  { rewrite Z.abs_le in HP.
    split.
    - apply Z.le_trans with (-2^126 / 2^64);
        [reflexivity | apply Z.div_le_mono; lia].
    - apply Z.le_trans with (2^126 / 2^64);
        [apply Z.div_le_mono; lia | reflexivity]. }
  rewrite Int64.signed_repr
    by (change Int64.min_signed with (-2^63);
        change Int64.max_signed with (2^63 - 1); lia).
  change Int64.min_signed with (-2^63).
  change Int64.max_signed with (2^63 - 1).
  lia.
Qed.

Lemma body_secp256k1_i128_dissip_mul :
  semax_body Vprog Gprog
    f_secp256k1_i128_dissip_mul spec_secp256k1_i128_dissip_mul.
Proof.
  start_function.

  (* lo = (uint64_t)secp256k1_mul128(a, b, &hi): writes hi := (a*b)/2^64,
     returns the low limb (a*b) mod 2^64 as the temp [lo]. *)
  forward_call (a, b, v_hi, Tsh).

  (* hi += r->lo < lo: fold the old low limb's borrow into hi. *)
  forward. (* _t'5 = hi *)
  forward. (* _t'6 = r->lo *)
  forward. (* hi = _t'5 + (_t'6 < lo) -- typecheck: hi stays in int64 *)
  { (* no overflow in [hi += borrow]: |a*b/2^64| <= 2^62, borrow in {0,1} *)
    entailer!.
    change (Z.pow_pos 2 64) with (2^64).
    change (let (q, _) := Z.div_eucl (i64_val a * i64_val b) (2^64) in q)
      with (i64_val a * i64_val b / 2^64).
    rewrite Int.signed_repr by (destruct (Int64.ltu _ _); simpl Z.b2z; rep_lia).
    apply dissip_hi_no_overflow; try apply i64_range.
    destruct (Int64.ltu _ _).
    - (* branch: borrow = 1 *)
      simpl Z.b2z.
      lia.
    - (* branch: borrow = 0 *)
      simpl Z.b2z.
      lia. }

  (* r->hi -= hi: unsigned limb subtraction (no overflow obligation). *)
  forward. (* _t'3 = r->hi *)
  forward. (* _t'4 = hi *)
  forward. (* r->hi = _t'3 - _t'4 *)

  (* r->lo -= lo *)
  forward. (* _t'2 = r->lo *)
  forward. (* r->lo = _t'2 - lo *)

  (* ===== Postcondition: the difference fits, the struct matches its repr ===== *)
  Exists (mkInt128 (i128_val r - i64_val a * i64_val b) (conj H H0)).
  entailer!.
  apply derives_refl'.
  unfold int128_to_val.
  change (Z.pow_pos 2 64) with (2^64).
  f_equal.
  rewrite !i128_val_mk.
  fold (Z.div (i128_val r) (2^64)).
  fold (Z.div (i64_val a * i64_val b) (2^64)).
  f_equal.

  - (* low word: (r mod 2^64 - a*b) and (r - a*b) mod 2^64 agree mod 2^64 *)
    f_equal.
    apply Int64.eqm_samerepr.
    apply eqm_of_mod_eq.
    rewrite Zminus_mod_idemp_l.
    reflexivity.

  - (* high word: borrow recombination gives the high limb of r - a*b *)
    f_equal.
    set (Rlo := i128_val r mod 2^64) in *.
    set (P := i64_val a * i64_val b) in *.
    assert (HRlo : 0 <= Rlo < 2^64) by (subst Rlo; apply Z.mod_pos_bound; lia).
    assert (Hltu : Int64.ltu (Int64.repr Rlo) (Int64.repr P)
                   = (Rlo <? P mod 2^64)).
    { unfold Int64.ltu.
      rewrite !Int64.unsigned_repr_eq.
      change Int64.modulus with (2^64).
      rewrite (Z.mod_small Rlo (2^64)) by lia.
      destruct (zlt Rlo (P mod 2^64)) as [Hl|Hl].
      - symmetry. apply Z.ltb_lt. lia.
      - symmetry. apply Z.ltb_ge. lia. }
    rewrite Hltu.
    assert (Hsig : Int.signed (Int.repr (Z.b2z (Rlo <? P mod 2^64)))
                   = Z.b2z (Rlo <? P mod 2^64)).
    { apply Int.signed_repr. destruct (Rlo <? P mod 2^64); simpl; rep_lia. }
    rewrite Hsig.
    f_equal.
    subst Rlo.
    apply arith_div_sub_borrow.
    lia.
Qed.
