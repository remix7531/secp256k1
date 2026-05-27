(** * Verif_mul128: Proof of body_secp256k1_mul128 *)
(** Copyright (C) 2026 remix7531
    SPDX-License-Identifier: MIT *)

Require Import secp256k1.vst.base.
Require Import secp256k1.contract.helper.notations.
Require Import secp256k1.contract.gprog.int128.
Require Import secp256k1.contract.impl.int128.
Require Import secp256k1.tactics.core.
Require Import secp256k1.tactics.int128.

(* ================================================================= *)
(** ** secp256k1_mul128 -- [64x64 -> 128 signed product]. *)

(** Signed 64x64 -> 128 multiply built from 32-bit pieces and shifts; this
    is the signed twin of [secp256k1_umul128]. Mirrors the limb-arithmetic
    pattern in [verif/int128/impl/umul128.v], adapted to signed high halves:
    the [(a >> 32)] / [(b >> 32)] sub-expressions are arithmetic (signed)
    shifts, so the high halves [a / 2^32] / [b / 2^32] are signed, and the
    result high word is the signed quotient [(a * b) / 2^64]. *)

(** The [Int64.shru]/[Int64.shl] by 32 bridges ([Int64_shru_32],
    [Int64_shl_32]) and the signed [Int64.shr]-to-[/] bridge
    ([Int64_shr_div]) live in [tactics/core.v]; they are shared
    with the unsigned [umul128] helper and the [i128] shifts.  The
    manual set rule for the signed-shift multiplicands ([mul_set])
    lives in [tactics/int128.v]. *)

(* ----------------------------------------------------------------- *)
(** *** Shift/cast bridges -- [Int64_signed_shr_32] / [Int_cast_u32]. *)

(** Arithmetic (signed) right shift by 32 on a value in [Int64] range
    equals signed Z division [x / 2^32] (floor). *)
Lemma Int64_signed_shr_32 : forall x,
  -2^63 <= x < 2^63 ->
  Int64.signed (Int64.shr (Int64.repr x) (Int64.repr 32)) = x / 2^32.
Proof.
  intros x Hx.
  assert (Hd : -2^31 <= x / 2^32 < 2^31)
    by (split; [apply Z.div_le_lower_bound; lia | apply Z.div_lt_upper_bound; lia]).
  rewrite (Int64_shr_div x 32) by lia.
  apply Int64.signed_repr.
  change Int64.min_signed with (-2^63).
  change Int64.max_signed with (2^63-1).
  lia.
Qed.

(** A 32-bit unsigned cast [(uint32_t)x] reads the low 32 bits of the
    two's-complement value [x mod 2^64], i.e. [x mod 2^32]. *)
Lemma Int_cast_u32 : forall x,
  Int.unsigned (Int.repr (Int64.Z_mod_modulus x)) = x mod 2^32.
Proof.
  intros x.
  rewrite Int64.Z_mod_modulus_eq.
  rewrite Int.unsigned_repr_eq.
  change Int.modulus with (2^32).
  change Int64.modulus with (2^64).
  symmetry.
  rewrite <- Zmod_div_mod; [reflexivity | lia | lia | exists (2^32); reflexivity].
Qed.

(* ----------------------------------------------------------------- *)
(** *** Signed-overflow side conditions for the cross products.

    The four 32x32 products fit in a signed [int64]: a low half is in
    [[0, 2^32)] and a high half is in [[-2^31, 2^31)], so each product
    lies in [(-2^63, 2^63)] and the [tc_expr] no-signed-overflow goal
    holds. One lemma per [forward]-generated shape. *)

Lemma ovf_lh : forall av bv,
  -2^63 <= av < 2^63 -> -2^63 <= bv < 2^63 ->
  Int64.min_signed <=
  Int.unsigned (Int.repr (Int64.Z_mod_modulus av)) *
  Int64.signed
    (Int64.shr (Int64.repr bv) (Int64.repr (Int.unsigned (Int.repr 32))))
  <= Int64.max_signed.
Proof.
  intros av bv Hav Hbv.
  change (Int.unsigned (Int.repr 32)) with 32.
  rewrite Int_cast_u32.
  rewrite Int64_signed_shr_32 by lia.
  assert (Hlo : 0 <= av mod 2^32 < 2^32) by (apply Z.mod_pos_bound; lia).
  assert (Hhi : -2^31 <= bv / 2^32 < 2^31)
    by (split; [apply Z.div_le_lower_bound; lia | apply Z.div_lt_upper_bound; lia]).
  change Int64.min_signed with (-2^63).
  change Int64.max_signed with (2^63-1).
  nia.
Qed.

(** Identity: a 32-bit unsigned cast of an already-32-bit value is the
    identity (used to normalise the [hl] no-overflow goal after [cbn]). *)
Lemma cast_int_int_I32_id : forall x, cast_int_int I32 Unsigned x = x.
Proof. intros. reflexivity. Qed.

(** No-overflow bound for [hl] in the exact shape left after the manual set
    decomposition reduces the [tc_expr] (the [(uint32_t)b] operand appears as
    [cast_int_int I32 Unsigned (Int.repr (Int64.unsigned ...))], and the shift
    amount as the literal 32). *)
Lemma ovf_hl_cbn : forall av bv,
  -2^63 <= av < 2^63 -> -2^63 <= bv < 2^63 ->
  Int64.min_signed <=
  Int64.signed (Int64.shr (Int64.repr av) (Int64.repr 32)) *
  Int.unsigned (cast_int_int I32 Unsigned (Int.repr (Int64.unsigned (Int64.repr bv))))
  <= Int64.max_signed.
Proof.
  intros av bv Hav Hbv.
  rewrite cast_int_int_I32_id.
  rewrite Int.unsigned_repr_eq.
  change Int.modulus with (2^32).
  rewrite Int64.unsigned_repr_eq.
  change Int64.modulus with (2^64).
  rewrite (Int64_signed_shr_32 av) by lia.
  assert (Hhi : -2^31 <= av / 2^32 < 2^31)
    by (split; [apply Z.div_le_lower_bound; lia | apply Z.div_lt_upper_bound; lia]).
  assert (Hlo : 0 <= (bv mod 2^64) mod 2^32 < 2^32) by (apply Z.mod_pos_bound; lia).
  change Int64.min_signed with (-2^63).
  change Int64.max_signed with (2^63-1).
  nia.
Qed.

(** No-overflow bound for [hh] in the post-[cbn] shape (both operands are
    signed shifts; no cast). *)
Lemma ovf_hh_cbn : forall av bv,
  -2^63 <= av < 2^63 -> -2^63 <= bv < 2^63 ->
  Int64.min_signed <=
  Int64.signed (Int64.shr (Int64.repr av) (Int64.repr 32)) *
  Int64.signed (Int64.shr (Int64.repr bv) (Int64.repr 32))
  <= Int64.max_signed.
Proof.
  intros av bv Hav Hbv.
  rewrite (Int64_signed_shr_32 av) by lia.
  rewrite (Int64_signed_shr_32 bv) by lia.
  assert (Hav2 : -2^31 <= av / 2^32 < 2^31)
    by (split; [apply Z.div_le_lower_bound; lia | apply Z.div_lt_upper_bound; lia]).
  assert (Hbv2 : -2^31 <= bv / 2^32 < 2^31)
    by (split; [apply Z.div_le_lower_bound; lia | apply Z.div_lt_upper_bound; lia]).
  change Int64.min_signed with (-2^63).
  change Int64.max_signed with (2^63-1).
  nia.
Qed.

(* ----------------------------------------------------------------- *)
(** *** Signed schoolbook glue -- [signed_school]. *)

(** The mid-accumulator variant of 2x2 schoolbook multiplication, with a
    SIGNED high half. Given base [B > 0], low halves [alo, blo] in [[0, B)]
    and arbitrary (possibly negative) high halves [ahi, bhi], the C code
    computes:
    - [mid := alo*blo / B + (alo*bhi) mod B + (ahi*blo) mod B]
    - [lo  := mid * B + (alo*blo) mod B]
    - [hi  := ahi*bhi + (alo*bhi) / B + (ahi*blo) / B + mid / B]

    where every [mod] / [/] is the Euclidean one (matching C's unsigned
    32-bit cast and arithmetic-shift respectively). For [av = ahi*B + alo],
    [bv = bhi*B + blo] this yields [lo mod B^2 = (av*bv) mod B^2] (the low
    64-bit return) and [hi = (av*bv) / B^2] (the signed high word). The
    algebra is identical to the unsigned [schoolbook_mul_2x2_mid]; only the
    sign constraints on the high halves are relaxed. *)
Lemma signed_school :
  forall B, B > 0 ->
  forall alo blo ahi bhi,
  0 <= alo < B -> 0 <= blo < B ->
  let mid := alo * blo / B + (alo * bhi) mod B + (ahi * blo) mod B in
  let lo := mid * B + (alo * blo) mod B in
  let hi := ahi * bhi + (alo * bhi) / B + (ahi * blo) / B + mid / B in
  let av := ahi * B + alo in
  let bv := bhi * B + blo in
  lo mod (B * B) = (av * bv) mod (B * B) /\
  hi = (av * bv) / (B * B).
Proof.
  intros B HB alo blo ahi bhi Halo Hblo mid lo hi av bv.
  assert (Hprod : av * bv = alo*blo + (alo*bhi + ahi*blo)*B + ahi*bhi*B*B)
    by (subst av bv; ring).
  set (acc1 := alo*blo/B + alo*bhi + ahi*blo).
  split.

  (* conjunct 0: lo mod B^2 = product mod B^2 *)
  - subst lo.
    rewrite (Z_div_mod_eq_full mid B) at 1.
    replace ((B * (mid / B) + mid mod B) * B + (alo * blo) mod B)
      with ((alo * blo) mod B + mid mod B * B + mid / B * (B * B)) by ring.
    rewrite Z_mod_plus_full.
    subst mid.
    rewrite mod_add_residues_eq by lia.
    fold acc1.
    rewrite <- (low_digits_mod_sq B (av*bv)) by lia.
    (* side goal of [Zmod_small]: both digits are < B, so the pair is < B^2 *)
    assert (Hlo_bnd : 0 <= (alo*blo) mod B < B) by (apply Z.mod_pos_bound; lia).
    assert (Hacc1_bnd : 0 <= acc1 mod B < B) by (apply Z.mod_pos_bound; lia).
    rewrite Zmod_small by nia.
    rewrite Hprod.
    f_equal.
    + (* low digit: (alo*blo) mod B = (av*bv) mod B *)
      symmetry.
      replace (alo * blo + (alo * bhi + ahi * blo) * B + ahi * bhi * B * B)
        with (alo*blo + ((alo*bhi+ahi*blo) + ahi*bhi*B)*B) by ring.
      rewrite Z_mod_plus_full.
      reflexivity.
    + (* next digit: acc1 mod B = ((av*bv)/B) mod B *)
      f_equal.
      replace (alo * blo + (alo * bhi + ahi * blo) * B + ahi * bhi * B * B)
        with (alo*blo + (alo*bhi + ahi*blo + ahi*bhi*B)*B) by ring.
      rewrite Z.div_add by lia.
      unfold acc1.
      replace (alo * blo / B + (alo * bhi + ahi * blo + ahi * bhi * B))
        with ((alo * blo / B + alo * bhi + ahi * blo) + ahi*bhi*B) by ring.
      rewrite Z_mod_plus_full.
      reflexivity.

  (* conjunct 1: hi = product / B^2 *)
  - subst hi.
    replace (ahi * bhi + alo * bhi / B + ahi * blo / B + mid / B)
      with (ahi * bhi + (alo * bhi / B + ahi * blo / B + mid / B)) by ring.
    subst mid.
    rewrite <- (div_sum_carry_split B (alo*blo/B) (alo*bhi) (ahi*blo)) by lia.
    fold acc1.
    rewrite Hprod.
    replace (alo*blo + (alo*bhi + ahi*blo) * B + ahi*bhi * B * B)
      with (ahi*bhi * (B * B) + ((alo*bhi + ahi*blo) * B + alo*blo)) by ring.
    rewrite Z.div_add_l by lia.
    f_equal.
    rewrite <- Z.div_div by lia.
    replace ((alo * bhi + ahi * blo) * B + alo * blo)
      with (acc1 * B + (alo * blo) mod B)
      by (subst acc1; pose proof (Z_div_mod_eq_full (alo*blo) B); nia).
    rewrite Z.div_add_l by lia.
    pose proof (Z.mod_pos_bound (alo*blo) B ltac:(lia)).
    rewrite (Z.div_small ((alo*blo) mod B) B) by lia.
    rewrite Z.add_0_r.
    reflexivity.
Qed.

Lemma body_secp256k1_mul128 :
  semax_body Vprog Gprog
    f_secp256k1_mul128 spec_secp256k1_mul128.
Proof.
  start_function.

  (* ===== Stage 0: 32-bit partial products ll/lh/hl/hh and mid34 ===== *)

  (* ll = (uint64_t)(uint32_t)a * (uint32_t)b *)
  forward.
  (* lh = (uint32_t)a * (b >> 32) (cast-on-left: plain forward, ovf side goal) *)
  forward.
  { entailer!.
    apply ovf_lh; rep_lia. }
  (* hl = (a >> 32) * (uint32_t)b (signed shift on left: manual set) *)
  mul_set ovf_hl_cbn.
  (* hh = (a >> 32) * (b >> 32) (signed shifts: manual set) *)
  mul_set ovf_hh_cbn.
  (* mid34 = (ll >> 32) + (uint32_t)lh + (uint32_t)hl (unsigned: plain forward) *)
  forward.

  (* ===== Normalize the five temps to [Int64.repr (clean Z)] form =====
     Plain [forward] on the [*hi] store / [return] diverges while the temps
     are nested [Int64.shr]/[Int64.mul] terms; rewriting them to
     [Int64.repr (<Z>)] (as the unsigned [umul128] does) makes [forward] and
     [entailer!] tractable. *)
  unfold int64_to_val in *.
  set (av := i64_val a) in *.
  set (bv := i64_val b) in *.
  assert (Hav : -2^63 <= av < 2^63) by (subst av; apply i64_range).
  assert (Hbv : -2^63 <= bv < 2^63) by (subst bv; apply i64_range).
  assert (Hshr : forall x, -2^63 <= x < 2^63 ->
    Int64.shr (Int64.repr x) (Int64.repr 32) = Int64.repr (x / 2^32)).
  { intros x Hx.
    apply Int64_shr_div; lia. }
  change (Int.unsigned (Int.repr 32)) with 32 in *.
  rewrite !Int_cast_u32 in *.
  rewrite !(Hshr av Hav) in *.
  rewrite !(Hshr bv Hbv) in *.
  set (a_lo := av mod 2^32) in *.
  set (a_hi := av / 2^32) in *.
  set (b_lo := bv mod 2^32) in *.
  set (b_hi := bv / 2^32) in *.
  rewrite !mul64_repr in *.
  assert (Halo : 0 <= a_lo < 2^32) by (subst a_lo; apply Z.mod_pos_bound; lia).
  assert (Hblo : 0 <= b_lo < 2^32) by (subst b_lo; apply Z.mod_pos_bound; lia).
  assert (Hahi : -2^31 <= a_hi < 2^31)
    by (subst a_hi; split; [apply Z.div_le_lower_bound | apply Z.div_lt_upper_bound]; lia).
  assert (Hbhi : -2^31 <= b_hi < 2^31)
    by (subst b_hi; split; [apply Z.div_le_lower_bound | apply Z.div_lt_upper_bound]; lia).
  assert (Hllr : 0 <= a_lo * b_lo <= Int64.max_unsigned).
  { change Int64.max_unsigned with (2^64-1).
    nia. }
  assert (Hu32 : forall z,
    Int.unsigned (Int.repr (Int64.unsigned (Int64.repr z))) = z mod 2^32).
  { intros z.
    rewrite Int64.unsigned_repr_eq.
    rewrite Int.unsigned_repr_eq.
    change Int.modulus with (2^32).
    change Int64.modulus with (2^64).
    rewrite <- Zmod_div_mod; [reflexivity | lia | lia | exists (2^32); reflexivity]. }
  rewrite (Int64_shru_32 (a_lo * b_lo)) in * by exact Hllr.
  change Int.modulus with (2^32) in *.
  rewrite !Hu32 in *.
  rewrite !add64_repr in *.
  set (mid := a_lo * b_lo / 2 ^ 32 + (a_lo * b_hi) mod 2 ^ 32 +
              (a_hi * b_lo) mod 2 ^ 32) in *.
  assert (Hmid : 0 <= mid < 2 ^ 34).
  { subst mid.
    pose proof (Z.mod_pos_bound (a_lo * b_hi) (2^32) ltac:(lia)).
    pose proof (Z.mod_pos_bound (a_hi * b_lo) (2^32) ltac:(lia)).
    assert (Hd : 0 <= a_lo * b_lo / 2 ^ 32 < 2 ^ 32).
    { split; [apply Z.div_pos; nia | apply Z.div_lt_upper_bound; nia]. }
    lia. }

  (* *hi = hh + (lh >> 32) + (hl >> 32) + (mid34 >> 32) *)
  forward.
  { (* store typecheck: the two signed partial sums stay in int64 range *)
    entailer!.
    assert (Hlhr : -2^63 <= a_lo * b_hi < 2^63) by nia.
    assert (Hhlr : -2^63 <= a_hi * b_lo < 2^63) by nia.
    rewrite (Hshr (a_lo * b_hi) Hlhr).
    rewrite (Hshr (a_hi * b_lo) Hhlr).
    rewrite !add64_repr.
    assert (Hhh2 : -2^62 <= a_hi * b_hi <= 2^62) by nia.
    assert (Hlhq : -2^31 <= (a_lo * b_hi) / 2^32 < 2^31)
      by (split; [apply Z.div_le_lower_bound | apply Z.div_lt_upper_bound]; nia).
    assert (Hhlq : -2^31 <= (a_hi * b_lo) / 2^32 < 2^31)
      by (split; [apply Z.div_le_lower_bound | apply Z.div_lt_upper_bound]; nia).
    rewrite !Int64.signed_repr by rep_lia.
    split; rep_lia. }

  (* return (mid34 << 32) + (uint32_t)ll *)
  forward.

  (* ===== Glue: [signed_school] relates the limbs to (av*bv) lo/hi ===== *)
  pose proof (signed_school (2^32) ltac:(lia) a_lo b_lo a_hi b_hi Halo Hblo) as Hsch.
  cbv zeta in Hsch.
  assert (Hae : a_hi * 2 ^ 32 + a_lo = av).
  { change a_hi with (av / 2 ^ 32).
    change a_lo with (av mod 2 ^ 32).
    pose proof (Z_div_mod_eq_full av (2 ^ 32)).
    lia. }
  assert (Hbe : b_hi * 2 ^ 32 + b_lo = bv).
  { change b_hi with (bv / 2 ^ 32).
    change b_lo with (bv mod 2 ^ 32).
    pose proof (Z_div_mod_eq_full bv (2 ^ 32)).
    lia. }
  fold mid in Hsch.
  rewrite Hae, Hbe in Hsch.
  change (2 ^ 32 * 2 ^ 32) with (2 ^ 64) in Hsch.
  destruct Hsch as [Hlo Hhi].
  assert (Hlhr : -2^63 <= a_lo * b_hi < 2^63) by nia.
  assert (Hhlr : -2^63 <= a_hi * b_lo < 2^63) by nia.
  assert (Hmidu : 0 <= mid <= Int64.max_unsigned)
    by (change Int64.max_unsigned with (2^64-1); lia).
  assert (Hhv : i64_val (i128_hi (mul_i64 a b)) = av * bv / 2^64) by reflexivity.

  (* return value: [mid * 2^32 + (a_lo*b_lo) mod 2^32 = av*bv] modulo 2^64 *)
  assert (Hret : Int64.add (Int64.shl (Int64.repr mid) (Int64.repr 32))
                   (Int64.repr (Int.unsigned (Int.repr (a_lo * b_lo))))
                 = Int64.repr (av * bv)).
  { rewrite (Int64_shl_32 mid Hmidu).
    rewrite Int.unsigned_repr_eq.
    change Int.modulus with (2 ^ 32).
    rewrite add64_repr.
    apply Int64.eqm_samerepr.
    apply Int64.eqm_trans
      with ((mid * 2 ^ 32 + (a_lo * b_lo) mod 2 ^ 32) mod Int64.modulus).
    - apply eqmod_mod. rep_lia.
    - change Int64.modulus with (2 ^ 64).
      rewrite Hlo.
      apply eqmod_sym. apply eqmod_mod. rep_lia. }

  (* stored high word: the four-term sum is [(av*bv) / 2^64] *)
  assert (Hstore : Int64.add
                     (Int64.add
                        (Int64.add (Int64.repr (a_hi * b_hi))
                           (Int64.shr (Int64.repr (a_lo * b_hi)) (Int64.repr 32)))
                        (Int64.shr (Int64.repr (a_hi * b_lo)) (Int64.repr 32)))
                     (Int64.shru (Int64.repr mid) (Int64.repr 32))
                   = Int64.repr (i64_val (i128_hi (mul_i64 a b)))).
  { rewrite (Hshr (a_lo * b_hi) Hlhr).
    rewrite (Hshr (a_hi * b_lo) Hhlr).
    rewrite (Int64_shru_32 mid Hmidu).
    change Int.modulus with (2 ^ 32).
    rewrite !add64_repr.
    rewrite Hhi.
    rewrite Hhv.
    reflexivity. }

  rewrite Hret, Hstore.
  entailer!.
Qed.
