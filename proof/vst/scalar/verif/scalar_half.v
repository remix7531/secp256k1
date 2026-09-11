(** * Verif_scalar_half: Proof of body_secp256k1_scalar_half *)
(** Copyright (C) 2026 remix7531
    SPDX-License-Identifier: MIT *)

Require Import secp256k1.vst.base.
Require Import secp256k1.vst.helper.notations.
Require Import secp256k1.vst.gprog.
Require secp256k1.specification.
Import specification.Math.
Import specification.Math.residues.
Require Import secp256k1.vst.tactics.core.
Require Import secp256k1.vst.tactics.int128.
Require Import secp256k1.vst.tactics.scalar.

(* ================================================================= *)
(** ** Bit-level helpers -- [&1] / [-mask] / shifts (file-local). *)

(** [x & 1] on a [uint64] selects the parity bit: [x mod 2]. *)
Lemma and_one_parity : forall v,
  Int64.and (Int64.repr v) (Int64.repr 1) = Int64.repr (v mod 2).
Proof.
  intros v.
  apply Int64.same_bits_eq.
  intros i Hi.
  rewrite Int64.bits_and by lia.
  rewrite !(Int64.testbit_repr) by lia.
  rewrite !Z.testbit_eqb by lia.
  destruct (Z.eqb_spec i 0) as [E|E].
  - subst i.
    change (2^0) with 1.
    rewrite !Z.div_1_r.
    rewrite (Zmod_mod v 2).
    destruct (Z.eqb_spec (v mod 2) 1); reflexivity.
  - assert (H2 : 2 <= 2^i) by (replace 2 with (2^1) by reflexivity; apply Z.pow_le_mono_r; lia).
    assert (Hm : 0 <= v mod 2 < 2) by (apply Z.mod_pos_bound; lia).
    rewrite (Z.div_small 1 (2^i)) by lia.
    rewrite (Z.div_small (v mod 2) (2^i)) by lia.
    simpl.
    rewrite andb_false_r.
    reflexivity.
Qed.

(** The C mask [-(uint64_t)(a&1)] times a constant [c] is [c] when [v] is
    odd and [0] when even. *)
Lemma mask_and_const : forall c v, 0 <= c < 2^64 ->
  Int64.and (Int64.repr c) (Int64.neg (Int64.repr (v mod 2)))
  = Int64.repr (if Z.odd v then c else 0).
Proof.
  intros c v Hc.
  assert (Hpar : v mod 2 = if Z.odd v then 1 else 0)
    by (rewrite Zmod_odd; destruct (Z.odd v); reflexivity).
  rewrite Hpar.
  destruct (Z.odd v).
  - change (Int64.neg (Int64.repr 1)) with Int64.mone.
    apply Int64.and_mone.
  - change (Int64.neg (Int64.repr 0)) with Int64.zero.
    apply Int64.and_zero.
Qed.

(** Logical shift right by 1 is division by 2 (unsigned-range argument). *)
Lemma Int64_shru_1 : forall v, 0 <= v < 2^64 ->
  Int64.shru (Int64.repr v) (Int64.repr 1) = Int64.repr (v / 2).
Proof.
  intros v Hv.
  rewrite Int64.shru_div_two_p.
  rewrite (Int64.unsigned_repr v) by rep_lia.
  rewrite (Int64.unsigned_repr 1) by rep_lia.
  change (two_p 1) with 2.
  reflexivity.
Qed.

(** Shift left by 63 keeps only the low bit, lifted to bit 63. *)
Lemma Int64_shl_63 : forall v, 0 <= v < 2^64 ->
  Int64.shl (Int64.repr v) (Int64.repr 63) = Int64.repr ((v mod 2) * 2^63).
Proof.
  intros v Hv.
  rewrite Int64.shl_mul_two_p.
  rewrite (Int64.unsigned_repr 63) by rep_lia.
  change (two_p 63) with (2^63).
  unfold Int64.mul.
  rewrite (Int64.unsigned_repr v) by rep_lia.
  rewrite (Int64.unsigned_repr (2^63)) by rep_lia.
  apply Int64.eqm_samerepr.
  exists (v / 2).
  change Int64.modulus with (2^64).
  rewrite (Z_div_mod_eq_full v 2) at 1.
  ring.
Qed.

(** The C shift-combination [(v0 >> 1) | (v1 << 63)] is, as a [Z],
    [v0/2 + (v1 mod 2) * 2^63] (the two bit ranges are disjoint, so OR
    is addition). *)
Lemma shift_or_repr : forall v0 v1, 0 <= v0 < 2^64 -> 0 <= v1 < 2^64 ->
  Int64.or (Int64.shru (Int64.repr v0) (Int64.repr 1))
           (Int64.shl (Int64.repr v1) (Int64.repr 63))
  = Int64.repr (v0 / 2 + (v1 mod 2) * 2^63).
Proof.
  intros v0 v1 Hv0 Hv1.
  rewrite Int64_shru_1 by lia.
  rewrite Int64_shl_63 by lia.
  assert (Hlo : 0 <= v0 / 2 < 2^63)
    by (split; [apply Z.div_pos; lia| apply Z.div_lt_upper_bound; lia]).
  assert (Hp : 0 <= v1 mod 2 < 2) by (apply Z.mod_pos_bound; lia).
  rewrite <- Int64.add_is_or.
  - apply add64_repr.
  - apply Int64.same_bits_eq.
    intros i Hi.
    rewrite Int64.bits_and by lia.
    rewrite Int64.bits_zero.
    rewrite !(Int64.testbit_repr) by lia.
    destruct (Z.lt_ge_cases i 63) as [Hi63|Hi63].
    + assert (Hhi0 : Z.testbit (v1 mod 2 * 2^63) i = false).
      { destruct (Z.eqb_spec (v1 mod 2) 0) as [Hz|Hz].
        - rewrite Hz.
          simpl.
          apply Z.testbit_0_l.
        - assert (Hv1eq : v1 mod 2 = 1) by lia.
          rewrite Hv1eq, Z.mul_1_l.
          apply Z.pow2_bits_false.
          lia. }
      rewrite Hhi0.
      apply andb_false_r.
    + assert (Hlo0 : Z.testbit (v0 / 2) i = false).
      { apply Z.testbit_false.
        lia.
        rewrite Z.div_small.
        reflexivity.
        split.
        lia.
        apply Z.lt_le_trans with (2^63).
        lia.
        apply Z.pow_le_mono_r; lia. }
      rewrite Hlo0.
      apply andb_false_l.
Qed.

(* ================================================================= *)
(** ** Pure-Z helpers -- [shift_recon] / [half_value] (file-local). *)

(** The four-limb shift-down [(a >> 1)] reconstructs to [floor(a/2)].
    Each limb contributes [a_i/2] plus the carried low bit of [a_{i+1}]
    lifted to bit 63. *)
Lemma shift_recon : forall a0 a1 a2 a3,
  0 <= a0 < 2^64 -> 0 <= a1 < 2^64 -> 0 <= a2 < 2^64 -> 0 <= a3 < 2^64 ->
  (a0 / 2 + (a1 mod 2) * 2^63)
  + (a1 / 2 + (a2 mod 2) * 2^63) * 2^64
  + (a2 / 2 + (a3 mod 2) * 2^63) * 2^128
  + (a3 / 2) * 2^192
  = (a0 + a1 * 2^64 + a2 * 2^128 + a3 * 2^192) / 2.
Proof.
  intros a0 a1 a2 a3 H0 H1 H2 H3.
  apply Z.div_unique_pos with (r := a0 mod 2).
  - assert (0 <= a0 mod 2 < 2) by (apply Z.mod_pos_bound; lia).
    lia.
  - pose proof (Z_div_mod_eq_full a0 2) as E0.
    pose proof (Z_div_mod_eq_full a1 2) as E1.
    pose proof (Z_div_mod_eq_full a2 2) as E2.
    pose proof (Z_div_mod_eq_full a3 2) as E3.
    nia.
Qed.

(** The crux modular identity: [floor(a/2) + (odd ? N//2+1 : 0)] equals
    [a * inv2 mod N], where [inv2 = (N+1)/2 = N_H + 1]. *)
Lemma half_value : forall a,
  0 <= a < secp256k1_N ->
  a / 2 + (if Z.odd a then secp256k1_N_H + 1 else 0)
  = (a * ((secp256k1_N + 1) / 2)) mod secp256k1_N.
Proof.
  intros a Ha.
  assert (HN2H : secp256k1_N = 2 * secp256k1_N_H + 1) by apply secp256k1_N_as_2H.
  assert (Hinv2 : (secp256k1_N + 1) / 2 = secp256k1_N_H + 1).
  { rewrite HN2H.
    replace (2 * secp256k1_N_H + 1 + 1) with ((secp256k1_N_H + 1) * 2) by ring.
    rewrite Z.div_mul by lia.
    reflexivity. }
  rewrite Hinv2.
  assert (HNH : 0 <= secp256k1_N_H < secp256k1_N) by (pose proof secp256k1_N_H_range; lia).
  assert (Hdm : a = 2 * (a / 2) + a mod 2) by (apply Z_div_mod_eq_full).
  assert (Hpar : a mod 2 = if Z.odd a then 1 else 0)
    by (rewrite Zmod_odd; destruct (Z.odd a); reflexivity).
  assert (Hq : 0 <= a / 2) by (apply Z.div_pos; lia).
  set (q := a / 2) in *.
  set (par := if Z.odd a then 1 else 0).
  set (res := q + (if Z.odd a then secp256k1_N_H + 1 else 0)).
  assert (Hident : a * (secp256k1_N_H + 1) = res + q * secp256k1_N).
  { subst res par.
    rewrite HN2H.
    rewrite Hpar in Hdm.
    destruct (Z.odd a); nia. }
  rewrite Hident.
  rewrite Z_mod_plus_full.
  symmetry.
  apply Z.mod_small.
  subst res.
  destruct (Z.odd a).
  - split.
    + lia.
    + assert (a <= 2 * secp256k1_N_H) by lia.
      rewrite Hpar in Hdm.
      lia.
  - split.
    + lia.
    + rewrite Hpar in Hdm.
      lia.
Qed.

(** The four-constant ripple-add carry chain (a per-limb constant addend
    [c_i] on every limb, including limb 3) is
    [theory.arithmetic.add4_carry_chain], shared with [scalar_add] and
    [scalar_negate].  [r_z] is the in-range result, [hi] the discarded
    final carry. *)

(* ================================================================= *)
(** ** secp256k1_scalar_half -- [a/2 mod N]. *)

(** Strategy: the C code computes [a/2 mod N] as [floor(a/2)] plus a
    masked constant [(odd ? N//2+1 : 0)], laid out as four limbs.  The
    proof walks the C in five phases:
      - Stage 0 reads [a->d[0]] and builds [mask = -(a&1)] (all-ones iff
        [a] is odd), and names the four input limbs [a0..a3] with their
        ranges / canonical forms.
      - Rounds 0..3 are the unrolled per-limb ripple-add: each round folds
        the shifted-down limb [(a_i>>1 | a_{i+1}<<63)] and the masked
        constant [N_H_i & mask] into the [u128] accumulator, stores the low
        word into [r->d[i]], and carries the high word into the next round.
      - Stage 4 (postcondition) collapses the [upd_Znth] store chain to a
        4-element list and reduces to four pure-Z limb equalities.
      - Stage 5 (pure-Z) reconstructs [floor(a/2)] ([shift_recon]) and the
        masked constants, identifies the model value via [half_value], and
        closes with the shared carry-chain lemma
        [theory.arithmetic.add4_carry_chain] + [limbs_eval4]. *)
Lemma body_secp256k1_scalar_half:
  semax_body Vprog Gprog
    f_secp256k1_scalar_half spec_secp256k1_scalar_half.
Proof.
  start_function.
  rename SH into Hsh_r.
  rename SH0 into Hsh_a.

  (* ===== Stage 0: read a->d[0], compute mask = -(a->d[0] & 1) ===== *)

  (* _t'12 = a->d[0] *)
  forward.

  (* mask = -(uint64_t)(a->d[0] & 1) *)
  forward.

  (* Name the four limbs of [a] and their ranges / canonical forms. *)
  set (a0 := limb (2^64) (scalar_val a) 0) in *.
  set (a1 := limb (2^64) (scalar_val a) 1) in *.
  set (a2 := limb (2^64) (scalar_val a) 2) in *.
  set (a3 := limb (2^64) (scalar_val a) 3) in *.
  assert (Ha0r : 0 <= a0 < 2^64) by (subst a0; apply Z.mod_pos_bound; lia).
  assert (Ha1r : 0 <= a1 < 2^64) by (subst a1; apply Z.mod_pos_bound; lia).
  assert (Ha2r : 0 <= a2 < 2^64) by (subst a2; apply Z.mod_pos_bound; lia).
  assert (Ha3r : 0 <= a3 < 2^64) by (subst a3; apply Z.mod_pos_bound; lia).
  assert (Ha0e : a0 = scalar_val a mod 2^64)
    by (subst a0; unfold limb; simpl Z.of_nat; rewrite Z.pow_0_r, Z.div_1_r; reflexivity).
  assert (Ha1e : a1 = (scalar_val a / 2^64) mod 2^64)
    by (subst a1; unfold limb; simpl Z.of_nat; rewrite Z.pow_1_r; reflexivity).
  assert (Ha2e : a2 = (scalar_val a / 2^128) mod 2^64)
    by (subst a2; unfold limb; simpl Z.of_nat; change ((2^64)^2) with (2^128); reflexivity).
  assert (Ha3e : a3 = (scalar_val a / 2^192) mod 2^64)
    by (subst a3; unfold limb; simpl Z.of_nat; change ((2^64)^3) with (2^192); reflexivity).

  (* Normalize the [mask] temp to [Int64.neg (Int64.repr (a mod 2))]. *)
  assert (Hmaskeq : Int64.and (Int64.repr (scalar_val a mod 2 ^ 64))
                      (Int64.repr (Int.unsigned (Int.repr 1)))
                    = Int64.repr (scalar_val a mod 2)).
  { rewrite Int.unsigned_repr by rep_lia.
    rewrite and_one_parity.
    f_equal.
    apply Z.mod_mod_divide.
    exists (2^63).
    reflexivity. }
  rewrite Hmaskeq.
  clear Hmaskeq.
  set (mask := Int64.neg (Int64.repr (scalar_val a mod 2))) in *.

  (* Ranges for the per-round shift inputs and masked constants. *)
  assert (Hs0 : 0 <= a0 / 2 + (a1 mod 2) * 2^63 < 2^64).
  { assert (0 <= a0 / 2 < 2^63) by (split; [apply Z.div_pos; lia| apply Z.div_lt_upper_bound; lia]).
    assert (0 <= a1 mod 2 < 2) by (apply Z.mod_pos_bound; lia).
    assert (0 <= (a1 mod 2) * 2^63 <= 2^63) by nia.
    lia. }
  assert (Hmc0 : 0 <= (if Z.odd (scalar_val a) then N_H_0 + 1 else 0) < 2^64)
    by (destruct (Z.odd (scalar_val a)); unfold N_H_0; lia).

  (* ===== Round 0: t = (a[0]>>1 | a[1]<<63) + ((N_H_0+1) & mask) ===== *)

  (* _t'10 = a->d[0] *)
  forward.

  (* _t'11 = a->d[1] *)
  forward.

  (* secp256k1_u128_from_u64(&t, (a->d[0] >> 1) | (a->d[1] << 63)) *)
  forward_call_u128_from_u64 v_t (mkUInt64 (a0 / 2 + (a1 mod 2) * 2^63) Hs0) Tsh t_init Ht_init.
  { entailer!.
    simpl.
    unfold uint64_to_val.
    simpl u64_val.
    f_equal.
    f_equal.
    change (Z.pow_pos 2 64) with (2^64).
    change (Z.pow_pos 2 63) with (2^63).
    fold (Z.div a (2^64)).
    fold (Z.div (limb (2^64) a 0) 2).
    rewrite shift_or_repr by (rewrite ?Ha0e in *; lia).
    rewrite <- Ha0e, <- Ha1e.
    reflexivity. }

  (* secp256k1_u128_accum_u64(&t, (N_H_0 + 1) & mask) *)
  forward_call_u128_accum_u64 v_t t_init
    (mkUInt64 (if Z.odd (scalar_val a) then N_H_0 + 1 else 0) Hmc0) Tsh acc0 Hacc0_raw.
  { entailer!.
    simpl.
    unfold uint64_to_val.
    simpl u64_val.
    f_equal.
    f_equal.
    unfold mask.
    replace (Int64.repr (-2312264954237214559)) with (Int64.repr (N_H_0 + 1))
      by (apply Int64.eqm_samerepr; exists 1; unfold N_H_0; change Int64.modulus with (2^64); lia).
    rewrite mask_and_const by (unfold N_H_0; lia).
    unfold N_H_0.
    reflexivity. }
  assert (Hacc0 : u128_val acc0 =
    (a0 / 2 + (a1 mod 2) * 2^63) + (if Z.odd (scalar_val a) then N_H_0 + 1 else 0))
    by (rewrite Hacc0_raw, Ht_init; simpl u64_val; reflexivity).
  clear Ht_init Hacc0_raw t_init.

  (* r->d[0] = secp256k1_u128_to_u64(&t) *)
  forward_call_u128_to_u64 v_t acc0 Tsh lo0 Hlo0.
  forward.

  (* secp256k1_u128_rshift(&t, 64) *)
  forward_call_u128_rshift v_t acc0 Tsh carry0 Hcarry0.
  assert (Hcarry0_val : u128_val carry0 =
    ((a0 / 2 + (a1 mod 2) * 2^63) + (if Z.odd (scalar_val a) then N_H_0 + 1 else 0)) / 2^64)
    by (rewrite Hcarry0, Hacc0; reflexivity).
  clear Hcarry0.

  (* ===== Round 1: t += (a[1]>>1 | a[2]<<63) + (N_H_1 & mask) ===== *)

  assert (Hs1 : 0 <= a1 / 2 + (a2 mod 2) * 2^63 < 2^64).
  { assert (0 <= a1 / 2 < 2^63) by (split; [apply Z.div_pos; lia| apply Z.div_lt_upper_bound; lia]).
    assert (0 <= a2 mod 2 < 2) by (apply Z.mod_pos_bound; lia).
    assert (0 <= (a2 mod 2) * 2^63 <= 2^63) by nia.
    lia. }
  assert (Hmc1 : 0 <= (if Z.odd (scalar_val a) then N_H_1 else 0) < 2^64)
    by (destruct (Z.odd (scalar_val a)); unfold N_H_1; lia).

  (* _t'8 = a->d[1] *)
  forward.

  (* _t'9 = a->d[2] *)
  forward.

  (* secp256k1_u128_accum_u64(&t, (a->d[1] >> 1) | (a->d[2] << 63)) *)
  forward_call_u128_accum_u64 v_t carry0 (mkUInt64 (a1 / 2 + (a2 mod 2) * 2^63) Hs1) Tsh t1a Ht1a.
  { entailer!.
    simpl.
    unfold uint64_to_val.
    simpl u64_val.
    f_equal.
    f_equal.
    change (Z.pow_pos 2 128) with (2^128).
    change (Z.pow_pos 2 64) with (2^64).
    fold (Z.div a (2^64)).
    fold (Z.div a (2^128)).
    rewrite (shift_or_repr ((a/2^64) mod 2^64) ((a/2^128) mod 2^64))
      by (split; [apply Z.mod_pos_bound; lia| apply Z.mod_pos_bound; lia]).
    rewrite <- Ha1e.
    f_equal. }
  { rewrite Hcarry0_val.
    simpl u64_val.
    change (Z.pow_pos 2 63) with (2^63).
    fold (Z.div a1 2).
    assert (Hcb : (a0 / 2 + a1 mod 2 * 2 ^ 63 + (if Z.odd (scalar_val a) then N_H_0 + 1 else 0)) / 2 ^ 64 < 2)
      by (apply Z.div_lt_upper_bound; lia).
    assert (Hcnn : 0 <= (a0 / 2 + a1 mod 2 * 2 ^ 63 + (if Z.odd (scalar_val a) then N_H_0 + 1 else 0)) / 2 ^ 64)
      by (apply Z.div_pos; lia).
    lia. }

  (* secp256k1_u128_accum_u64(&t, N_H_1 & mask) *)
  forward_call_u128_accum_u64 v_t t1a (mkUInt64 (if Z.odd (scalar_val a) then N_H_1 else 0) Hmc1) Tsh acc1 Hacc1_raw.
  { entailer!.
    simpl.
    unfold uint64_to_val.
    simpl u64_val.
    f_equal.
    f_equal.
    unfold mask.
    change 6725966010171805725 with N_H_1.
    rewrite mask_and_const by (unfold N_H_1; lia).
    reflexivity. }
  { rewrite Ht1a, Hcarry0_val.
    simpl u64_val.
    change (Z.pow_pos 2 63) with (2^63).
    fold (Z.div a1 2).
    assert (Hcb : (a0 / 2 + a1 mod 2 * 2 ^ 63 + (if Z.odd (scalar_val a) then N_H_0 + 1 else 0)) / 2 ^ 64 < 2)
      by (apply Z.div_lt_upper_bound; lia).
    assert (Hcnn : 0 <= (a0 / 2 + a1 mod 2 * 2 ^ 63 + (if Z.odd (scalar_val a) then N_H_0 + 1 else 0)) / 2 ^ 64)
      by (apply Z.div_pos; lia).
    lia. }
  assert (Hacc1 : u128_val acc1 =
    ((a0 / 2 + (a1 mod 2) * 2^63) + (if Z.odd (scalar_val a) then N_H_0 + 1 else 0)) / 2^64
    + (a1 / 2 + (a2 mod 2) * 2^63) + (if Z.odd (scalar_val a) then N_H_1 else 0)).
  { rewrite Hacc1_raw, Ht1a, Hcarry0_val.
    simpl u64_val.
    change (Z.pow_pos 2 63) with (2^63).
    fold (Z.div a1 2).
    lia. }
  clear Hacc1_raw Ht1a Hcarry0_val carry0 t1a.

  (* r->d[1] = secp256k1_u128_to_u64(&t) *)
  forward_call_u128_to_u64 v_t acc1 Tsh lo1 Hlo1.
  forward.

  (* secp256k1_u128_rshift(&t, 64) *)
  forward_call_u128_rshift v_t acc1 Tsh carry1 Hcarry1.
  assert (Hcarry1_val : u128_val carry1 = u128_val acc1 / 2^64) by exact Hcarry1.
  clear Hcarry1.

  (* ===== Round 2: t += (a[2]>>1 | a[3]<<63) + (N_H_2 & mask) ===== *)

  assert (Hs2 : 0 <= a2 / 2 + (a3 mod 2) * 2^63 < 2^64).
  { assert (0 <= a2 / 2 < 2^63) by (split; [apply Z.div_pos; lia| apply Z.div_lt_upper_bound; lia]).
    assert (0 <= a3 mod 2 < 2) by (apply Z.mod_pos_bound; lia).
    assert (0 <= (a3 mod 2) * 2^63 <= 2^63) by nia.
    lia. }
  assert (Hmc2 : 0 <= (if Z.odd (scalar_val a) then N_H_2 else 0) < 2^64)
    by (destruct (Z.odd (scalar_val a)); unfold N_H_2; lia).

  (* _t'6 = a->d[2] *)
  forward.

  (* _t'7 = a->d[3] *)
  forward.

  (* secp256k1_u128_accum_u64(&t, (a->d[2] >> 1) | (a->d[3] << 63)) *)
  forward_call_u128_accum_u64 v_t carry1 (mkUInt64 (a2 / 2 + (a3 mod 2) * 2^63) Hs2) Tsh t2a Ht2a.
  { entailer!.
    simpl.
    unfold uint64_to_val.
    simpl u64_val.
    f_equal.
    f_equal.
    change (Z.pow_pos 2 192) with (2^192).
    change (Z.pow_pos 2 128) with (2^128).
    change (Z.pow_pos 2 64) with (2^64).
    fold (Z.div a (2^128)).
    fold (Z.div a (2^192)).
    rewrite (shift_or_repr ((a/2^128) mod 2^64) ((a/2^192) mod 2^64))
      by (split; [apply Z.mod_pos_bound; lia| apply Z.mod_pos_bound; lia]).
    rewrite <- Ha2e, <- Ha3e.
    reflexivity. }

  (* secp256k1_u128_accum_u64(&t, N_H_2 & mask) *)
  forward_call_u128_accum_u64 v_t t2a (mkUInt64 (if Z.odd (scalar_val a) then N_H_2 else 0) Hmc2) Tsh acc2 Hacc2_raw.
  { entailer!.
    simpl.
    unfold uint64_to_val.
    simpl u64_val.
    f_equal.
    f_equal.
    unfold mask.
    assert (Hm2 : Int64.repr (-1) = Int64.repr N_H_2).
    { apply Int64.eqm_samerepr.
      unfold Int64.eqm, Zbits.eqmod.
      exists (-1).
      unfold N_H_2.
      change Int64.modulus with (2^64).
      lia. }
    rewrite Hm2.
    rewrite mask_and_const by (unfold N_H_2; lia).
    reflexivity. }
  assert (Hacc2 : u128_val acc2 =
    ((a0 / 2 + (a1 mod 2) * 2^63 + (if Z.odd (scalar_val a) then N_H_0 + 1 else 0)) / 2^64
     + (a1 / 2 + (a2 mod 2) * 2^63) + (if Z.odd (scalar_val a) then N_H_1 else 0)) / 2^64
    + (a2 / 2 + (a3 mod 2) * 2^63) + (if Z.odd (scalar_val a) then N_H_2 else 0)).
  { rewrite Hacc2_raw, Ht2a, Hcarry1_val, Hacc1.
    simpl u64_val.
    change (Z.pow_pos 2 63) with (2^63).
    fold (Z.div a2 2).
    lia. }
  clear Hacc2_raw Ht2a Hcarry1_val carry1 t2a.

  (* r->d[2] = secp256k1_u128_to_u64(&t) *)
  forward_call_u128_to_u64 v_t acc2 Tsh lo2 Hlo2.
  forward.

  (* secp256k1_u128_rshift(&t, 64) *)
  forward_call_u128_rshift v_t acc2 Tsh carry2 Hcarry2.
  assert (Hcarry2_val : u128_val carry2 = u128_val acc2 / 2^64) by exact Hcarry2.
  clear Hcarry2.

  (* ===== Round 3: r->d[3] = to_u64(t) + (a[3]>>1) + (N_H_3 & mask) ===== *)

  assert (Hmc3 : 0 <= (if Z.odd (scalar_val a) then N_H_3 else 0) < 2^64)
    by (destruct (Z.odd (scalar_val a)); unfold N_H_3; lia).
  assert (Hs3 : 0 <= a3 / 2 < 2^64)
    by (split; [apply Z.div_pos; lia| apply Z.div_lt_upper_bound; lia]).

  (* _t'4 = secp256k1_u128_to_u64(&t) *)
  forward_call_u128_to_u64 v_t carry2 Tsh lo3 Hlo3.

  (* _t'5 = a->d[3] *)
  forward.

  (* r->d[3] = _t'4 + (a->d[3] >> 1) + (N_H_3 & mask) *)
  forward.

  (* ===== Stage 4: Postcondition ===== *)

  (* property POST: [(2 * (a/2 mod N)) mod N = a]; entailer! discharges it from
     this fact, then the SEP limb-matching proceeds as before. *)
  assert (Hprop : Z.modulo (Z.mul 2 (scalar_val (scalar_half a)))
                    secp256k1_N = scalar_val a) by apply scalar_half_prop.
  Exists (scalar_half a).
  entailer!.

  (* Goal: masked upd_Znth chain |-- scalar_to_val (scalar_half a). *)
  apply derives_refl'.
  f_equal.

  (* Collapse the [upd_Znth] chain to a plain 4-element list. *)
  unfold scalar_to_val.
  transitivity [Vlong (Int64.repr (u64_val (u128_lo acc0)));
                Vlong (Int64.repr (u64_val (u128_lo acc1)));
                Vlong (Int64.repr (u64_val (u128_lo acc2)));
                Vlong (Int64.add
                         (Int64.add (Int64.repr (u64_val (u128_lo carry2)))
                            (Int64.shru (Int64.repr ((a / 2 ^ 192) mod 2 ^ 64)) (Int64.repr 1)))
                         (Int64.and (Int64.repr 9223372036854775807) mask))].
  { unfold uint64_to_val.
    change (Z.pow_pos 2 192) with (2^192).
    fold (Z.div a (2^192)).
    reflexivity. }

  (* Normalize round 3's plain-add limb: shift bridge + mask + add. *)
  rewrite Int64_shru_1 by (apply Z.mod_pos_bound; lia).
  unfold mask.
  replace (Int64.repr 9223372036854775807) with (Int64.repr N_H_3) by (unfold N_H_3; reflexivity).
  rewrite mask_and_const by (unfold N_H_3; lia).
  rewrite Int64.add_assoc.
  rewrite !add64_repr.
  rewrite !u128_lo_val.
  rewrite Hcarry2_val.

  (* Name the carry-chain quantities. *)
  set (a0 := limb (2^64) (scalar_val a) 0) in *.
  set (a1 := limb (2^64) (scalar_val a) 1) in *.
  set (a2 := limb (2^64) (scalar_val a) 2) in *.
  set (a3 := limb (2^64) (scalar_val a) 3) in *.
  set (s0 := a0 / 2 + (a1 mod 2) * 2^63) in *.
  set (s1 := a1 / 2 + (a2 mod 2) * 2^63) in *.
  set (s2 := a2 / 2 + (a3 mod 2) * 2^63) in *.
  set (mc0 := if Z.odd (scalar_val a) then N_H_0 + 1 else 0) in *.
  set (mc1 := if Z.odd (scalar_val a) then N_H_1 else 0) in *.
  set (mc2 := if Z.odd (scalar_val a) then N_H_2 else 0) in *.
  set (mc3 := if Z.odd (scalar_val a) then N_H_3 else 0) in *.
  set (t0 := s0 + mc0) in *.
  set (t1 := t0 / 2^64 + s1 + mc1) in *.
  set (t2 := t1 / 2^64 + s2 + mc2) in *.
  set (t3 := t2 / 2^64 + a3 / 2 + mc3) in *.

  (* The stored r->d[3] equals [Int64.repr t3] (the inner [mod] is absorbed). *)
  assert (Hd3eq : Int64.repr ((u128_val acc2 / 2 ^ 64) mod 2 ^ 64
                                + ((a / 2 ^ 192) mod 2 ^ 64 / 2 + mc3))
                  = Int64.repr t3).
  { rewrite Hacc2.
    replace ((a / 2 ^ 192) mod 2 ^ 64 / 2) with (a3 / 2) by (rewrite <- Ha3e; reflexivity).
    apply Int64.eqm_samerepr.
    unfold Int64.eqm, Zbits.eqmod.
    exists (- (t2 / 2^64 / 2^64)).
    change Int64.modulus with (2^64).
    subst t3.
    set (y := t2 / 2^64) in *.
    pose proof (Z_div_mod_eq_full y (2^64)) as E.
    lia. }
  rewrite Hd3eq.
  rewrite Hacc0, Hacc1, Hacc2.

  (* Reduce to four pure-Z limb equalities. *)
  cut (t0 mod 2^64 = scalar_half a mod 2^64 /\
       t1 mod 2^64 = (scalar_half a / 2^64) mod 2^64 /\
       t2 mod 2^64 = (scalar_half a / 2^128) mod 2^64 /\
       t3 mod 2^64 = (scalar_half a / 2^192) mod 2^64).
  { intros [E0 [E1 [E2 E3]]].
    assert (E3' : Int64.repr t3 = Int64.repr ((scalar_half a / 2^192) mod 2^64)).
    { apply Int64.eqm_samerepr.
      unfold Int64.eqm, Zbits.eqmod.
      exists (t3 / 2^64).
      change Int64.modulus with (2^64).
      rewrite <- E3.
      rewrite (Z_div_mod_eq_full t3 (2^64)) at 1.
      lia. }
    rewrite E0, E1, E2, E3'.
    reflexivity. }

  (* ===== Stage 5: pure-Z arithmetic ===== *)

  (* [a] decomposes into its four limbs. *)
  assert (Hadecomp : a0 + a1 * 2^64 + a2 * (2^64)^2 + a3 * (2^64)^3 = scalar_val a).
  { pose proof (eval4_limbs (2^64) (scalar_val a) ltac:(lia)) as E.
    unfold eval4 in E.
    subst a0 a1 a2 a3.
    apply E.
    change ((2^64)^4) with (2^256).
    pose proof (scalar_range a).
    unfold secp256k1_N in *.
    lia. }

  (* The shift inputs reconstruct to [floor(a/2)]. *)
  assert (Hval : s0 + s1 * 2^64 + s2 * (2^64)^2 + (a3 / 2) * (2^64)^3 = scalar_val a / 2).
  { subst s0 s1 s2.
    pose proof (shift_recon a0 a1 a2 a3 Ha0r Ha1r Ha2r Ha3r) as Hsr.
    change ((2^64)^2) with (2^128) in *.
    change ((2^64)^3) with (2^192) in *.
    rewrite Hsr.
    f_equal.
    rewrite <- Hadecomp.
    change ((2^64)^2) with (2^128).
    change ((2^64)^3) with (2^192).
    ring. }

  (* The masked constants reconstruct to [(odd ? N//2+1 : 0)]. *)
  assert (HC : mc0 + mc1 * 2^64 + mc2 * (2^64)^2 + mc3 * (2^64)^3
               = if Z.odd (scalar_val a) then secp256k1_N_H + 1 else 0).
  { subst mc0 mc1 mc2 mc3.
    destruct (Z.odd (scalar_val a)).
    - (* branch: odd -- limbs of N_H reassemble to N//2 + 1 *)
      unfold secp256k1_N_H.
      change ((2^64)^2) with (2^128).
      change ((2^64)^3) with (2^192).
      ring.
    - (* branch: even -- all masked constants are 0 *)
      ring. }

  (* The model value equals [floor(a/2) + (odd ? N//2+1 : 0)]. *)
  assert (Hhalf : scalar_val (scalar_half a)
                  = scalar_val a / 2 + (if Z.odd (scalar_val a) then secp256k1_N_H + 1 else 0)).
  { unfold scalar_half.
    cbn [scalar_val scalar_reduce].
    rewrite <- half_value by apply scalar_range.
    reflexivity. }
  assert (Hhalf_range : 0 <= scalar_val (scalar_half a) < 2^256).
  { pose proof (scalar_range (scalar_half a)).
    unfold secp256k1_N in *.
    lia. }

  set (B := 2^64) in *.

  (* Apply the four-constant carry-chain identity. *)
  pose proof (add4_carry_chain B s0 s1 s2 (a3 / 2) mc0 mc1 mc2 mc3
    ltac:(subst B; lia)
    ltac:(subst B; lia) ltac:(subst B; lia) ltac:(subst B; lia) ltac:(subst B; lia)
    ltac:(subst mc0; destruct (Z.odd (scalar_val a)); unfold N_H_0; lia)
    ltac:(subst mc1; destruct (Z.odd (scalar_val a)); unfold N_H_1; lia)
    ltac:(subst mc2; destruct (Z.odd (scalar_val a)); unfold N_H_2; lia)
    ltac:(subst mc3; destruct (Z.odd (scalar_val a)); unfold N_H_3; lia)) as Hchain.
  cbv zeta in Hchain.
  unfold eval4 in Hchain.
  replace (B * B * B * B) with (B ^ 4) in Hchain by ring.
  rewrite Hval, HC in Hchain.
  rewrite <- Hhalf in Hchain.
  fold t0 in Hchain.
  fold t1 in Hchain.
  fold t2 in Hchain.
  fold t3 in Hchain.
  assert (HB4 : B^4 = 2^256) by (subst B; reflexivity).
  destruct Hchain as [Heq [Hrz_bnd Hhi_bnd]].
  { rewrite HB4. lia. }

  (* The discarded carry [hi] is 0, so [r_z = scalar_half a]. *)
  assert (Hhi0 : t3 / B = 0).
  { assert (HB4pos : 0 < B^4) by (rewrite HB4; lia).
    destruct (Z.eq_dec (t3 / B) 0) as [E|E].
    - (* branch: hi = 0 -- nothing to discard *)
      exact E.
    - (* branch: hi = 1 -- contradicts the in-range bound on r_z *)
      assert (Hhi1 : t3 / B = 1) by lia.
      rewrite Hhi1 in Heq.
      rewrite HB4 in Heq, Hrz_bnd.
      lia. }
  rewrite Hhi0 in Heq.
  assert (Hrz : t0 mod B + t1 mod B * B + t2 mod B * B^2 + t3 mod B * B^3 = scalar_half a) by lia.

  (* Extract the per-limb values via [limbs_eval4]. *)
  pose proof (limbs_eval4 B (t0 mod B) (t1 mod B) (t2 mod B) (t3 mod B)
    ltac:(subst B; lia)
    ltac:(apply Z.mod_pos_bound; subst B; lia)
    ltac:(apply Z.mod_pos_bound; subst B; lia)
    ltac:(apply Z.mod_pos_bound; subst B; lia)
    ltac:(apply Z.mod_pos_bound; subst B; lia)) as [Hl0 [Hl1 [Hl2 Hl3]]].
  unfold eval4 in Hl0, Hl1, Hl2, Hl3.
  rewrite Hrz in Hl0, Hl1, Hl2, Hl3.
  unfold limb in Hl0, Hl1, Hl2, Hl3.
  simpl Z.of_nat in Hl0, Hl1, Hl2, Hl3.
  rewrite Z.pow_0_r, Z.div_1_r, Z.pow_1_r in *.
  replace (B^2) with (2^128) in Hl2 by (subst B; reflexivity).
  replace (B^3) with (2^192) in Hl3 by (subst B; reflexivity).
  repeat split.
  - (* limb 0 *)
    exact (eq_sym Hl0).
  - (* limb 1 *)
    exact (eq_sym Hl1).
  - (* limb 2 *)
    exact (eq_sym Hl2).
  - (* limb 3 *)
    exact (eq_sym Hl3).
Qed.
