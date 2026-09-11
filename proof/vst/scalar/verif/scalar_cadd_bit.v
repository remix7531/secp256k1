(** * vst.scalar.verif.scalar_cadd_bit: Proof of body_secp256k1_scalar_cadd_bit. *)
(** Copyright (C) 2026 remix7531
    SPDX-License-Identifier: MIT *)

Require Import secp256k1.vst.base.
Require Import secp256k1.vst.helper.notations.
Require Import secp256k1.vst.gprog.
Require Import secp256k1.vst.tactics.core.
Require Import secp256k1.vst.tactics.int128.
Require Import secp256k1.vst.tactics.scalar.

(* ================================================================= *)
(** ** secp256k1_scalar_cadd_bit -- [*r += flag * 2^bit]. *)

(** [*r += flag * 2^bit] in constant time.  The extraction unit [#define]s
    [volatile] away (the [volatile int vflag] hardening hint becomes a plain
    temp -- no [EF_vstore] / [EF_vload] builtins), so the conditional add
    goes through.

    The C masks the bit index by [bit += ((uint32_t)vflag - 1) & 0x100]:
    when [flag = 1] this is [+0] (the index stays in [[0, 256)]); when
    [flag = 0] it is [+256], pushing [bit] into [[256, 512)] so [bit >> 6]
    lands in [{4..7}] and never matches a limb index [{0..3}], adding zero.
    A 128-bit accumulator [t] ripples the per-limb addend
    [(uint64)(bit>>6 == i) << (bit & 63)] through the four scalar limbs;
    its weighted sum is exactly [flag * 2^bit] (lemma [cadd_addend_sum]). *)

(* ----------------------------------------------------------------- *)
(** *** Pure-arithmetic helpers (local to this file). *)

(** The 4-limb ripple-add carry-chain identity over an abstract base [B]:
    the four stored low-words reconstruct the sum [eval4 d + eval4 a].
    The top carry vanishes because the sum stays below [B^4]. *)
Lemma cadd_carry4 : forall B d0 d1 d2 d3 a0 a1 a2 a3,
  B > 1 ->
  0 <= d0 < B -> 0 <= d1 < B -> 0 <= d2 < B -> 0 <= d3 < B ->
  0 <= a0 -> 0 <= a1 -> 0 <= a2 -> 0 <= a3 ->
  eval4 B d0 d1 d2 d3 + eval4 B a0 a1 a2 a3 < B ^ 4 ->
  eval4 B ((d0 + a0) mod B)
          (((d0 + a0) / B + d1 + a1) mod B)
          ((((d0 + a0) / B + d1 + a1) / B + d2 + a2) mod B)
          (((((d0 + a0) / B + d1 + a1) / B + d2 + a2) / B + d3 + a3) mod B)
  = eval4 B d0 d1 d2 d3 + eval4 B a0 a1 a2 a3.
Proof.
  intros B d0 d1 d2 d3 a0 a1 a2 a3 HB Hd0 Hd1 Hd2 Hd3 Ha0 Ha1 Ha2 Ha3 Hlt.
  unfold eval4 in *.
  set (x0 := d0 + a0).
  set (x1 := x0 / B + d1 + a1).
  set (x2 := x1 / B + d2 + a2).
  set (x3 := x2 / B + d3 + a3).
  assert (Hx0n : 0 <= x0) by (subst x0; lia).
  assert (HdivB0 : 0 <= x0 / B) by (apply Z.div_pos; lia).
  assert (Hx1n : 0 <= x1) by (subst x1; lia).
  assert (HdivB1 : 0 <= x1 / B) by (apply Z.div_pos; lia).
  assert (Hx2n : 0 <= x2) by (subst x2; lia).
  assert (HdivB2 : 0 <= x2 / B) by (apply Z.div_pos; lia).
  assert (Hx3n : 0 <= x3) by (subst x3; lia).
  pose proof (Z.mod_pos_bound x0 B ltac:(lia)) as M0.
  pose proof (Z.mod_pos_bound x1 B ltac:(lia)) as M1.
  pose proof (Z.mod_pos_bound x2 B ltac:(lia)) as M2.

  (* Telescoped sum: the lower three stored words plus the top word [x3]. *)
  assert (Htel : d0 + d1 * B + d2 * B ^ 2 + d3 * B ^ 3
                 + (a0 + a1 * B + a2 * B ^ 2 + a3 * B ^ 3)
               = x0 mod B + (x1 mod B) * B + (x2 mod B) * B ^ 2 + x3 * B ^ 3).
  { pose proof (Z_div_mod_eq_full x0 B) as E0.
    pose proof (Z_div_mod_eq_full x1 B) as E1.
    pose proof (Z_div_mod_eq_full x2 B) as E2.
    subst x3 x2 x1 x0.
    nia. }

  assert (HBpow : 0 < B ^ 3) by (apply Z.pow_pos_nonneg; lia).
  (* The top word fits in one limb, so the top carry is zero. *)
  assert (Hx3lt : x3 < B).
  { assert (Hle : x3 * B ^ 3 <= d0 + d1 * B + d2 * B ^ 2 + d3 * B ^ 3
                              + (a0 + a1 * B + a2 * B ^ 2 + a3 * B ^ 3)).
    { rewrite Htel.
      assert (0 <= x0 mod B + x1 mod B * B + x2 mod B * B ^ 2) by nia.
      lia. }
    assert (H2 : x3 * B ^ 3 < B * B ^ 3) by (replace (B * B ^ 3) with (B ^ 4) by ring; lia).
    exact (proj2 (Z.mul_lt_mono_pos_r (B ^ 3) x3 B HBpow) H2). }

  assert (Hx3q : x3 / B = 0) by (apply Z.div_small; lia).
  pose proof (Z_div_mod_eq_full x3 B) as E3.
  rewrite Hx3q in E3.
  nia.
Qed.

(** The CompCert evaluation of the per-limb C addend expression
    [(tulong)(bit>>6 == idx) << (bit & 63)] reduces to the [Z] value
    [(if bit/64 = idx then 1 else 0) * 2^(bit mod 64)].  Bridges the
    [forward_call] argument match. *)
Lemma cadd_arg_eval : forall b idx : Z,
  0 <= b < 512 ->
  0 <= idx < 8 ->
  Int64.shl
    (Int64.repr
       (Int.signed
          (Int.repr
             (Z.b2z (Int.eq (Int.shru (Int.repr b) (Int.repr 6)) (Int.repr idx))))))
    (Int64.repr (Int.unsigned (Int.repr (Z.land b 63))))
  = Int64.repr ((if b / 64 =? idx then 1 else 0) * 2 ^ (b mod 64)).
Proof.
  intros b idx Hb Hidx.
  assert (Hmu : 0 <= b <= Int.max_unsigned)
    by (change Int.max_unsigned with 4294967295; lia).

  (* [bit >> 6 = bit / 64]. *)
  assert (Hshru : Int.shru (Int.repr b) (Int.repr 6) = Int.repr (b / 64)).
  { rewrite Int.shru_div_two_p.
    rewrite (Int.unsigned_repr b Hmu).
    rewrite (Int.unsigned_repr 6) by (change Int.max_unsigned with 4294967295; lia).
    change (two_p 6) with 64.
    reflexivity. }
  rewrite Hshru.

  (* The equality test [bit/64 == idx] decides [bit/64 =? idx]. *)
  assert (Hq : 0 <= b / 64 <= Int.max_unsigned).
  { assert (0 <= b / 64) by (apply Z.div_pos; lia).
    assert (b / 64 < 8) by (apply Z.div_lt_upper_bound; lia).
    change Int.max_unsigned with 4294967295; lia. }
  assert (Hidxu : 0 <= idx <= Int.max_unsigned)
    by (change Int.max_unsigned with 4294967295; lia).
  rewrite (eq_repr_zeq (b / 64) idx Hq Hidxu).

  (* [bit & 63 = bit mod 64], in range, so the left shift is a multiply. *)
  assert (Hland : Z.land b 63 = b mod 64)
    by (change 63 with (Z.ones 6); rewrite Z.land_ones by lia; reflexivity).
  assert (Hm64 : 0 <= b mod 64 < 64) by (apply Z.mod_pos_bound; lia).
  rewrite Hland.
  rewrite (Int.unsigned_repr (b mod 64)) by (change Int.max_unsigned with 4294967295; lia).
  rewrite Int64.shl_mul_two_p.
  rewrite (Int64.unsigned_repr (b mod 64))
    by (change Int64.max_unsigned with 18446744073709551615; lia).
  rewrite mul64_repr.
  rewrite two_p_equiv.
  destruct (zeq (b / 64) idx) as [Heq | Hne]; simpl Z.b2z.
  - (* match: indicator is 1 *)
    rewrite (proj2 (Z.eqb_eq (b / 64) idx) Heq).
    change (Int.signed (Int.repr 1)) with 1.
    reflexivity.
  - (* mismatch: indicator is 0 *)
    rewrite (proj2 (Z.eqb_neq (b / 64) idx) Hne).
    change (Int.signed (Int.repr 0)) with 0.
    reflexivity.
Qed.

(** The four per-limb addends, weighted little-endian, sum to [flag * 2^bit].
    When [flag = 1] the unique matching limb [bit/64] contributes [2^bit];
    when [flag = 0] the masked index [bit + 256] matches no limb. *)
Lemma cadd_addend_sum : forall bit flag,
  0 <= bit < 256 ->
  flag = 0 \/ flag = 1 ->
  eval4 (2 ^ 64)
    ((if (bit + (1 - flag) * 256) / 64 =? 0 then 1 else 0) * 2 ^ ((bit + (1 - flag) * 256) mod 64))
    ((if (bit + (1 - flag) * 256) / 64 =? 1 then 1 else 0) * 2 ^ ((bit + (1 - flag) * 256) mod 64))
    ((if (bit + (1 - flag) * 256) / 64 =? 2 then 1 else 0) * 2 ^ ((bit + (1 - flag) * 256) mod 64))
    ((if (bit + (1 - flag) * 256) / 64 =? 3 then 1 else 0) * 2 ^ ((bit + (1 - flag) * 256) mod 64))
  = flag * 2 ^ bit.
Proof.
  intros bit flag Hbit Hflag.
  unfold eval4.
  destruct Hflag as [Hf | Hf]; subst flag.
  - (* flag = 0: index is [bit + 256], quotient >= 4, no limb matches *)
    replace (bit + (1 - 0) * 256) with (bit + 256) by ring.
    assert (Hge : (bit + 256) / 64 >= 4)
      by (apply Z.le_ge; apply Z.div_le_lower_bound; lia).
    rewrite (proj2 (Z.eqb_neq ((bit + 256) / 64) 0)) by lia.
    rewrite (proj2 (Z.eqb_neq ((bit + 256) / 64) 1)) by lia.
    rewrite (proj2 (Z.eqb_neq ((bit + 256) / 64) 2)) by lia.
    rewrite (proj2 (Z.eqb_neq ((bit + 256) / 64) 3)) by lia.
    ring.
  - (* flag = 1: exactly one limb [bit/64] matches, contributing [2^bit] *)
    replace (bit + (1 - 1) * 256) with bit by ring.
    assert (Hq : 0 <= bit / 64 < 4)
      by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
    assert (Hm : 0 <= bit mod 64 < 64) by (apply Z.mod_pos_bound; lia).

    assert (Hbit2 : 2 ^ bit = 2 ^ (bit mod 64) * 2 ^ (64 * (bit / 64))).
    { rewrite <- Z.pow_add_r by lia.
      f_equal.
      rewrite (Z_div_mod_eq_full bit 64) at 1.
      lia. }

    rewrite Hbit2.
    assert (HC : bit / 64 = 0 \/ bit / 64 = 1 \/ bit / 64 = 2 \/ bit / 64 = 3) by lia.
    destruct HC as [E | [E | [E | E]]];
      rewrite E;
      cbn [Z.eqb Pos.eqb];
      [ change (2 ^ (64 * 0)) with 1
      | change (2 ^ (64 * 1)) with (2 ^ 64)
      | change (2 ^ (64 * 2)) with ((2 ^ 64) ^ 2)
      | change (2 ^ (64 * 3)) with ((2 ^ 64) ^ 3) ];
      ring.
Qed.

(* ----------------------------------------------------------------- *)
(** *** The body proof. *)

Lemma body_secp256k1_scalar_cadd_bit:
  semax_body Vprog Gprog
    f_secp256k1_scalar_cadd_bit spec_secp256k1_scalar_cadd_bit.
Proof.
  start_function.

  rename H into Hbit.
  rename H0 into Hflag.
  rename H1 into Hno_overflow.

  (* ===== Setup: read vflag, mask the bit index, pose limb/addend ranges ===== *)

  (* vflag = flag (a plain temp -- volatile neutralized in the extraction) *)
  forward.
  (* bit += ((uint32_t)vflag - 1) & 0x100: +0 if flag=1, +256 if flag=0 *)
  forward.
  assert (Hmask : Int.and (Int.sub (Int.repr flag) (Int.repr 1)) (Int.repr 256)
                  = Int.repr ((1 - flag) * 256))
    by (destruct Hflag as [Hf | Hf]; subst flag; apply Int.same_if_eq; reflexivity).
  rewrite Hmask.
  rewrite add_repr.

  (* Abbreviations for the masked index [b] and the per-limb addend value. *)
  set (b := bit + (1 - flag) * 256) in *.
  assert (Hb_range : 0 <= b < 512) by (subst b; destruct Hflag; subst flag; lia).
  (* The shift amount [b mod 64] is in range, so each addend < 2^64. *)
  assert (Hbm : 0 <= b mod 64 < 64) by (apply Z.mod_pos_bound; lia).
  assert (Hpow_lt : 2 ^ (b mod 64) < 2 ^ 64) by (apply Z.pow_lt_mono_r; lia).
  assert (Hpow_nn : 0 <= 2 ^ (b mod 64)) by (apply Z.pow_nonneg; lia).
  assert (Haddr : forall idx, 0 <= (if b / 64 =? idx then 1 else 0) * 2 ^ (b mod 64) < 2 ^ 64).
  { intro idx.
    destruct (b / 64 =? idx) eqn:E; lia. }
  (* The scalar limbs [d_i] of [r0]. *)
  assert (Hd : forall i, 0 <= (r0 / 2 ^ (64 * i)) mod 2 ^ 64 < 2 ^ 64)
    by (intro i; apply Z.mod_pos_bound; lia).
  assert (Hd0 : 0 <= r0 mod 2 ^ 64 < 2 ^ 64) by (apply Z.mod_pos_bound; lia).
  assert (Hd1 : 0 <= (r0 / 2 ^ 64) mod 2 ^ 64 < 2 ^ 64) by (apply Z.mod_pos_bound; lia).
  assert (Hd2 : 0 <= (r0 / 2 ^ 128) mod 2 ^ 64 < 2 ^ 64) by (apply Z.mod_pos_bound; lia).
  assert (Hd3 : 0 <= (r0 / 2 ^ 192) mod 2 ^ 64 < 2 ^ 64) by (apply Z.mod_pos_bound; lia).

  (* ===== Limb 0: t = from_u64(r->d[0]); t += addend; r->d[0] = t; t >>= 64 ===== *)

  (* t'8 = r->d[0] *)
  forward.

  (* secp256k1_u128_from_u64(&t, r->d[0]) *)
  forward_call (v_t, mkUInt64 (r0 mod 2 ^ 64) Hd0, Tsh).
  Intros t0.
  rename H into Ht0.

  (* secp256k1_u128_accum_u64(&t, (uint64)(bit>>6 == 0) << (bit & 63)) *)
  forward_call (v_t, t0, mkUInt64 ((if b / 64 =? 0 then 1 else 0) * 2 ^ (b mod 64)) (Haddr 0), Tsh).
  { (* shift amount [bit & 63] < 64 *)
    change (Z.land b 63) with (Z.land b 63).
    assert (Hl : Z.land b 63 = b mod 64)
      by (change 63 with (Z.ones 6); rewrite Z.land_ones by lia; reflexivity).
    rewrite Hl.
    change (Int.unsigned Int64.iwordsize') with 64.
    rewrite Int.unsigned_repr by (pose proof (Z.mod_pos_bound b 64 ltac:(lia)); rep_lia).
    pose proof (Z.mod_pos_bound b 64 ltac:(lia)); lia. }
  { (* PARAMS: the C addend expression evaluates to the witness value *)
    entailer!.
    rewrite cadd_arg_eval by (subst b; lia).
    reflexivity. }
  { (* PROP: [t < 2^128] *)
    rewrite Ht0.
    cbn [u64_val].
    change (Z.pow_pos 2 64) with (2 ^ 64).
    pose proof (Haddr 0).
    assert (Hpp : (2 ^ 64 + 2 ^ 64 <= 2 ^ 128)%Z) by (vm_compute; congruence).
    lia. }
  Intros t0a.
  rename H into Ht0a.

  (* t'1 = secp256k1_u128_to_u64(&t); r->d[0] = t'1 *)
  forward_call (v_t, t0a, Tsh).
  Intros r1.
  rename H into Hr1.
  forward.

  (* secp256k1_u128_rshift(&t, 64) *)
  forward_call (v_t, t0a, 64, Tsh).
  Intros t0b.
  rename H into Ht0b.

  (* ===== Limb 1: t += r->d[1]; t += addend; r->d[1] = t; t >>= 64 ===== *)

  (* t'7 = r->d[1] *)
  forward.

  (* secp256k1_u128_accum_u64(&t, r->d[1]) *)
  forward_call (v_t, t0b, mkUInt64 ((r0 / 2 ^ 64) mod 2 ^ 64) Hd1, Tsh).
  Intros t1.
  rename H into Ht1.

  (* secp256k1_u128_accum_u64(&t, (uint64)(bit>>6 == 1) << (bit & 63)) *)
  forward_call (v_t, t1, mkUInt64 ((if b / 64 =? 1 then 1 else 0) * 2 ^ (b mod 64)) (Haddr 1), Tsh).
  { assert (Hl : Z.land b 63 = b mod 64)
      by (change 63 with (Z.ones 6); rewrite Z.land_ones by lia; reflexivity).
    rewrite Hl.
    change (Int.unsigned Int64.iwordsize') with 64.
    rewrite Int.unsigned_repr by (pose proof (Z.mod_pos_bound b 64 ltac:(lia)); rep_lia).
    pose proof (Z.mod_pos_bound b 64 ltac:(lia)); lia. }
  { entailer!.
    rewrite cadd_arg_eval by (subst b; lia).
    reflexivity. }
  { rewrite Ht1, Ht0b.
    cbn [u64_val].
    pose proof (u128_range t0a) as Hr0a.
    assert (Ht0bn : 0 <= u128_val t0a / 2 ^ 64 < 2 ^ 64)
      by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
    pose proof (Haddr 1).
    assert (Hpp : (2 ^ 64 + 2 ^ 64 + 2 ^ 64 <= 2 ^ 128)%Z) by (vm_compute; congruence).
    lia. }
  Intros t1a.
  rename H into Ht1a.

  (* t'2 = secp256k1_u128_to_u64(&t); r->d[1] = t'2 *)
  forward_call (v_t, t1a, Tsh).
  Intros r2.
  rename H into Hr2.
  forward.

  (* secp256k1_u128_rshift(&t, 64) *)
  forward_call (v_t, t1a, 64, Tsh).
  Intros t1b.
  rename H into Ht1b.

  (* ===== Limb 2: t += r->d[2]; t += addend; r->d[2] = t; t >>= 64 ===== *)

  (* t'6 = r->d[2] *)
  forward.

  (* secp256k1_u128_accum_u64(&t, r->d[2]) *)
  forward_call (v_t, t1b, mkUInt64 ((r0 / 2 ^ 128) mod 2 ^ 64) Hd2, Tsh).
  Intros t2.
  rename H into Ht2.

  (* secp256k1_u128_accum_u64(&t, (uint64)(bit>>6 == 2) << (bit & 63)) *)
  forward_call (v_t, t2, mkUInt64 ((if b / 64 =? 2 then 1 else 0) * 2 ^ (b mod 64)) (Haddr 2), Tsh).
  { assert (Hl : Z.land b 63 = b mod 64)
      by (change 63 with (Z.ones 6); rewrite Z.land_ones by lia; reflexivity).
    rewrite Hl.
    change (Int.unsigned Int64.iwordsize') with 64.
    rewrite Int.unsigned_repr by (pose proof (Z.mod_pos_bound b 64 ltac:(lia)); rep_lia).
    pose proof (Z.mod_pos_bound b 64 ltac:(lia)); lia. }
  { entailer!.
    rewrite cadd_arg_eval by (subst b; lia).
    reflexivity. }
  { rewrite Ht2, Ht1b.
    cbn [u64_val].
    pose proof (u128_range t1a) as Hr1a.
    assert (Ht1bn : 0 <= u128_val t1a / 2 ^ 64 < 2 ^ 64)
      by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
    pose proof (Haddr 2).
    assert (Hpp : (2 ^ 64 + 2 ^ 64 + 2 ^ 64 <= 2 ^ 128)%Z) by (vm_compute; congruence).
    lia. }
  Intros t2a.
  rename H into Ht2a.

  (* t'3 = secp256k1_u128_to_u64(&t); r->d[2] = t'3 *)
  forward_call (v_t, t2a, Tsh).
  Intros r3.
  rename H into Hr3.
  forward.

  (* secp256k1_u128_rshift(&t, 64) *)
  forward_call (v_t, t2a, 64, Tsh).
  Intros t2b.
  rename H into Ht2b.

  (* ===== Limb 3: t += r->d[3]; t += addend; r->d[3] = t ===== *)

  (* t'5 = r->d[3] *)
  forward.

  (* secp256k1_u128_accum_u64(&t, r->d[3]) *)
  forward_call (v_t, t2b, mkUInt64 ((r0 / 2 ^ 192) mod 2 ^ 64) Hd3, Tsh).
  Intros t3.
  rename H into Ht3.

  (* secp256k1_u128_accum_u64(&t, (uint64)(bit>>6 == 3) << (bit & 63)) *)
  forward_call (v_t, t3, mkUInt64 ((if b / 64 =? 3 then 1 else 0) * 2 ^ (b mod 64)) (Haddr 3), Tsh).
  { assert (Hl : Z.land b 63 = b mod 64)
      by (change 63 with (Z.ones 6); rewrite Z.land_ones by lia; reflexivity).
    rewrite Hl.
    change (Int.unsigned Int64.iwordsize') with 64.
    rewrite Int.unsigned_repr by (pose proof (Z.mod_pos_bound b 64 ltac:(lia)); rep_lia).
    pose proof (Z.mod_pos_bound b 64 ltac:(lia)); lia. }
  { entailer!.
    rewrite cadd_arg_eval by (subst b; lia).
    reflexivity. }
  { rewrite Ht3, Ht2b.
    cbn [u64_val].
    pose proof (u128_range t2a) as Hr2a.
    assert (Ht2bn : 0 <= u128_val t2a / 2 ^ 64 < 2 ^ 64)
      by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
    pose proof (Haddr 3).
    assert (Hpp : (2 ^ 64 + 2 ^ 64 + 2 ^ 64 <= 2 ^ 128)%Z) by (vm_compute; congruence).
    lia. }
  Intros t3a.
  rename H into Ht3a.

  (* t'4 = secp256k1_u128_to_u64(&t); r->d[3] = t'4 *)
  forward_call (v_t, t3a, Tsh).
  Intros r4.
  rename H into Hr4.
  forward.

  (* ===== Postcondition: the stored limbs reconstruct [r0 + flag*2^bit] ===== *)

  (* The four stored low-words are the base-2^64 limbs of [S = r0 + flag*2^bit]. *)
  set (S := scalar_val r0 + flag * 2 ^ bit) in *.
  assert (HSpos : 0 <= S).
  { subst S.
    pose proof (scalar_range r0).
    assert (0 <= flag * 2 ^ bit) by (apply Z.mul_nonneg_nonneg; [lia | apply Z.pow_nonneg; lia]).
    lia. }
  assert (HNlt : secp256k1_N < 2 ^ 256)
    by (unfold secp256k1_N; apply Z.ltb_lt; vm_compute; reflexivity).
  assert (HSlt : S < (2 ^ 64) ^ 4).
  { subst S.
    change ((2 ^ 64) ^ 4) with (2 ^ 256).
    lia. }

  (* Stored value of each limb, expressed via the carry chain. *)
  assert (Hr1v : u64_val r1 = (r0 mod 2 ^ 64
                 + (if b / 64 =? 0 then 1 else 0) * 2 ^ (b mod 64)) mod 2 ^ 64).
  { rewrite Hr1.
    unfold u128_lo.
    cbn [u64_val].
    rewrite Ht0a, Ht0.
    cbn [u64_val].
    reflexivity. }
  assert (Hr2v : u64_val r2 = ((r0 mod 2 ^ 64
                 + (if b / 64 =? 0 then 1 else 0) * 2 ^ (b mod 64)) / 2 ^ 64
                 + (r0 / 2 ^ 64) mod 2 ^ 64
                 + (if b / 64 =? 1 then 1 else 0) * 2 ^ (b mod 64)) mod 2 ^ 64).
  { rewrite Hr2.
    unfold u128_lo.
    cbn [u64_val].
    rewrite Ht1a, Ht1, Ht0b, Ht0a, Ht0.
    cbn [u64_val].
    reflexivity. }
  assert (Hr3v : u64_val r3 = ((((r0 mod 2 ^ 64
                 + (if b / 64 =? 0 then 1 else 0) * 2 ^ (b mod 64)) / 2 ^ 64
                 + (r0 / 2 ^ 64) mod 2 ^ 64
                 + (if b / 64 =? 1 then 1 else 0) * 2 ^ (b mod 64)) / 2 ^ 64)
                 + (r0 / 2 ^ 128) mod 2 ^ 64
                 + (if b / 64 =? 2 then 1 else 0) * 2 ^ (b mod 64)) mod 2 ^ 64).
  { rewrite Hr3.
    unfold u128_lo.
    cbn [u64_val].
    rewrite Ht2a, Ht2, Ht1b, Ht1a, Ht1, Ht0b, Ht0a, Ht0.
    cbn [u64_val].
    reflexivity. }
  assert (Hr4v : u64_val r4 = (((((r0 mod 2 ^ 64
                 + (if b / 64 =? 0 then 1 else 0) * 2 ^ (b mod 64)) / 2 ^ 64
                 + (r0 / 2 ^ 64) mod 2 ^ 64
                 + (if b / 64 =? 1 then 1 else 0) * 2 ^ (b mod 64)) / 2 ^ 64
                 + (r0 / 2 ^ 128) mod 2 ^ 64
                 + (if b / 64 =? 2 then 1 else 0) * 2 ^ (b mod 64)) / 2 ^ 64)
                 + (r0 / 2 ^ 192) mod 2 ^ 64
                 + (if b / 64 =? 3 then 1 else 0) * 2 ^ (b mod 64)) mod 2 ^ 64).
  { rewrite Hr4.
    unfold u128_lo.
    cbn [u64_val].
    rewrite Ht3a, Ht3, Ht2b, Ht2a, Ht2, Ht1b, Ht1a, Ht1, Ht0b, Ht0a, Ht0.
    cbn [u64_val].
    reflexivity. }

  (* The four limbs evaluate to [S]. *)
  assert (Heval : eval4 (2 ^ 64) (u64_val r1) (u64_val r2) (u64_val r3) (u64_val r4) = S).
  { rewrite Hr1v, Hr2v, Hr3v, Hr4v.
    rewrite (cadd_carry4 (2 ^ 64)
               (r0 mod 2 ^ 64) ((r0 / 2 ^ 64) mod 2 ^ 64)
               ((r0 / 2 ^ 128) mod 2 ^ 64) ((r0 / 2 ^ 192) mod 2 ^ 64)
               ((if b / 64 =? 0 then 1 else 0) * 2 ^ (b mod 64))
               ((if b / 64 =? 1 then 1 else 0) * 2 ^ (b mod 64))
               ((if b / 64 =? 2 then 1 else 0) * 2 ^ (b mod 64))
               ((if b / 64 =? 3 then 1 else 0) * 2 ^ (b mod 64)));
      [ | lia | exact Hd0 | exact Hd1 | exact Hd2 | exact Hd3
        | apply (Haddr 0) | apply (Haddr 1) | apply (Haddr 2) | apply (Haddr 3) | ].
    - (* the reconstructed sum = r0 + flag*2^bit = S *)
      assert (Hdsum : eval4 (2 ^ 64) (r0 mod 2 ^ 64) ((r0 / 2 ^ 64) mod 2 ^ 64)
                        ((r0 / 2 ^ 128) mod 2 ^ 64) ((r0 / 2 ^ 192) mod 2 ^ 64) = r0).
      { pose proof (eval4_limbs (2 ^ 64) (scalar_val r0) ltac:(lia)) as HE.
        unfold limb in HE.
        cbn [Z.of_nat Pos.of_succ_nat] in HE.
        rewrite Z.pow_0_r, Z.div_1_r, Z.pow_1_r in HE.
        change ((2 ^ 64) ^ 2) with (2 ^ 128) in HE.
        change ((2 ^ 64) ^ 3) with (2 ^ 192) in HE.
        apply HE.
        pose proof (scalar_range r0).
        pose proof HNlt.
        change ((2 ^ 64) ^ 4) with (2 ^ 256).
        lia. }
      rewrite Hdsum.
      pose proof (cadd_addend_sum bit flag Hbit Hflag) as Hsum.
      fold b in Hsum.
      rewrite Hsum.
      subst S; reflexivity.
    - (* the sum stays below (2^64)^4 *)
      assert (Hdsum : eval4 (2 ^ 64) (r0 mod 2 ^ 64) ((r0 / 2 ^ 64) mod 2 ^ 64)
                        ((r0 / 2 ^ 128) mod 2 ^ 64) ((r0 / 2 ^ 192) mod 2 ^ 64) = r0).
      { pose proof (eval4_limbs (2 ^ 64) (scalar_val r0) ltac:(lia)) as HE.
        unfold limb in HE.
        cbn [Z.of_nat Pos.of_succ_nat] in HE.
        rewrite Z.pow_0_r, Z.div_1_r, Z.pow_1_r in HE.
        change ((2 ^ 64) ^ 2) with (2 ^ 128) in HE.
        change ((2 ^ 64) ^ 3) with (2 ^ 192) in HE.
        apply HE.
        pose proof (scalar_range r0).
        pose proof HNlt.
        change ((2 ^ 64) ^ 4) with (2 ^ 256).
        lia. }
      rewrite Hdsum.
      pose proof (cadd_addend_sum bit flag Hbit Hflag) as Hsum.
      fold b in Hsum.
      rewrite Hsum.
      change ((2 ^ 64) ^ 4) with (2 ^ 256).
      lia. }

  (* Each stored limb is the corresponding base-2^64 digit of [S]. *)
  pose proof (Z.mod_pos_bound S (2 ^ 64) ltac:(lia)) as HSm.
  pose proof (u64_range r1) as Hr1r.
  pose proof (u64_range r2) as Hr2r.
  pose proof (u64_range r3) as Hr3r.
  pose proof (u64_range r4) as Hr4r.
  pose proof (limbs_eval4 (2 ^ 64) (u64_val r1) (u64_val r2) (u64_val r3) (u64_val r4)
                ltac:(lia) Hr1r Hr2r Hr3r Hr4r) as Hdig.
  rewrite Heval in Hdig.
  unfold limb in Hdig.
  cbn [Z.of_nat Pos.of_succ_nat] in Hdig.
  rewrite Z.pow_0_r, Z.div_1_r, Z.pow_1_r in Hdig.
  change ((2 ^ 64) ^ 2) with (2 ^ 128) in Hdig.
  change ((2 ^ 64) ^ 3) with (2 ^ 192) in Hdig.
  destruct Hdig as [Hg0 [Hg1 [Hg2 Hg3]]].

  (* Normalize the two top digit exponents to literal powers. *)
  replace ((2 ^ 64) ^ Z.pos (PosDef.Pos.succ 1)) with (2 ^ 128) in Hg2 by reflexivity.
  replace ((2 ^ 64) ^ Z.pos (PosDef.Pos.succ (PosDef.Pos.succ 1))) with (2 ^ 192) in Hg3 by reflexivity.

  (* Provide the result scalar [S] and match the stored representation. *)
  Exists (mkScalar (S mod secp256k1_N) (Z.mod_pos_bound S secp256k1_N ltac:(unfold secp256k1_N; lia))).
  assert (HSsmall : S mod secp256k1_N = S).
  { apply Z.mod_small.
    split; [exact HSpos|].
    subst S; exact Hno_overflow. }
  (* [entailer!] discharges [scalar_val r = r0 + flag*2^bit]; the data_at remains. *)
  entailer!.
  apply derives_refl'.
  f_equal.
  unfold scalar_to_val.
  cbn [scalar_val scalar_reduce].
  rewrite HSsmall.
  unfold uint64_to_val.
  rewrite Hg0, Hg1, Hg2, Hg3.
  reflexivity.
Qed.
