(** * Verif_scalar_mul_512: Proof of body_secp256k1_scalar_mul_512 *)
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
(** ** Accumulator lemmas -- [carry_bit_range] / [accum_carry_zero] / [extract_correct]. *)

(** The C accumulator is a [secp256k1_uint128] [acc] plus a 64-bit temp [c2]
    holding the bits above 128, so together they stand for the 192-bit value
    [u128_val acc + c2 * 2^128].  The lemmas below are the per-macro facts
    about that value. *)

(** The carry returned by [secp256k1_u128_accum_mul_carry], as a range.  The
    proof keeps one carry per [muladd] in context and [lia] case-splits on
    every disjunction it sees: with the disjunctions the file did not finish
    in 30 minutes, with the ranges it builds in about two. *)
Lemma carry_bit_range : forall k : Z,
  k = 0 \/ k = 1 ->
  0 <= k <= 1.
Proof.
  intros k Hk.
  lia.
Qed.

(** [muladd_fast]: when the exact sum fits in 128 bits, the carry returned by
    [secp256k1_u128_accum_mul_carry] is zero. *)
Lemma accum_carry_zero : forall (acc' : UInt128) (k s : Z),
  0 <= k <= 1 ->
  u128_val acc' + k * 2^128 = s ->
  s < 2^128 ->
  k = 0.
Proof.
  intros acc' k s Hk Hacc' Hs.
  pose proof (u128_range acc').
  lia.
Qed.

(** [extract]: the stored limb [to_u64(acc)] is the low 64 bits of the
    192-bit value, and the reloaded accumulator [c2 * 2^64 + hi_u64(acc)] is
    its quotient by [2^64]. *)
Lemma extract_correct : forall (acc acc' : UInt128) (lo hi : UInt64) (c2 : Z),
  lo = u128_lo acc ->
  hi = u128_hi acc ->
  u128_val acc' = u64_val hi + c2 * 2^64 ->
  u64_val lo = (u128_val acc + c2 * 2^128) mod 2^64 /\
  u128_val acc' = (u128_val acc + c2 * 2^128) / 2^64.
Proof.
  intros acc acc' lo hi c2 Hlo Hhi Hacc'.
  rewrite Hacc', Hlo, Hhi, u128_lo_val, u128_hi_val.
  replace (c2 * 2^128) with ((c2 * 2^64) * 2^64) by ring.
  split.
  - rewrite Z_mod_plus_full.
    reflexivity.
  - rewrite Z_div_plus_full by lia.
    reflexivity.
Qed.

(* ================================================================= *)
(** ** Macro tactics -- [muladd_step] / [muladd_fast_step] / [extract_step] / [extract_fast_step]. *)

(** One tactic per accumulator macro of [src/scalar_4x64_impl.h].  Each
    [muladd] call site first loads [a->d[i]] and [b->d[j]] into temps, and
    each [extract] stores [to_u64(&acc)] through a temp into [l8[i]], so the
    tactics step those statements too. *)

(** [muladd(a, b)]: [carry = accum_mul_carry(&acc, a, b); c2 += carry].  The
    [c2] temp stays in the form [Vlong (Int64.repr c)], with [c] the exact sum
    of the carries since the last [extract]. *)
Ltac muladd_step acc_ptr acc a b acc' k Hk Hacc' :=
  let vret := fresh "vret" in
  (* _t'i = a->d[i] *)
  forward;
  (* _t'j = b->d[j] *)
  forward;
  (* _t' = secp256k1_u128_accum_mul_carry(&acc, _t'i, _t'j) *)
  forward_call (acc_ptr, acc, a, b, Tsh);
  [ solve_param_match .. | Intros vret ];
  destruct vret as [acc' k];
  simpl fst in *;
  simpl snd in *;
  rename H into Hk;
  apply carry_bit_range in Hk;
  rename H0 into Hacc';
  (* carry = _t' *)
  forward;
  (* c2 += carry *)
  forward;
  rewrite Int.signed_repr by rep_lia;
  rewrite add64_repr;
  deadvars!.

(** [muladd_fast(a, b)]: [carry = accum_mul_carry(&acc, a, b)], with the
    carry left unused. *)
Ltac muladd_fast_step acc_ptr acc a b acc' k Hk Hacc' :=
  let vret := fresh "vret" in
  (* _t'i = a->d[i] *)
  forward;
  (* _t'j = b->d[j] *)
  forward;
  (* _t' = secp256k1_u128_accum_mul_carry(&acc, _t'i, _t'j) *)
  forward_call (acc_ptr, acc, a, b, Tsh);
  [ solve_param_match .. | Intros vret ];
  destruct vret as [acc' k];
  simpl fst in *;
  simpl snd in *;
  rename H into Hk;
  apply carry_bit_range in Hk;
  rename H0 into Hacc';
  (* carry = _t' *)
  forward;
  deadvars!.

(** [extract(n)]: [n = to_u64(&acc); load(&acc, c2, hi_u64(&acc)); c2 = 0].
    Leaves [Hr] and [Hacc'] as stated by [extract_correct]. *)
Ltac extract_step acc_ptr acc r Hr acc' Hacc' :=
  let Hlo := fresh "Hlo" in
  let hi := fresh "hi" in
  let Hhi := fresh "Hhi" in
  let Hc2 := fresh "Hc2" in
  let Hload := fresh "Hload" in
  (* _t' = secp256k1_u128_to_u64(&acc) *)
  forward_call (acc_ptr, acc, Tsh);
  Intros r;
  rename H into Hlo;
  (* l8[i] = _t' *)
  forward;
  (* _t'' = secp256k1_u128_hi_u64(&acc) *)
  forward_call (acc_ptr, acc, Tsh);
  Intros hi;
  rename H into Hhi;
  (* secp256k1_u128_load(&acc, c2, _t'') -- the c2 value is read off LOCAL *)
  match goal with
  | |- context [temp _c2 (Vlong (Int64.repr ?c2))] =>
      assert (Hc2 : 0 <= c2 < 2^64) by rep_lia;
      forward_call (acc_ptr, mkUInt64 c2 Hc2, hi, Tsh)
  end;
  Intros acc';
  rename H into Hload;
  simpl u64_val in Hload;
  (* c2 = 0 *)
  forward;
  change (Int.signed (Int.repr 0)) with 0;
  deadvars!;
  destruct (extract_correct acc acc' r hi _ Hlo Hhi Hload) as [Hr Hacc'];
  clear Hlo Hhi Hload Hc2 hi.

(** [extract_fast(n)]: [n = to_u64(&acc); rshift(&acc, 64)], used where
    [c2] is zero.  No [deadvars!] here: the last [extract_fast] ends the
    function body, so its goal is the postcondition rather than a [semax]. *)
Ltac extract_fast_step acc_ptr acc r Hr acc' Hacc' :=
  let Hlo := fresh "Hlo" in
  (* _t' = secp256k1_u128_to_u64(&acc) *)
  forward_call (acc_ptr, acc, Tsh);
  Intros r;
  rename H into Hlo;
  (* l8[i] = _t' *)
  forward;
  (* secp256k1_u128_rshift(&acc, 64) *)
  forward_call (acc_ptr, acc, 64, Tsh);
  Intros acc';
  rename H into Hacc';
  assert (Hr : u64_val r = u128_val acc mod 2^64) by (rewrite Hlo; apply u128_lo_val);
  clear Hlo.

(* ================================================================= *)
(** ** secp256k1_scalar_mul_512 -- [l8 = a * b (full 512-bit product)]. *)

Lemma body_secp256k1_scalar_mul_512:
  semax_body Vprog Gprog f_secp256k1_scalar_mul_512 spec_secp256k1_scalar_mul_512.
Proof.
  start_function.
  rename SH into Hsh_l_writable.
  rename SH0 into Hsh_a_readable.
  rename SH1 into Hsh_b_readable.

  (* Provide the Inhabitant witness for deadvars! *)
  assert (Inh_UInt512 : UInt512)
    by exact (mkUInt512 0 ltac:(lia)).

  (* Name the UInt64 limbs for all 8 scalar components *)
  set (a0 := u256_limb a 0).
  set (a1 := u256_limb a 1).
  set (a2 := u256_limb a 2).
  set (a3 := u256_limb a 3).
  set (b0 := u256_limb b 0).
  set (b1 := u256_limb b 1).
  set (b2 := u256_limb b 2).
  set (b3 := u256_limb b 3).

  (* All 16 limb products are bounded by (2^64-1)^2 *)
  pose proof (u64_mul_bound a0 b0) as Hab00.
  pose proof (u64_mul_bound a0 b1) as Hab01.
  pose proof (u64_mul_bound a0 b2) as Hab02.
  pose proof (u64_mul_bound a0 b3) as Hab03.
  pose proof (u64_mul_bound a1 b0) as Hab10.
  pose proof (u64_mul_bound a1 b1) as Hab11.
  pose proof (u64_mul_bound a1 b2) as Hab12.
  pose proof (u64_mul_bound a1 b3) as Hab13.
  pose proof (u64_mul_bound a2 b0) as Hab20.
  pose proof (u64_mul_bound a2 b1) as Hab21.
  pose proof (u64_mul_bound a2 b2) as Hab22.
  pose proof (u64_mul_bound a2 b3) as Hab23.
  pose proof (u64_mul_bound a3 b0) as Hab30.
  pose proof (u64_mul_bound a3 b1) as Hab31.
  pose proof (u64_mul_bound a3 b2) as Hab32.
  pose proof (u64_mul_bound a3 b3) as Hab33.

  (* ===== Init: c2 = 0, acc = 0 ===== *)

  forward. (* c2 = 0 *)
  change (Int.signed (Int.repr 0)) with 0.

  assert (Hzero_range : 0 <= 0 < 2^64) by lia.
  (* init(0) -- secp256k1_u128_from_u64(&acc, 0) *)
  forward_call (v_acc, mkUInt64 0 Hzero_range, Tsh).
  Intros acc_init.
  rename H into Hacc_init.
  simpl u64_val in Hacc_init.
  clear Hzero_range.

  (* ===== Round 0: l8[0] = a0*b0 (muladd_fast + extract_fast) ===== *)

  (* muladd_fast(a->d[0], b->d[0]) *)
  muladd_fast_step v_acc acc_init a0 b0 acc0 k0 Hk0 Hacc0.

  (* A single product fits in 128 bits, so the carry is zero *)
  assert (Hk0_zero : k0 = 0).
  { apply (accum_carry_zero acc0 k0 (u128_val acc_init + u64_val a0 * u64_val b0)).
    - exact Hk0.
    - exact Hacc0.
    - rewrite Hacc_init.
      apply mul_u64_lt_u128; rep_lia. }
  subst k0.

  assert (HV0 : u128_val acc0 = u64_val a0 * u64_val b0) by lia.
  clear Hacc0 Hk0 Hacc_init acc_init.

  (* extract_fast(l8[0]) *)
  extract_fast_step v_acc acc0 r0 Hr0 carry0 Hcarry0.

  assert (Hcarry0_ub : u128_val carry0 <= 2^64 - 2).
  { rewrite Hcarry0, HV0.
    apply (carry_div_ub_eq _ ((2^64 - 1) * (2^64 - 1)) _); lia. }
  clear Hab00.

  (* ===== Round 1: l8[1] = a0*b1 + a1*b0 (2 products) ===== *)

  (* muladd(a->d[0], b->d[1]) *)
  muladd_step v_acc carry0 a0 b1 acc1a k1a Hk1a Hacc1a.

  (* muladd(a->d[1], b->d[0]) *)
  muladd_step v_acc acc1a a1 b0 acc1 k1b Hk1b Hacc1.

  (* The 192-bit value acc + c2 * 2^128 after round 1 *)
  assert (HV1 : u128_val acc1 + (0 + k1a + k1b) * 2^128 =
    u128_val carry0 + u64_val a0 * u64_val b1 + u64_val a1 * u64_val b0) by lia.
  clear Hacc1a Hacc1.

  (* extract(l8[1]) *)
  extract_step v_acc acc1 r1 Hr1 carry1 Hcarry1.

  assert (Hcarry1_ub : u128_val carry1 <= 2 * 2^64 - 3).
  { rewrite Hcarry1, HV1.
    apply (carry_div_ub_eq _ ((2^64 - 2) + 2 * ((2^64 - 1) * (2^64 - 1))) _); lia. }
  clear Hab01 Hab10.

  (* ===== Round 2: l8[2] = a0*b2 + a1*b1 + a2*b0 (3 products) ===== *)

  (* muladd(a->d[0], b->d[2]) *)
  muladd_step v_acc carry1 a0 b2 acc2a k2a Hk2a Hacc2a.

  (* muladd(a->d[1], b->d[1]) *)
  muladd_step v_acc acc2a a1 b1 acc2b k2b Hk2b Hacc2b.

  (* muladd(a->d[2], b->d[0]) *)
  muladd_step v_acc acc2b a2 b0 acc2 k2c Hk2c Hacc2.

  (* The 192-bit value acc + c2 * 2^128 after round 2 *)
  assert (HV2 : u128_val acc2 + (0 + k2a + k2b + k2c) * 2^128 =
    u128_val carry1 + u64_val a0 * u64_val b2 + u64_val a1 * u64_val b1
    + u64_val a2 * u64_val b0) by lia.
  clear Hacc2a Hacc2b Hacc2.

  (* extract(l8[2]) *)
  extract_step v_acc acc2 r2 Hr2 carry2 Hcarry2.

  assert (Hcarry2_ub : u128_val carry2 <= 3 * 2^64 - 4).
  { rewrite Hcarry2, HV2.
    apply (carry_div_ub_eq _ ((2 * 2^64 - 3) + 3 * ((2^64 - 1) * (2^64 - 1))) _); lia. }
  clear Hab02 Hab11 Hab20.

  (* ===== Round 3: l8[3] = a0*b3 + a1*b2 + a2*b1 + a3*b0 (4 products) ===== *)

  (* muladd(a->d[0], b->d[3]) *)
  muladd_step v_acc carry2 a0 b3 acc3a k3a Hk3a Hacc3a.

  (* muladd(a->d[1], b->d[2]) *)
  muladd_step v_acc acc3a a1 b2 acc3b k3b Hk3b Hacc3b.

  (* muladd(a->d[2], b->d[1]) *)
  muladd_step v_acc acc3b a2 b1 acc3c k3c Hk3c Hacc3c.

  (* muladd(a->d[3], b->d[0]) *)
  muladd_step v_acc acc3c a3 b0 acc3 k3d Hk3d Hacc3.

  (* The 192-bit value acc + c2 * 2^128 after round 3 *)
  assert (HV3 : u128_val acc3 + (0 + k3a + k3b + k3c + k3d) * 2^128 =
    u128_val carry2 + u64_val a0 * u64_val b3 + u64_val a1 * u64_val b2
    + u64_val a2 * u64_val b1 + u64_val a3 * u64_val b0) by lia.
  clear Hacc3a Hacc3b Hacc3c Hacc3.

  (* extract(l8[3]) *)
  extract_step v_acc acc3 r3 Hr3 carry3 Hcarry3.

  assert (Hcarry3_ub : u128_val carry3 <= 4 * 2^64 - 5).
  { rewrite Hcarry3, HV3.
    apply (carry_div_ub_eq _ ((3 * 2^64 - 4) + 4 * ((2^64 - 1) * (2^64 - 1))) _); lia. }
  clear Hab03 Hab12 Hab21 Hab30.

  (* ===== Round 4: l8[4] = a1*b3 + a2*b2 + a3*b1 (3 products) ===== *)

  (* muladd(a->d[1], b->d[3]) *)
  muladd_step v_acc carry3 a1 b3 acc4a k4a Hk4a Hacc4a.

  (* muladd(a->d[2], b->d[2]) *)
  muladd_step v_acc acc4a a2 b2 acc4b k4b Hk4b Hacc4b.

  (* muladd(a->d[3], b->d[1]) *)
  muladd_step v_acc acc4b a3 b1 acc4 k4c Hk4c Hacc4.

  (* The 192-bit value acc + c2 * 2^128 after round 4 *)
  assert (HV4 : u128_val acc4 + (0 + k4a + k4b + k4c) * 2^128 =
    u128_val carry3 + u64_val a1 * u64_val b3 + u64_val a2 * u64_val b2
    + u64_val a3 * u64_val b1) by lia.
  clear Hacc4a Hacc4b Hacc4.

  (* extract(l8[4]) *)
  extract_step v_acc acc4 r4 Hr4 carry4 Hcarry4.

  assert (Hcarry4_ub : u128_val carry4 <= 3 * 2^64 - 3).
  { rewrite Hcarry4, HV4.
    apply (carry_div_ub_eq _ ((4 * 2^64 - 5) + 3 * ((2^64 - 1) * (2^64 - 1))) _); lia. }
  clear Hab13 Hab22 Hab31.

  (* ===== Round 5: l8[5] = a2*b3 + a3*b2 (2 products) ===== *)

  (* muladd(a->d[2], b->d[3]) *)
  muladd_step v_acc carry4 a2 b3 acc5a k5a Hk5a Hacc5a.

  (* muladd(a->d[3], b->d[2]) *)
  muladd_step v_acc acc5a a3 b2 acc5 k5b Hk5b Hacc5.

  (* The 192-bit value acc + c2 * 2^128 after round 5 *)
  assert (HV5 : u128_val acc5 + (0 + k5a + k5b) * 2^128 =
    u128_val carry4 + u64_val a2 * u64_val b3 + u64_val a3 * u64_val b2) by lia.
  clear Hacc5a Hacc5.

  (* extract(l8[5]) *)
  extract_step v_acc acc5 r5 Hr5 carry5 Hcarry5.

  assert (Hcarry5_ub : u128_val carry5 <= 2 * 2^64 - 2).
  { rewrite Hcarry5, HV5.
    apply (carry_div_ub_eq _ ((3 * 2^64 - 3) + 2 * ((2^64 - 1) * (2^64 - 1))) _); lia. }
  clear Hab23 Hab32.

  (* ===== Round 6: l8[6], l8[7] = a3*b3 (muladd_fast + two extract_fast) ===== *)

  (* muladd_fast(a->d[3], b->d[3]) *)
  muladd_fast_step v_acc carry5 a3 b3 acc6 k6 Hk6 Hacc6.

  (* The round 5 carry bound keeps this sum below 2^128, so the carry is zero *)
  assert (Hk6_zero : k6 = 0).
  { apply (accum_carry_zero acc6 k6 (u128_val carry5 + u64_val a3 * u64_val b3)).
    - exact Hk6.
    - exact Hacc6.
    - lia. }
  subst k6.

  assert (HV6 : u128_val acc6 = u128_val carry5 + u64_val a3 * u64_val b3) by lia.
  clear Hacc6 Hk6 Hab33.

  (* extract_fast(l8[6]) *)
  extract_fast_step v_acc acc6 r6 Hr6 carry6 Hcarry6.

  (* extract_fast(l8[7]) *)
  extract_fast_step v_acc carry6 r7 Hr7 carry7 Hcarry7.

  (* ===== Cleanup: provide witness and strip VST machinery ===== *)

  Exists (mul_256 a b).
  entailer!.

  (* Reduce to list equality *)
  apply derives_refl'.
  f_equal.

  (* The eight stores into the default array give the list of the limbs *)
  transitivity [uint64_to_val r0; uint64_to_val r1; uint64_to_val r2;
                uint64_to_val r3; uint64_to_val r4; uint64_to_val r5;
                uint64_to_val r6; uint64_to_val r7].
  { reflexivity. }

  (* Remove all VST/pointer/bounds context -- keep only pure Z facts *)
  clear - a b
    HV0 Hcarry0 Hr0
    HV1 Hcarry1 Hr1
    HV2 Hcarry2 Hr2
    HV3 Hcarry3 Hr3
    HV4 Hcarry4 Hr4
    HV5 Hcarry5 Hr5
    HV6 Hcarry6 Hr6
    Hr7.

  (* Strip Vlong/Int64.repr wrappers *)
  unfold uint512_to_val, uint64_to_val.
  rewrite Hr0, Hr1, Hr2, Hr3, Hr4, Hr5, Hr6, Hr7.

  (* ===== Postcondition: prove mul_256 correctness via schoolbook lemma ===== *)

  pose proof (schoolbook_mul_4x4 (2^64) ltac:(lia)
    (u64_val a0) (u64_val a1) (u64_val a2) (u64_val a3)
    (u64_val b0) (u64_val b1) (u64_val b2) (u64_val b3)
    ltac:(rep_lia) ltac:(rep_lia) ltac:(rep_lia) ltac:(rep_lia)
    ltac:(rep_lia) ltac:(rep_lia) ltac:(rep_lia) ltac:(rep_lia)
    _ HV0 _ Hcarry0
    _ HV1 _ Hcarry1
    _ HV2 _ Hcarry2
    _ HV3 _ Hcarry3
    _ HV4 _ Hcarry4
    _ HV5 _ Hcarry5
    _ HV6 _ Hcarry6
  ) as Hschoolbook.

  (* The schoolbook lemma talks about eval4, connect to u256_val *)
  assert (Heval_a : eval4 (2^64) (u64_val a0) (u64_val a1) (u64_val a2) (u64_val a3) = u256_val a)
    by (subst a0 a1 a2 a3; exact (u256_as_eval4 a)).
  assert (Heval_b : eval4 (2^64) (u64_val b0) (u64_val b1) (u64_val b2) (u64_val b3) = u256_val b)
    by (subst b0 b1 b2 b3; exact (u256_as_eval4 b)).

  rewrite Heval_a, Heval_b in Hschoolbook.
  unfold mul_256.
  simpl u512_val.
  destruct Hschoolbook as (-> & -> & -> & -> & -> & -> & -> & ->).
  reflexivity.
Qed.
