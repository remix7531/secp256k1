(** * Verif_scalar_add: Proof of body_secp256k1_scalar_add *)
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
(** ** Stage lemmas -- the pure-Z content of the ripple add, shared by both branches. *)

(** [secp256k1_scalar_add] has two straight-line branches (in-place and
    three-distinct-chunks) running the identical arithmetic, so every
    mathematical stage of the body proof is stated here once and used twice.
    The workhorse is the four-constant ripple-add carry chain
    [theory.arithmetic.add4_carry_chain] (every limb gets a per-limb addend
    [c_i], unlike the three-constant [reduce_carry_chain]); it is shared with
    [scalar_negate] and [scalar_half]. *)

(** Per-round bound: the carry out of a two-limb 64-bit add is [0] or [1].
    This is what keeps each ripple accumulator below [2^128], discharging the
    [secp256k1_u128_accum_u64] precondition of the two round-1 calls. *)
Lemma scalar_add_carry_bnd : forall x y : Z,
  0 <= x < 2^64 ->
  0 <= y < 2^64 ->
  0 <= (x + y) / 2^64 < 2.
Proof.
  intros x y Hx Hy.
  split.
  - apply Z.div_pos; lia.
  - apply Z.div_lt_upper_bound; lia.
Qed.

(** Stage 1: the ripple add of two scalars, limb by limb.  [t0..t3] are the
    four accumulator values the C code builds ([t_(i+1)] takes the carry
    [t_i / 2^64] of its predecessor), [rz] is the little-endian evaluation of
    the four stored low words [t_i mod 2^64], and [t3 / 2^64] is the carry-out
    the C code reads back as [c4].  Together they reconstruct [s + t]:
    [rz] is the low 256 bits and the carry-out is the 257th bit. *)
Lemma scalar_add_ripple_eq : forall s t : Scalar,
  let a0 := limb (2^64) (scalar_val s) 0 in
  let a1 := limb (2^64) (scalar_val s) 1 in
  let a2 := limb (2^64) (scalar_val s) 2 in
  let a3 := limb (2^64) (scalar_val s) 3 in
  let b0 := limb (2^64) (scalar_val t) 0 in
  let b1 := limb (2^64) (scalar_val t) 1 in
  let b2 := limb (2^64) (scalar_val t) 2 in
  let b3 := limb (2^64) (scalar_val t) 3 in
  let t0 := a0 + b0 in
  let t1 := t0 / 2^64 + a1 + b1 in
  let t2 := t1 / 2^64 + a2 + b2 in
  let t3 := t2 / 2^64 + a3 + b3 in
  let rz := t0 mod 2^64 + t1 mod 2^64 * 2^64
          + t2 mod 2^64 * (2^64*2^64) + t3 mod 2^64 * (2^64*2^64*2^64) in
  rz + t3 / 2^64 * 2^256 = scalar_val s + scalar_val t
  /\ 0 <= rz < 2^256
  /\ 0 <= t3 / 2^64 <= 1.
Proof.
  intros s t a0 a1 a2 a3 b0 b1 b2 b3 t0 t1 t2 t3 rz.

  assert (Ha0 : 0 <= a0 < 2^64) by (subst a0; apply Z.mod_pos_bound; lia).
  assert (Ha1 : 0 <= a1 < 2^64) by (subst a1; apply Z.mod_pos_bound; lia).
  assert (Ha2 : 0 <= a2 < 2^64) by (subst a2; apply Z.mod_pos_bound; lia).
  assert (Ha3 : 0 <= a3 < 2^64) by (subst a3; apply Z.mod_pos_bound; lia).
  assert (Hb0 : 0 <= b0 < 2^64) by (subst b0; apply Z.mod_pos_bound; lia).
  assert (Hb1 : 0 <= b1 < 2^64) by (subst b1; apply Z.mod_pos_bound; lia).
  assert (Hb2 : 0 <= b2 < 2^64) by (subst b2; apply Z.mod_pos_bound; lia).
  assert (Hb3 : 0 <= b3 < 2^64) by (subst b3; apply Z.mod_pos_bound; lia).

  (* Setup: each operand decomposes into its four 64-bit limbs. *)
  assert (Hsdec :
    a0 + a1 * 2^64 + a2 * (2^64*2^64) + a3 * (2^64*2^64*2^64) = scalar_val s).
  { pose proof (eval4_limbs (2^64) (scalar_val s) ltac:(lia)) as Es.
    unfold eval4 in Es.
    fold a0 a1 a2 a3 in Es.
    pose proof (scalar_range s) as Hrs.
    change ((2^64)^4) with (2^256) in Es.
    unfold secp256k1_N in Hrs.
    replace ((2^64)^2) with (2^64*2^64) in Es by ring.
    replace ((2^64)^3) with (2^64*2^64*2^64) in Es by ring.
    rewrite Es by lia.
    reflexivity. }

  assert (Htdec :
    b0 + b1 * 2^64 + b2 * (2^64*2^64) + b3 * (2^64*2^64*2^64) = scalar_val t).
  { pose proof (eval4_limbs (2^64) (scalar_val t) ltac:(lia)) as Et.
    unfold eval4 in Et.
    fold b0 b1 b2 b3 in Et.
    pose proof (scalar_range t) as Hrt.
    change ((2^64)^4) with (2^256) in Et.
    unfold secp256k1_N in Hrt.
    replace ((2^64)^2) with (2^64*2^64) in Et by ring.
    replace ((2^64)^3) with (2^64*2^64*2^64) in Et by ring.
    rewrite Et by lia.
    reflexivity. }

  (* Main: the carry chain, with the sum bound it needs. *)
  pose proof (add4_carry_chain (2^64) a0 a1 a2 a3 b0 b1 b2 b3
    ltac:(lia) Ha0 Ha1 Ha2 Ha3
    ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as Hchain0.
  cbv zeta in Hchain0.
  unfold eval4 in Hchain0.
  replace ((2^64)^2) with (2^64*2^64) in Hchain0 by ring.
  replace ((2^64)^3) with (2^64*2^64*2^64) in Hchain0 by ring.

  assert (Hchain_bnd :
    0 <= a0 + a1 * 2^64 + a2 * (2^64*2^64) + a3 * (2^64*2^64*2^64)
       + (b0 + b1 * 2^64 + b2 * (2^64*2^64) + b3 * (2^64*2^64*2^64))
       < 2 * (2^64*2^64*2^64*2^64)).
  { rewrite Hsdec, Htdec.
    pose proof (scalar_range s).
    pose proof (scalar_range t).
    change (2^64*2^64*2^64*2^64) with (2^256).
    unfold secp256k1_N in *.
    lia. }
  destruct (Hchain0 Hchain_bnd) as [Hchain_eq [Hrz_bnd Hhi_bnd]].
  rewrite Hsdec, Htdec in Hchain_eq.
  change (2^64*2^64*2^64*2^64) with (2^256) in Hchain_eq, Hrz_bnd.

  (* Closeout: the three conjuncts, up to unfolding the [let]s. *)
  split.
  - (* conjunct 1: the stored words plus the carry reconstruct [s + t] *)
    exact Hchain_eq.
  - split.
    + (* conjunct 2: the stored words are the low 256 bits *)
      exact Hrz_bnd.
    + (* conjunct 3: the carry-out is a bit *)
      exact Hhi_bnd.
Qed.

(** Stage 2: the four 64-bit limbs of the ripple result [rz] are exactly the
    low words [t_i mod 2^64] the C code stored, so the four-limb [data_at]
    the stores leave behind is [uint256_to_val] of [rz]. *)
Lemma scalar_add_store_eq : forall t0 t1 t2 t3 rz : Z,
  rz = t0 mod 2^64 + t1 mod 2^64 * 2^64
     + t2 mod 2^64 * (2^64*2^64) + t3 mod 2^64 * (2^64*2^64*2^64) ->
  rz mod 2^64 = t0 mod 2^64
  /\ (rz / 2^64) mod 2^64 = t1 mod 2^64
  /\ (rz / 2^128) mod 2^64 = t2 mod 2^64
  /\ (rz / 2^192) mod 2^64 = t3 mod 2^64.
Proof.
  intros t0 t1 t2 t3 rz Hrz.

  (* Setup: extract the four digits of the evaluation, then fold it to [rz]. *)
  pose proof (limbs_eval4 (2^64) (t0 mod 2^64) (t1 mod 2^64) (t2 mod 2^64) (t3 mod 2^64)
    ltac:(lia)
    ltac:(apply Z.mod_pos_bound; lia)
    ltac:(apply Z.mod_pos_bound; lia)
    ltac:(apply Z.mod_pos_bound; lia)
    ltac:(apply Z.mod_pos_bound; lia)) as [Hl0 [Hl1 [Hl2 Hl3]]].
  unfold eval4 in Hl0, Hl1, Hl2, Hl3.
  replace ((2^64)^2) with (2^64*2^64) in Hl0, Hl1, Hl2, Hl3 by ring.
  replace ((2^64)^3) with (2^64*2^64*2^64) in Hl0, Hl1, Hl2, Hl3 by ring.
  rewrite <- Hrz in Hl0, Hl1, Hl2, Hl3.

  (* Main: normalize each digit to the [rz / 2^(64*i)] divisor shape that
     [uint256_to_val] uses. *)
  unfold limb in Hl0, Hl1, Hl2, Hl3.
  simpl Z.of_nat in Hl0, Hl1, Hl2, Hl3.
  rewrite Z.pow_0_r, Z.div_1_r in Hl0.
  rewrite Z.pow_1_r in Hl1.
  change ((2^64)^2) with (2^128) in Hl2.
  change ((2^64)^3) with (2^192) in Hl3.

  (* Closeout: one conjunct per limb. *)
  repeat split.
  - (* limb 0 *)
    exact Hl0.
  - (* limb 1 *)
    exact Hl1.
  - (* limb 2 *)
    exact Hl2.
  - (* limb 3 *)
    exact Hl3.
Qed.

(** Stages 3-5: the two postcondition facts of [secp256k1_scalar_add],
    packaged as a pure-Z lemma.  [S = a + b], [rz] is the low 256 bits and
    [hi in {0,1}] the carry-out of the ripple add, and [cov] is the overflow
    flag from [check_overflow] (1 iff [rz >= N]).  The conjuncts state that
    (1) the returned flag [hi + cov] is [1] iff [a + b >= N], and
    (2) the conditional reduction yields [(a + b) mod N]. *)
Lemma scalar_add_flag_reduce_eq :
  forall (N S rz hi cov : Z),
    0 < N < 2^256 ->
    0 <= S < 2 * N ->
    (hi = 0 \/ hi = 1) ->
    rz + hi * 2^256 = S ->
    0 <= rz < 2^256 ->
    cov = (if Z_lt_dec rz N then 0 else 1) ->
    hi + cov = (if Z_le_dec N S then 1 else 0)
    /\ (rz + (hi + cov) * (2^256 - N)) mod 2^256 = S mod N.
Proof.
  intros N S rz hi cov HN HS Hhi Heq Hrz Hcov.
  assert (HNpos : 0 < N) by lia.
  destruct Hhi as [Hhi|Hhi]; subst hi.

  (* branch: hi = 0 -- no carry beyond 256 bits, so rz = S < 2^256. *)
  - rewrite Z.mul_0_l, Z.add_0_r in Heq.
    subst rz.
    destruct (Z_lt_dec S N) as [Hlt|Hge].
    + (* branch: S < N -- no reduction. *)
      subst cov.
      destruct (Z_lt_dec S N) as [_|Hcon]; [|lia].
      destruct (Z_le_dec N S) as [Hcon|_]; [lia|].
      split.
      * reflexivity.
      * rewrite Z.mul_0_l, Z.add_0_r.
        rewrite Z.mod_small by lia.
        rewrite (Z.mod_small S N) by lia.
        reflexivity.
    + (* branch: N <= S < 2^256 -- subtract N once. *)
      subst cov.
      destruct (Z_lt_dec S N) as [Hcon|_]; [lia|].
      destruct (Z_le_dec N S) as [_|Hcon]; [|lia].
      split.
      * reflexivity.
      * rewrite Z.mul_1_l.
        replace (S + (2^256 - N)) with ((S - N) + 1 * 2^256) by ring.
        rewrite Z_mod_plus_full.
        rewrite (Z.mod_small (S - N) (2^256)) by lia.
        symmetry.
        rewrite (Z.mod_eq S N) by lia.
        assert (S / N = 1) by (symmetry; apply Z.div_unique_pos with (r := S - N); lia).
        lia.

  (* branch: hi = 1 -- a carry occurred, so S >= 2^256 and rz = S - 2^256 < N. *)
  - assert (Hrz_eq : rz = S - 2^256) by lia.
    assert (HSge : 2^256 <= S) by lia.
    assert (Hcov0 : cov = 0).
    { rewrite Hcov.
      destruct (Z_lt_dec rz N) as [_|Hcon]; [reflexivity|].
      exfalso. apply Hcon. lia. }
    rewrite Hcov0.
    destruct (Z_le_dec N S) as [_|Hcon]; [|lia].
    split.
    + reflexivity.
    + rewrite Z.add_0_r, Z.mul_1_l.
      replace (rz + (2^256 - N)) with ((S - N) + 0 * 2^256) by lia.
      rewrite Z_mod_plus_full.
      rewrite (Z.mod_small (S - N) (2^256)) by lia.
      symmetry.
      rewrite (Z.mod_eq S N) by lia.
      assert (S / N = 1) by (symmetry; apply Z.div_unique_pos with (r := S - N); lia).
      lia.
Qed.

(* ================================================================= *)
(** ** secp256k1_scalar_add -- [(a + b) mod N], returns the overflow flag. *)

(** The funspec is mode-parametrized over [alias : bool].  When [alias = true]
    the call is in-place ([a_ptr = r_ptr], [b] a distinct readable chunk);
    when [alias = false] all three pointers address distinct chunks.  The two
    branches run the identical ripple-add arithmetic: [b] is always read from
    its own untouched chunk, and in the aliased branch each [a->d[i]] load
    reads from the evolving [r_ptr] chunk at index [i], which still holds [a]'s
    limb [i] because earlier rounds only wrote limbs [0..i-1]
    ([solve_param_match] reduces the [Znth i (upd_Znth ...)] back to [a]'s
    limb automatically). *)
Lemma body_secp256k1_scalar_add:
  semax_body Vprog Gprog
    f_secp256k1_scalar_add spec_secp256k1_scalar_add.
Proof.
  start_function.

  destruct alias.

  (* ===== branch: alias = true -- in-place add(r, r, b); r_ptr = a_ptr, b distinct ===== *)
  - specialize (H eq_refl).
    subst a_ptr.
    clear H0.
    rename SH into Hsh_r.
    rename SH0 into Hsh_b.

    (* ===== Stage 0: name the input limbs and their ranges ===== *)

    set (a0 := limb (2^64) (scalar_val a) 0).
    set (a1 := limb (2^64) (scalar_val a) 1).
    set (a2 := limb (2^64) (scalar_val a) 2).
    set (a3 := limb (2^64) (scalar_val a) 3).
    set (b0 := limb (2^64) (scalar_val b) 0).
    set (b1 := limb (2^64) (scalar_val b) 1).
    set (b2 := limb (2^64) (scalar_val b) 2).
    set (b3 := limb (2^64) (scalar_val b) 3).

    assert (Ha0 : 0 <= a0 < 2^64) by (subst a0; apply Z.mod_pos_bound; lia).
    assert (Ha1 : 0 <= a1 < 2^64) by (subst a1; apply Z.mod_pos_bound; lia).
    assert (Ha2 : 0 <= a2 < 2^64) by (subst a2; apply Z.mod_pos_bound; lia).
    assert (Ha3 : 0 <= a3 < 2^64) by (subst a3; apply Z.mod_pos_bound; lia).
    assert (Hb0 : 0 <= b0 < 2^64) by (subst b0; apply Z.mod_pos_bound; lia).
    assert (Hb1 : 0 <= b1 < 2^64) by (subst b1; apply Z.mod_pos_bound; lia).
    assert (Hb2 : 0 <= b2 < 2^64) by (subst b2; apply Z.mod_pos_bound; lia).
    assert (Hb3 : 0 <= b3 < 2^64) by (subst b3; apply Z.mod_pos_bound; lia).

    (* Flatten the aliased SEP conjunction [scalar_at r * scalar_at b]. *)
    Intros.

    (* ===== Round 0: t = a[0] + b[0] ===== *)

    (* _t'14 = a->d[0] (reads the r/a chunk, still holding a) *)
    forward.

    (* secp256k1_u128_from_u64(&t, a->d[0]) *)
    forward_call_u128_from_u64 v_t (mkUInt64 a0 Ha0) Tsh t_init Ht_init.
    { entailer!.
      subst a0.
      unfold scalar_to_val, Znth.
      simpl.
      rewrite limb_fold0.
      reflexivity. }

    (* _t'13 = b->d[0] *)
    forward.

    (* secp256k1_u128_accum_u64(&t, b->d[0]) *)
    forward_call_u128_accum_u64 v_t t_init (mkUInt64 b0 Hb0) Tsh acc0 Hacc0_raw.
    { entailer!.
      subst b0.
      unfold scalar_to_val, Znth.
      simpl.
      rewrite limb_fold0.
      reflexivity. }
    assert (Hacc0 : u128_val acc0 = a0 + b0)
      by (rewrite Hacc0_raw, Ht_init; reflexivity).
    clear Ht_init Hacc0_raw t_init.

    (* r->d[0] = secp256k1_u128_to_u64(&t) (overwrites limb 0 of the r/a chunk) *)
    forward_call_u128_to_u64 v_t acc0 Tsh lo0 Hlo0.
    forward.

    (* secp256k1_u128_rshift(&t, 64) *)
    forward_call_u128_rshift v_t acc0 Tsh carry0 Hcarry0.
    assert (Hcarry0_val : u128_val carry0 = (a0 + b0) / 2^64)
      by (rewrite Hcarry0, Hacc0; reflexivity).
    clear Hcarry0.

    (* The round-0 carry is a bit ([scalar_add_carry_bnd]); with it in context
       the wrapper discharges the [< 2^128] precondition of both round-1
       accumulate calls. *)
    pose proof (scalar_add_carry_bnd a0 b0 Ha0 Hb0) as Hcarry0_bnd.

    (* ===== Round 1: t += a[1] + b[1] ===== *)

    (* _t'12 = a->d[1] (limb 1 of the r/a chunk still holds a's limb 1) *)
    forward.

    (* secp256k1_u128_accum_u64(&t, a->d[1]) *)
    forward_call_u128_accum_u64 v_t carry0 (mkUInt64 a1 Ha1) Tsh t1a Ht1a.

    (* _t'11 = b->d[1] *)
    forward.

    (* secp256k1_u128_accum_u64(&t, b->d[1]) *)
    forward_call_u128_accum_u64 v_t t1a (mkUInt64 b1 Hb1) Tsh acc1 Hacc1_raw.
    assert (Hacc1 : u128_val acc1 = (a0 + b0) / 2^64 + a1 + b1).
    { rewrite Hacc1_raw, Ht1a, Hcarry0_val.
      simpl u64_val.
      lia. }
    clear Hacc1_raw Ht1a Hcarry0_val Hcarry0_bnd carry0 t1a.

    (* r->d[1] = secp256k1_u128_to_u64(&t) *)
    forward_call_u128_to_u64 v_t acc1 Tsh lo1 Hlo1.
    forward.

    (* secp256k1_u128_rshift(&t, 64) *)
    forward_call_u128_rshift v_t acc1 Tsh carry1 Hcarry1.
    assert (Hcarry1_val : u128_val carry1 = u128_val acc1 / 2^64) by exact Hcarry1.
    clear Hcarry1.

    (* ===== Round 2: t += a[2] + b[2] ===== *)

    (* _t'10 = a->d[2] *)
    forward.

    (* secp256k1_u128_accum_u64(&t, a->d[2]) *)
    forward_call_u128_accum_u64 v_t carry1 (mkUInt64 a2 Ha2) Tsh t2a Ht2a.

    (* _t'9 = b->d[2] *)
    forward.

    (* secp256k1_u128_accum_u64(&t, b->d[2]) *)
    forward_call_u128_accum_u64 v_t t2a (mkUInt64 b2 Hb2) Tsh acc2 Hacc2_raw.
    assert (Hacc2 : u128_val acc2 = ((a0 + b0) / 2^64 + a1 + b1) / 2^64 + a2 + b2).
    { rewrite Hacc2_raw, Ht2a, Hcarry1_val, Hacc1.
      simpl u64_val.
      lia. }
    clear Hacc2_raw Ht2a Hcarry1_val carry1 t2a.

    (* r->d[2] = secp256k1_u128_to_u64(&t) *)
    forward_call_u128_to_u64 v_t acc2 Tsh lo2 Hlo2.
    forward.

    (* secp256k1_u128_rshift(&t, 64) *)
    forward_call_u128_rshift v_t acc2 Tsh carry2 Hcarry2.
    assert (Hcarry2_val : u128_val carry2 = u128_val acc2 / 2^64) by exact Hcarry2.
    clear Hcarry2.

    (* ===== Round 3: t += a[3] + b[3] ===== *)

    (* _t'8 = a->d[3] *)
    forward.

    (* secp256k1_u128_accum_u64(&t, a->d[3]) *)
    forward_call_u128_accum_u64 v_t carry2 (mkUInt64 a3 Ha3) Tsh t3a Ht3a.

    (* _t'7 = b->d[3] *)
    forward.

    (* secp256k1_u128_accum_u64(&t, b->d[3]) *)
    forward_call_u128_accum_u64 v_t t3a (mkUInt64 b3 Hb3) Tsh acc3 Hacc3_raw.
    assert (Hacc3 : u128_val acc3 =
      (((a0 + b0) / 2^64 + a1 + b1) / 2^64 + a2 + b2) / 2^64 + a3 + b3).
    { rewrite Hacc3_raw, Ht3a, Hcarry2_val, Hacc2.
      simpl u64_val.
      lia. }
    clear Hacc3_raw Ht3a Hcarry2_val carry2 t3a.

    (* r->d[3] = secp256k1_u128_to_u64(&t) *)
    forward_call_u128_to_u64 v_t acc3 Tsh lo3 Hlo3.
    forward.

    (* secp256k1_u128_rshift(&t, 64) *)
    forward_call_u128_rshift v_t acc3 Tsh carry3 Hcarry3.
    assert (Hcarry3_val : u128_val carry3 = u128_val acc3 / 2^64) by exact Hcarry3.
    clear Hcarry3.

    (* _t'5 = secp256k1_u128_to_u64(&t): the carry-out c4 *)
    forward_call_u128_to_u64 v_t carry3 Tsh c4 Hc4.

    (* ===== Stage 1: the ripple result as a [UInt256] [r_u] = (a+b) mod 2^256 ===== *)

    set (S := scalar_val a + scalar_val b).
    assert (HSrange : 0 <= S mod 2^256 < 2^256) by (apply Z.mod_pos_bound; lia).
    pose (r_u := mkUInt256 (S mod 2^256) HSrange).

    (* Carry-chain identity ([scalar_add_ripple_eq]): the ripple accumulators
       telescope to the low 256 bits [rz] and the carry-out [hi]. *)
    pose proof (scalar_add_ripple_eq a b) as Hchain0.
    cbv zeta in Hchain0.
    fold a0 a1 a2 a3 b0 b1 b2 b3 S in Hchain0.
    destruct Hchain0 as [Hchain_eq [Hrz_bnd Hhi_bnd]].

    (* Identify the chain's accumulators with the ripple's. *)
    set (t0 := a0 + b0) in *.
    set (t1 := t0 / 2^64 + a1 + b1) in *.
    set (t2 := t1 / 2^64 + a2 + b2) in *.
    set (t3 := t2 / 2^64 + a3 + b3) in *.
    set (rz := t0 mod 2^64 + t1 mod 2^64 * 2^64
             + t2 mod 2^64 * (2^64*2^64) + t3 mod 2^64 * (2^64*2^64*2^64)) in *.
    set (hi := t3 / 2^64) in *.

    (* [r_u]'s value is the chain's [rz]. *)
    assert (Hru_val : u256_val r_u = rz).
    { simpl u256_val.
      rewrite <- Hchain_eq.
      rewrite Z_mod_plus_full.
      apply Z.mod_small.
      lia. }

    (* The carry-out [c4] read back from [t] is the chain's [hi]. *)
    assert (Hc4_val : u64_val c4 = hi).
    { rewrite Hc4, u128_lo_val, Hcarry3_val, Hacc3.
      fold hi.
      apply Z.mod_small.
      lia. }

    (* ===== Stage 2: re-package the ripple's [data_at] as [u256_at r_ptr r_u] ===== *)

    (* The four stored limbs are exactly [uint256_to_val r_u]; the base of the
       [upd_Znth] tower is [scalar_to_val a] (the in-place chunk) but every
       limb is overwritten, so the base value is irrelevant. *)
    assert (Hbridge :
      (upd_Znth 3
        (upd_Znth 2
          (upd_Znth 1
            (upd_Znth 0 (scalar_to_val a) (uint64_to_val lo0))
            (uint64_to_val lo1)) (uint64_to_val lo2)) (uint64_to_val lo3))
      = uint256_to_val r_u).
    { unfold uint256_to_val, uint64_to_val.
      rewrite Hlo0, Hlo1, Hlo2, Hlo3, Hru_val.
      rewrite !u128_lo_val.
      rewrite Hacc0, Hacc1, Hacc2, Hacc3.
      destruct (scalar_add_store_eq t0 t1 t2 t3 rz eq_refl) as [Hl0 [Hl1 [Hl2 Hl3]]].
      rewrite Hl0, Hl1, Hl2, Hl3.
      reflexivity. }

    (* ===== Stage 3: overflow = c4 + check_overflow(r) ===== *)

    (* _t'6 = secp256k1_scalar_check_overflow(r); the [Hbridge] equality in
       context lets [forward_call] match the stored [data_at] with the
       [u256_at r_ptr r_u] the callee expects. *)
    forward_call (r_ptr, r_u, sh_r).

    (* overflow = (int)(_t'5 + _t'6) *)
    forward.

    (* Both flags are in {0,1}: [cov] = check_overflow, [hi] = the ripple's
       carry-out.  [overflow = hi + cov]. *)
    set (cov := if Z_lt_dec (u256_val r_u) secp256k1_N then 0 else 1).
    assert (Hcov01 : cov = 0 \/ cov = 1) by (subst cov; destruct (Z_lt_dec _ _); auto).
    assert (Hhi01 : hi = 0 \/ hi = 1) by lia.
    assert (Hovf_range : 0 <= u64_val c4 + cov <= 2).
    { rewrite Hc4_val. lia. }

    (* ===== Stage 4: secp256k1_scalar_reduce(r, overflow) ===== *)

    (* secp256k1_scalar_reduce(r, overflow) *)
    forward_call (r_ptr, r_u, u64_val c4 + cov, sh_r).
    { (* match the integer argument [(tint)(_t'5 + _t'6)] *)
      entailer!. }
    Intros r'.
    rename H into Hr'.

    (* The two model facts of the add, from [scalar_add_flag_reduce_eq]. *)
    assert (HNbnd : 0 < secp256k1_N < 2^256) by (unfold secp256k1_N; lia).
    assert (HSlt2N : 0 <= S < 2 * secp256k1_N).
    { subst S.
      pose proof (scalar_range a).
      pose proof (scalar_range b).
      lia. }
    assert (Hcov_rz : cov = if Z_lt_dec rz secp256k1_N then 0 else 1)
      by (subst cov; rewrite Hru_val; reflexivity).
    destruct (scalar_add_flag_reduce_eq secp256k1_N S rz hi cov
      HNbnd HSlt2N Hhi01 Hchain_eq Hrz_bnd Hcov_rz) as [Hflag Hvaleq].

    (* ===== Stage 5: postcondition ===== *)

    (* return overflow *)
    forward.

    (* [entailer!] discharges the RETURN-flag equation using [Hflag] (the
       returned value is [hi + cov]) and cancels the untouched [b] chunk; the
       residual is the stored scalar. *)
    Exists (scalar_add a b).
    entailer!.

    (* The stored scalar equals [scalar_add a b]: reduce to the value
       equality [Hvaleq].  The preceding [entailer!] unfolded the [cov]
       abbreviation in the residual goal, so re-[set] it [in *] to re-fold
       those occurrences before rewriting with [Hvaleq] (which mentions
       [cov]). *)
    apply derives_refl'.
    f_equal.
    set (cov := if Z_lt_dec (u256_val r_u) secp256k1_N then 0 else 1) in *.
    unfold scalar_to_val, uint256_to_val.
    rewrite Hr'.
    rewrite Hru_val, Hc4_val.
    simpl scalar_val.
    rewrite Hvaleq.
    reflexivity.

  (* ===== branch: alias = false -- add(r, a, b) with r, a, b distinct chunks ===== *)
  - specialize (H0 eq_refl).
    clear H.
    rename SH into Hsh_r.
    rename SH0 into Hsh_b.
    rename H0 into Hsh_a.

    (* Flatten the distinct-chunk SEP conjunction
       [data_at_ r * scalar_at a * scalar_at b]. *)
    Intros.

    (* ===== Stage 0: name the input limbs and their ranges ===== *)

    set (a0 := limb (2^64) (scalar_val a) 0).
    set (a1 := limb (2^64) (scalar_val a) 1).
    set (a2 := limb (2^64) (scalar_val a) 2).
    set (a3 := limb (2^64) (scalar_val a) 3).
    set (b0 := limb (2^64) (scalar_val b) 0).
    set (b1 := limb (2^64) (scalar_val b) 1).
    set (b2 := limb (2^64) (scalar_val b) 2).
    set (b3 := limb (2^64) (scalar_val b) 3).

    assert (Ha0 : 0 <= a0 < 2^64) by (subst a0; apply Z.mod_pos_bound; lia).
    assert (Ha1 : 0 <= a1 < 2^64) by (subst a1; apply Z.mod_pos_bound; lia).
    assert (Ha2 : 0 <= a2 < 2^64) by (subst a2; apply Z.mod_pos_bound; lia).
    assert (Ha3 : 0 <= a3 < 2^64) by (subst a3; apply Z.mod_pos_bound; lia).
    assert (Hb0 : 0 <= b0 < 2^64) by (subst b0; apply Z.mod_pos_bound; lia).
    assert (Hb1 : 0 <= b1 < 2^64) by (subst b1; apply Z.mod_pos_bound; lia).
    assert (Hb2 : 0 <= b2 < 2^64) by (subst b2; apply Z.mod_pos_bound; lia).
    assert (Hb3 : 0 <= b3 < 2^64) by (subst b3; apply Z.mod_pos_bound; lia).

    (* ===== Round 0: t = a[0] + b[0] ===== *)

    (* _t'14 = a->d[0] *)
    forward.

    (* secp256k1_u128_from_u64(&t, a->d[0]) *)
    forward_call_u128_from_u64 v_t (mkUInt64 a0 Ha0) Tsh t_init Ht_init.
    { entailer!.
      subst a0.
      unfold scalar_to_val, Znth.
      simpl.
      rewrite limb_fold0.
      reflexivity. }

    (* _t'13 = b->d[0] *)
    forward.

    (* secp256k1_u128_accum_u64(&t, b->d[0]) *)
    forward_call_u128_accum_u64 v_t t_init (mkUInt64 b0 Hb0) Tsh acc0 Hacc0_raw.
    { entailer!.
      subst b0.
      unfold scalar_to_val, Znth.
      simpl.
      rewrite limb_fold0.
      reflexivity. }
    assert (Hacc0 : u128_val acc0 = a0 + b0)
      by (rewrite Hacc0_raw, Ht_init; reflexivity).
    clear Ht_init Hacc0_raw t_init.

    (* r->d[0] = secp256k1_u128_to_u64(&t) *)
    forward_call_u128_to_u64 v_t acc0 Tsh lo0 Hlo0.
    forward.

    (* secp256k1_u128_rshift(&t, 64) *)
    forward_call_u128_rshift v_t acc0 Tsh carry0 Hcarry0.
    assert (Hcarry0_val : u128_val carry0 = (a0 + b0) / 2^64)
      by (rewrite Hcarry0, Hacc0; reflexivity).
    clear Hcarry0.

    (* The round-0 carry is a bit ([scalar_add_carry_bnd]); with it in context
       the wrapper discharges the [< 2^128] precondition of both round-1
       accumulate calls. *)
    pose proof (scalar_add_carry_bnd a0 b0 Ha0 Hb0) as Hcarry0_bnd.

    (* ===== Round 1: t += a[1] + b[1] ===== *)

    (* _t'12 = a->d[1] *)
    forward.

    (* secp256k1_u128_accum_u64(&t, a->d[1]) *)
    forward_call_u128_accum_u64 v_t carry0 (mkUInt64 a1 Ha1) Tsh t1a Ht1a.

    (* _t'11 = b->d[1] *)
    forward.

    (* secp256k1_u128_accum_u64(&t, b->d[1]) *)
    forward_call_u128_accum_u64 v_t t1a (mkUInt64 b1 Hb1) Tsh acc1 Hacc1_raw.
    assert (Hacc1 : u128_val acc1 = (a0 + b0) / 2^64 + a1 + b1).
    { rewrite Hacc1_raw, Ht1a, Hcarry0_val.
      simpl u64_val.
      lia. }
    clear Hacc1_raw Ht1a Hcarry0_val Hcarry0_bnd carry0 t1a.

    (* r->d[1] = secp256k1_u128_to_u64(&t) *)
    forward_call_u128_to_u64 v_t acc1 Tsh lo1 Hlo1.
    forward.

    (* secp256k1_u128_rshift(&t, 64) *)
    forward_call_u128_rshift v_t acc1 Tsh carry1 Hcarry1.
    assert (Hcarry1_val : u128_val carry1 = u128_val acc1 / 2^64) by exact Hcarry1.
    clear Hcarry1.

    (* ===== Round 2: t += a[2] + b[2] ===== *)

    (* _t'10 = a->d[2] *)
    forward.

    (* secp256k1_u128_accum_u64(&t, a->d[2]) *)
    forward_call_u128_accum_u64 v_t carry1 (mkUInt64 a2 Ha2) Tsh t2a Ht2a.

    (* _t'9 = b->d[2] *)
    forward.

    (* secp256k1_u128_accum_u64(&t, b->d[2]) *)
    forward_call_u128_accum_u64 v_t t2a (mkUInt64 b2 Hb2) Tsh acc2 Hacc2_raw.
    assert (Hacc2 : u128_val acc2 = ((a0 + b0) / 2^64 + a1 + b1) / 2^64 + a2 + b2).
    { rewrite Hacc2_raw, Ht2a, Hcarry1_val, Hacc1.
      simpl u64_val.
      lia. }
    clear Hacc2_raw Ht2a Hcarry1_val carry1 t2a.

    (* r->d[2] = secp256k1_u128_to_u64(&t) *)
    forward_call_u128_to_u64 v_t acc2 Tsh lo2 Hlo2.
    forward.

    (* secp256k1_u128_rshift(&t, 64) *)
    forward_call_u128_rshift v_t acc2 Tsh carry2 Hcarry2.
    assert (Hcarry2_val : u128_val carry2 = u128_val acc2 / 2^64) by exact Hcarry2.
    clear Hcarry2.

    (* ===== Round 3: t += a[3] + b[3] ===== *)

    (* _t'8 = a->d[3] *)
    forward.

    (* secp256k1_u128_accum_u64(&t, a->d[3]) *)
    forward_call_u128_accum_u64 v_t carry2 (mkUInt64 a3 Ha3) Tsh t3a Ht3a.

    (* _t'7 = b->d[3] *)
    forward.

    (* secp256k1_u128_accum_u64(&t, b->d[3]) *)
    forward_call_u128_accum_u64 v_t t3a (mkUInt64 b3 Hb3) Tsh acc3 Hacc3_raw.
    assert (Hacc3 : u128_val acc3 =
      (((a0 + b0) / 2^64 + a1 + b1) / 2^64 + a2 + b2) / 2^64 + a3 + b3).
    { rewrite Hacc3_raw, Ht3a, Hcarry2_val, Hacc2.
      simpl u64_val.
      lia. }
    clear Hacc3_raw Ht3a Hcarry2_val carry2 t3a.

    (* r->d[3] = secp256k1_u128_to_u64(&t) *)
    forward_call_u128_to_u64 v_t acc3 Tsh lo3 Hlo3.
    forward.

    (* secp256k1_u128_rshift(&t, 64) *)
    forward_call_u128_rshift v_t acc3 Tsh carry3 Hcarry3.
    assert (Hcarry3_val : u128_val carry3 = u128_val acc3 / 2^64) by exact Hcarry3.
    clear Hcarry3.

    (* _t'5 = secp256k1_u128_to_u64(&t): the carry-out c4 *)
    forward_call_u128_to_u64 v_t carry3 Tsh c4 Hc4.

    (* ===== Stage 1: the ripple result as a [UInt256] [r_u] = (a+b) mod 2^256 ===== *)

    set (S := scalar_val a + scalar_val b).
    assert (HSrange : 0 <= S mod 2^256 < 2^256) by (apply Z.mod_pos_bound; lia).
    pose (r_u := mkUInt256 (S mod 2^256) HSrange).

    (* Carry-chain identity ([scalar_add_ripple_eq]): the ripple accumulators
       telescope to the low 256 bits [rz] and the carry-out [hi]. *)
    pose proof (scalar_add_ripple_eq a b) as Hchain0.
    cbv zeta in Hchain0.
    fold a0 a1 a2 a3 b0 b1 b2 b3 S in Hchain0.
    destruct Hchain0 as [Hchain_eq [Hrz_bnd Hhi_bnd]].

    (* Identify the chain's accumulators with the ripple's. *)
    set (t0 := a0 + b0) in *.
    set (t1 := t0 / 2^64 + a1 + b1) in *.
    set (t2 := t1 / 2^64 + a2 + b2) in *.
    set (t3 := t2 / 2^64 + a3 + b3) in *.
    set (rz := t0 mod 2^64 + t1 mod 2^64 * 2^64
             + t2 mod 2^64 * (2^64*2^64) + t3 mod 2^64 * (2^64*2^64*2^64)) in *.
    set (hi := t3 / 2^64) in *.

    (* [r_u]'s value is the chain's [rz]. *)
    assert (Hru_val : u256_val r_u = rz).
    { simpl u256_val.
      rewrite <- Hchain_eq.
      rewrite Z_mod_plus_full.
      apply Z.mod_small.
      lia. }

    (* The carry-out [c4] read back from [t] is the chain's [hi]. *)
    assert (Hc4_val : u64_val c4 = hi).
    { rewrite Hc4, u128_lo_val, Hcarry3_val, Hacc3.
      fold hi.
      apply Z.mod_small.
      lia. }

    (* ===== Stage 2: re-package the ripple's [data_at] as [u256_at r_ptr r_u] ===== *)

    (* The four stored limbs are exactly [uint256_to_val r_u]. *)
    assert (Hbridge :
      (upd_Znth 3
        (upd_Znth 2
          (upd_Znth 1
            (upd_Znth 0 (default_val t_secp256k1_scalar) (uint64_to_val lo0))
            (uint64_to_val lo1)) (uint64_to_val lo2)) (uint64_to_val lo3))
      = uint256_to_val r_u).
    { unfold uint256_to_val, uint64_to_val.
      rewrite Hlo0, Hlo1, Hlo2, Hlo3, Hru_val.
      rewrite !u128_lo_val.
      rewrite Hacc0, Hacc1, Hacc2, Hacc3.
      destruct (scalar_add_store_eq t0 t1 t2 t3 rz eq_refl) as [Hl0 [Hl1 [Hl2 Hl3]]].
      rewrite Hl0, Hl1, Hl2, Hl3.
      reflexivity. }

    (* ===== Stage 3: overflow = c4 + check_overflow(r) ===== *)

    (* _t'6 = secp256k1_scalar_check_overflow(r); the [Hbridge] equality in
       context lets [forward_call] match the stored [data_at] with the
       [u256_at r_ptr r_u] the callee expects. *)
    forward_call (r_ptr, r_u, sh_r).

    (* overflow = (int)(_t'5 + _t'6) *)
    forward.

    (* Both flags are in {0,1}: [cov] = check_overflow, [hi] = the ripple's
       carry-out.  [overflow = hi + cov]. *)
    set (cov := if Z_lt_dec (u256_val r_u) secp256k1_N then 0 else 1).
    assert (Hcov01 : cov = 0 \/ cov = 1) by (subst cov; destruct (Z_lt_dec _ _); auto).
    assert (Hhi01 : hi = 0 \/ hi = 1) by lia.
    assert (Hovf_range : 0 <= u64_val c4 + cov <= 2).
    { rewrite Hc4_val. lia. }

    (* ===== Stage 4: secp256k1_scalar_reduce(r, overflow) ===== *)

    (* secp256k1_scalar_reduce(r, overflow) *)
    forward_call (r_ptr, r_u, u64_val c4 + cov, sh_r).
    { (* match the integer argument [(tint)(_t'5 + _t'6)] *)
      entailer!. }
    Intros r'.
    rename H into Hr'.

    (* The two model facts of the add, from [scalar_add_flag_reduce_eq]. *)
    assert (HNbnd : 0 < secp256k1_N < 2^256) by (unfold secp256k1_N; lia).
    assert (HSlt2N : 0 <= S < 2 * secp256k1_N).
    { subst S.
      pose proof (scalar_range a).
      pose proof (scalar_range b).
      lia. }
    assert (Hcov_rz : cov = if Z_lt_dec rz secp256k1_N then 0 else 1)
      by (subst cov; rewrite Hru_val; reflexivity).
    destruct (scalar_add_flag_reduce_eq secp256k1_N S rz hi cov
      HNbnd HSlt2N Hhi01 Hchain_eq Hrz_bnd Hcov_rz) as [Hflag Hvaleq].

    (* ===== Stage 5: postcondition ===== *)

    (* return overflow *)
    forward.

    (* [entailer!] discharges the RETURN-flag equation using [Hflag] (the
       returned value is [hi + cov]); the residual is the stored scalar. *)
    Exists (scalar_add a b).
    entailer!.

    (* The stored scalar equals [scalar_add a b]: reduce to the value
       equality [Hvaleq].  The preceding [entailer!] unfolded the [cov]
       abbreviation in the residual goal, so re-[set] it [in *] to re-fold
       those occurrences before rewriting with [Hvaleq] (which mentions
       [cov]). *)
    apply derives_refl'.
    f_equal.
    set (cov := if Z_lt_dec (u256_val r_u) secp256k1_N then 0 else 1) in *.
    unfold scalar_to_val, uint256_to_val.
    rewrite Hr'.
    rewrite Hru_val, Hc4_val.
    simpl scalar_val.
    rewrite Hvaleq.
    reflexivity.
Qed.
