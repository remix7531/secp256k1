(** * Verif_scalar_negate: Proof of body_secp256k1_scalar_negate *)
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
(** ** Stage lemmas -- the mask, the limb split, and the ripple chain. *)

(** The four-constant ripple-add carry chain [theory.arithmetic.add4_carry_chain]
    (each limb, including limb 3, gets a per-limb addend [c_i], unlike the
    three-constant [reduce_carry_chain]) is the workhorse here; it is shared
    with [scalar_add] and [scalar_half].  The bitwise-not-as-arithmetic identity
    [~x = 2^64 - 1 - x] is the shared [vst.integers.Int64_not_repr_complement],
    and the [nonzero] mask value is the shared
    [vst.integers.Int64_neg1_mul_b2z_eq].

    The body proof below runs the same five stages twice, once per aliasing
    mode; every stage whose content does not depend on the VST proof state
    (the limb split, the pure-Z ripple chain) is stated once here and applied
    from both branches. *)

(** Round 1: the carry out of round 0 is a single bit -- [~a[0] + (N_0 + 1)]
    is a sum of two values below [2^64]. *)
Lemma scalar_negate_carry0_bnd (a0 : Z) :
  0 <= a0 < 2^64 ->
  0 <= (2^64 - 1 - a0 + (N_0 + 1)) / 2^64 <= 1.
Proof.
  intros Ha0.
  assert (HN0 : 0 <= N_0 < 2^64) by (unfold N_0; lia).

  assert (Hlo : 0 <= (2^64 - 1 - a0 + (N_0 + 1)) / 2^64) by (apply Z.div_pos; lia).
  assert (Hhi : (2^64 - 1 - a0 + (N_0 + 1)) / 2^64 < 2)
    by (apply Z.div_lt_upper_bound; lia).
  lia.
Qed.

(** Stage 4, branch [a = 0]: [negate 0 = 0], whose four C limbs are all zero --
    the value the masked stores leave in [r]. *)
Lemma scalar_negate_zero_limbs_eq (a : Scalar) :
  scalar_val a = 0 ->
  scalar_to_val (scalar_negate a)
  = [Vlong Int64.zero; Vlong Int64.zero; Vlong Int64.zero; Vlong Int64.zero].
Proof.
  intros Ha.

  assert (Hneg0 : scalar_val (scalar_negate a) = 0).
  { unfold scalar_negate.
    simpl.
    rewrite Ha.
    rewrite Z.sub_0_r.
    apply Z_mod_same_full. }

  unfold scalar_to_val.
  rewrite Hneg0.
  change (0 mod 2^64) with 0.
  change (0 / 2^64 mod 2^64) with 0.
  change (0 / 2^128 mod 2^64) with 0.
  change (0 / 2^192 mod 2^64) with 0.
  reflexivity.
Qed.

(** Stage 4, branch [a <> 0]: the modular negation is the plain difference
    [n - a], since [0 < a < n] leaves the reduction inert. *)
Lemma scalar_negate_val_eq (a : Scalar) :
  scalar_val a <> 0 ->
  scalar_val (scalar_negate a) = secp256k1_N - scalar_val a.
Proof.
  intros Ha.
  pose proof (scalar_range a) as Harange.

  unfold scalar_negate.
  simpl.
  rewrite Z.mod_small by lia.
  reflexivity.
Qed.

(** Stage 5: a scalar is the little-endian recombination of its four 64-bit
    limbs -- [eval4_limbs] at [B = 2^64], available because a scalar is below
    [n < 2^256]. *)
Lemma scalar_negate_limbs_eval_eq (a : Scalar) :
  limb (2^64) (scalar_val a) 0
  + limb (2^64) (scalar_val a) 1 * 2^64
  + limb (2^64) (scalar_val a) 2 * (2^64)^2
  + limb (2^64) (scalar_val a) 3 * (2^64)^3
  = scalar_val a.
Proof.
  pose proof (scalar_range a) as Harange.

  (* Main: the reconstruction lemma, with [eval4] spelled out. *)
  pose proof (eval4_limbs (2^64) (scalar_val a) ltac:(lia)) as E.
  unfold eval4 in E.
  apply E.

  (* Closeout: a scalar is below [n], hence below [(2^64)^4]. *)
  change ((2^64)^4) with (2^256).
  unfold secp256k1_N in Harange.
  lia.
Qed.

(** Stage 5: the accumulator chain [t_0 .. t_3] of the four rounds -- round [i]
    adds the complement [~a[i]] and the constant limb [i] of [n + 1] to the
    carry of round [i-1] -- reconstructs exactly [n - av].

    Strategy: [add4_carry_chain] equates the four extracted limbs plus the
    final carry with [(2^256 - 1 - av) + (n + 1)].  That sum lies in
    [[2^256, 2 * 2^256)] whenever [0 < av < n], so the carry-out is [1] and
    the four extracted limbs carry the remaining [n - av]. *)
Lemma scalar_negate_chain_eval_eq :
  forall a0 a1 a2 a3 av : Z,
    0 <= a0 < 2^64 ->
    0 <= a1 < 2^64 ->
    0 <= a2 < 2^64 ->
    0 <= a3 < 2^64 ->
    0 < av < secp256k1_N ->
    a0 + a1 * 2^64 + a2 * (2^64)^2 + a3 * (2^64)^3 = av ->
    let t0 := 2^64 - 1 - a0 + (N_0 + 1) in
    let t1 := t0 / 2^64 + (2^64 - 1 - a1) + N_1 in
    let t2 := t1 / 2^64 + (2^64 - 1 - a2) + N_2 in
    let t3 := t2 / 2^64 + (2^64 - 1 - a3) + N_3 in
    eval4 (2^64) (t0 mod 2^64) (t1 mod 2^64) (t2 mod 2^64) (t3 mod 2^64)
    = secp256k1_N - av.
Proof.
  intros a0 a1 a2 a3 av Ha0r Ha1r Ha2r Ha3r Havr Hadecomp.
  cbv zeta.

  (* Setup: the complemented limbs evaluate to [2^256 - 1 - av], the
     constant limbs to [n + 1]. *)
  assert (Hval : eval4 (2^64) (2^64 - 1 - a0) (2^64 - 1 - a1)
                   (2^64 - 1 - a2) (2^64 - 1 - a3) = 2^256 - 1 - av).
  { unfold eval4.
    rewrite <- Hadecomp.
    ring. }

  assert (HC : eval4 (2^64) (N_0 + 1) N_1 N_2 N_3 = secp256k1_N + 1).
  { unfold eval4.
    rewrite secp256k1_N_limbs.
    ring. }

  (* Main: the four-constant ripple identity, instantiated at [B = 2^64]. *)
  pose proof (add4_carry_chain (2^64)
    (2^64 - 1 - a0) (2^64 - 1 - a1) (2^64 - 1 - a2) (2^64 - 1 - a3)
    (N_0 + 1) N_1 N_2 N_3
    ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)
    ltac:(unfold N_0; lia) ltac:(unfold N_1; lia)
    ltac:(unfold N_2; lia) ltac:(unfold N_3; lia)) as Hchain.
  cbv zeta in Hchain.
  rewrite Hval, HC in Hchain.

  assert (Hbnd : 0 <= 2^256 - 1 - av + (secp256k1_N + 1)
                 < 2 * (2^64 * 2^64 * 2^64 * 2^64)).
  { unfold secp256k1_N in *.
    lia. }

  destruct (Hchain Hbnd) as [Heq [Hrz_bnd Hhi_bnd]].

  (* Closeout: the sum reaches past [2^256], so the carry-out is [1] and the
     four limbs are left holding [n - av]. *)
  assert (HB4 : 2^64 * 2^64 * 2^64 * 2^64 = 2^256) by reflexivity.
  rewrite HB4 in Heq, Hrz_bnd.
  unfold secp256k1_N in *.
  lia.
Qed.

(** Stage 5: consequently limb [i] of the chain is limb [i] of [n - av] -- the
    four pure-Z equalities the postcondition's [scalar_to_val] needs.
    [limbs_eval4] inverts the recombination of the previous lemma. *)
Lemma scalar_negate_chain_limbs_eq :
  forall a0 a1 a2 a3 av : Z,
    0 <= a0 < 2^64 ->
    0 <= a1 < 2^64 ->
    0 <= a2 < 2^64 ->
    0 <= a3 < 2^64 ->
    0 < av < secp256k1_N ->
    a0 + a1 * 2^64 + a2 * (2^64)^2 + a3 * (2^64)^3 = av ->
    let t0 := 2^64 - 1 - a0 + (N_0 + 1) in
    let t1 := t0 / 2^64 + (2^64 - 1 - a1) + N_1 in
    let t2 := t1 / 2^64 + (2^64 - 1 - a2) + N_2 in
    let t3 := t2 / 2^64 + (2^64 - 1 - a3) + N_3 in
    t0 mod 2^64 = (secp256k1_N - av) mod 2^64 /\
    t1 mod 2^64 = (secp256k1_N - av) / 2^64 mod 2^64 /\
    t2 mod 2^64 = (secp256k1_N - av) / 2^128 mod 2^64 /\
    t3 mod 2^64 = (secp256k1_N - av) / 2^192 mod 2^64.
Proof.
  intros a0 a1 a2 a3 av Ha0r Ha1r Ha2r Ha3r Havr Hadecomp.
  cbv zeta.

  (* Setup: the chain reconstructs [n - av]; name its four accumulators. *)
  pose proof (scalar_negate_chain_eval_eq a0 a1 a2 a3 av
    Ha0r Ha1r Ha2r Ha3r Havr Hadecomp) as Hrz.
  cbv zeta in Hrz.
  set (t0 := 2^64 - 1 - a0 + (N_0 + 1)) in *.
  set (t1 := t0 / 2^64 + (2^64 - 1 - a1) + N_1) in *.
  set (t2 := t1 / 2^64 + (2^64 - 1 - a2) + N_2) in *.
  set (t3 := t2 / 2^64 + (2^64 - 1 - a3) + N_3) in *.

  (* Main: read the four limbs back off the reconstructed value. *)
  pose proof (limbs_eval4 (2^64) (t0 mod 2^64) (t1 mod 2^64) (t2 mod 2^64) (t3 mod 2^64)
    ltac:(lia)
    ltac:(apply Z.mod_pos_bound; lia)
    ltac:(apply Z.mod_pos_bound; lia)
    ltac:(apply Z.mod_pos_bound; lia)
    ltac:(apply Z.mod_pos_bound; lia)) as [Hl0 [Hl1 [Hl2 Hl3]]].
  rewrite Hrz in Hl0, Hl1, Hl2, Hl3.

  (* Closeout: normalise the [limb] exponents to the C limb offsets. *)
  unfold limb in Hl0, Hl1, Hl2, Hl3.
  simpl Z.of_nat in Hl0, Hl1, Hl2, Hl3.
  rewrite Z.pow_0_r, Z.div_1_r in Hl0.
  rewrite Z.pow_1_r in Hl1.
  replace ((2^64)^2) with (2^128) in Hl2 by reflexivity.
  replace ((2^64)^3) with (2^192) in Hl3 by reflexivity.

  repeat split.
  - (* conjunct 0: limb 0 of the chain *)
    exact (eq_sym Hl0).
  - (* conjunct 1: limb 1 of the chain *)
    exact (eq_sym Hl1).
  - (* conjunct 2: limb 2 of the chain *)
    exact (eq_sym Hl2).
  - (* conjunct 3: limb 3 of the chain *)
    exact (eq_sym Hl3).
Qed.

(* ================================================================= *)
(** ** secp256k1_scalar_negate -- [(N - a) mod N]. *)

Lemma body_secp256k1_scalar_negate:
  semax_body Vprog Gprog
    f_secp256k1_scalar_negate spec_secp256k1_scalar_negate.
Proof.
  start_function.

  destruct alias.

  (* branch: alias = true -- in-place negate(r, r), so r_ptr = a_ptr. *)
  (* One writable chunk at [r_ptr] holds [a]; each round reads [a->d[i]]
     before the store to [r->d[i]] overwrites it, and earlier rounds only
     wrote limbs [0..i-1], so each load still sees [a]'s original limb. *)
  - specialize (H eq_refl).
    subst a_ptr.
    clear H0.
    rename SH into Hsh_r.

    (* ===== Stage 0: nonzero = is_zero(a) ? 0 : -1 ===== *)

    (* _t'1 = secp256k1_scalar_is_zero(a) -- reads the shared chunk *)
    forward_call (r_ptr, a, sh_r).

    (* nonzero = (-1) * (_t'1 == 0) *)
    forward.

    (* Name the mask value [nz] and characterise it by the zero test. *)
    set (nz := Int64.mul (Int64.repr (-1))
      (Int64.repr
         (Int.signed
            (Int.repr
               (Z.b2z
                  (Int.eq (Int.repr (if Z.eq_dec a 0 then 1 else 0))
                     (Int.repr 0))))))) in *.
    assert (Hnz : nz = if Z.eq_dec (scalar_val a) 0 then Int64.zero else Int64.mone)
      by (subst nz; apply Int64_neg1_mul_b2z_eq).
    clearbody nz.

    (* The four 64-bit limbs of [a]. *)
    set (a0 := limb (2^64) (scalar_val a) 0).
    set (a1 := limb (2^64) (scalar_val a) 1).
    set (a2 := limb (2^64) (scalar_val a) 2).
    set (a3 := limb (2^64) (scalar_val a) 3).

    (* The per-round complement and constant ranges. *)
    assert (Ha0r : 0 <= a0 < 2^64) by (subst a0; apply Z.mod_pos_bound; lia).
    assert (Ha1r : 0 <= a1 < 2^64) by (subst a1; apply Z.mod_pos_bound; lia).
    assert (Ha2r : 0 <= a2 < 2^64) by (subst a2; apply Z.mod_pos_bound; lia).
    assert (Ha3r : 0 <= a3 < 2^64) by (subst a3; apply Z.mod_pos_bound; lia).
    assert (Hd0r : 0 <= 2^64 - 1 - a0 < 2^64) by lia.
    assert (Hd1r : 0 <= 2^64 - 1 - a1 < 2^64) by lia.
    assert (Hd2r : 0 <= 2^64 - 1 - a2 < 2^64) by lia.
    assert (Hd3r : 0 <= 2^64 - 1 - a3 < 2^64) by lia.
    assert (Hc0r : 0 <= N_0 + 1 < 2^64) by (unfold N_0; lia).
    assert (Hc1r : 0 <= N_1 < 2^64) by (unfold N_1; lia).
    assert (Hc2r : 0 <= N_2 < 2^64) by (unfold N_2; lia).
    assert (Hc3r : 0 <= N_3 < 2^64) by (unfold N_3; lia).

    (* ===== Round 0: t = ~a[0] + (N_0 + 1) ===== *)

    (* _t'9 = a->d[0] *)
    forward.

    (* secp256k1_u128_from_u64(&t, ~a->d[0]) *)
    forward_call_u128_from_u64 v_t (mkUInt64 (2^64 - 1 - a0) Hd0r) Tsh t_init Ht_init.
    { entailer!.
      simpl.
      unfold uint64_to_val.
      simpl.
      do 2 f_equal.
      change (Z.pow_pos 2 64) with (2^64).
      assert (Ha0e : a0 = a mod 2^64).
      { subst a0.
        unfold limb.
        simpl Z.of_nat.
        rewrite Z.pow_0_r, Z.div_1_r.
        reflexivity. }
      rewrite Int64_not_repr_complement by (apply Z.mod_pos_bound; lia).
      rewrite Ha0e.
      reflexivity. }

    (* secp256k1_u128_accum_u64(&t, N_0 + 1) *)
    forward_call_u128_accum_u64 v_t t_init (mkUInt64 (N_0 + 1) Hc0r) Tsh acc0 Hacc0_raw.
    assert (Hacc0 : u128_val acc0 = (2^64 - 1 - a0) + (N_0 + 1))
      by (rewrite Hacc0_raw, Ht_init; reflexivity).
    clear Ht_init Hacc0_raw t_init.

    (* lo0 = secp256k1_u128_to_u64(&t) *)
    forward_call_u128_to_u64 v_t acc0 Tsh lo0 Hlo0.
    (* r->d[0] = lo0 & nonzero *)
    forward.

    (* secp256k1_u128_rshift(&t, 64) *)
    forward_call_u128_rshift v_t acc0 Tsh carry0 Hcarry0.
    assert (Hcarry0_val : u128_val carry0 = ((2^64 - 1 - a0) + (N_0 + 1)) / 2^64)
      by (rewrite Hcarry0, Hacc0; reflexivity).
    clear Hcarry0.

    (* The round-0 carry is a bit ([scalar_negate_carry0_bnd]); with it in
       context the wrapper discharges the [< 2^128] precondition of both
       round-1 accumulate calls. *)
    pose proof (scalar_negate_carry0_bnd a0 Ha0r) as Hcarry0_bnd.

    (* ===== Round 1: t += ~a[1] + N_1 ===== *)

    (* _t'8 = a->d[1] -- still reads [a]'s limb 1 (only limb 0 was written) *)
    forward.

    (* secp256k1_u128_accum_u64(&t, ~a->d[1]) *)
    forward_call_u128_accum_u64 v_t carry0 (mkUInt64 (2^64 - 1 - a1) Hd1r) Tsh t1a Ht1a.
    (* The loaded value is [Znth 1 (upd_Znth 0 ...)]; peel back to [a]'s limb. *)
    rewrite Znth_upd_Znth_diff by lia.
    { entailer!.
      simpl.
      unfold uint64_to_val.
      do 2 f_equal.
      change (Z.pow_pos 2 64) with (2^64).
      rewrite Int64_not_repr_complement by (apply Z.mod_pos_bound; lia).
      f_equal. }

    (* secp256k1_u128_accum_u64(&t, N_1) *)
    forward_call_u128_accum_u64 v_t t1a (mkUInt64 N_1 Hc1r) Tsh acc1 Hacc1_raw.
    { entailer!.
      simpl.
      unfold uint64_to_val.
      do 2 f_equal.
      f_equal.
      apply Int64.same_if_eq.
      vm_compute.
      reflexivity. }

    assert (Hacc1 : u128_val acc1 = ((2^64 - 1 - a0) + (N_0 + 1)) / 2^64 + (2^64 - 1 - a1) + N_1).
    { rewrite Hacc1_raw, Ht1a, Hcarry0_val.
      simpl u64_val.
      lia. }

    clear Hacc1_raw Ht1a Hcarry0_val Hcarry0_bnd carry0 t1a.

    (* lo1 = secp256k1_u128_to_u64(&t) *)
    forward_call_u128_to_u64 v_t acc1 Tsh lo1 Hlo1.
    (* r->d[1] = lo1 & nonzero *)
    forward.

    (* secp256k1_u128_rshift(&t, 64) *)
    forward_call_u128_rshift v_t acc1 Tsh carry1 Hcarry1.
    assert (Hcarry1_val : u128_val carry1 = u128_val acc1 / 2^64) by exact Hcarry1.
    clear Hcarry1.

    (* ===== Round 2: t += ~a[2] + N_2 ===== *)

    (* _t'7 = a->d[2] -- still reads [a]'s limb 2 (limbs 0,1 were written) *)
    forward.

    (* secp256k1_u128_accum_u64(&t, ~a->d[2]) *)
    forward_call_u128_accum_u64 v_t carry1 (mkUInt64 (2^64 - 1 - a2) Hd2r) Tsh t2a Ht2a.
    (* Peel back [Znth 2] past the two earlier [upd_Znth] writes. *)
    rewrite !Znth_upd_Znth_diff by lia.
    { entailer!.
      simpl.
      unfold uint64_to_val.
      do 2 f_equal.
      change (Z.pow_pos 2 64) with (2^64).
      rewrite Int64_not_repr_complement by (apply Z.mod_pos_bound; lia).
      f_equal. }

    (* secp256k1_u128_accum_u64(&t, N_2) *)
    forward_call_u128_accum_u64 v_t t2a (mkUInt64 N_2 Hc2r) Tsh acc2 Hacc2_raw.
    { entailer!.
      simpl.
      unfold uint64_to_val.
      do 2 f_equal.
      f_equal.
      apply Int64.same_if_eq.
      vm_compute.
      reflexivity. }

    assert (Hacc2 : u128_val acc2 =
      ((2^64 - 1 - a0 + (N_0 + 1)) / 2^64 + (2^64 - 1 - a1) + N_1) / 2^64 + (2^64 - 1 - a2) + N_2).
    { rewrite Hacc2_raw, Ht2a, Hcarry1_val, Hacc1.
      simpl u64_val.
      lia. }

    clear Hacc2_raw Ht2a Hcarry1_val carry1 t2a.

    (* lo2 = secp256k1_u128_to_u64(&t) *)
    forward_call_u128_to_u64 v_t acc2 Tsh lo2 Hlo2.
    (* r->d[2] = lo2 & nonzero *)
    forward.

    (* secp256k1_u128_rshift(&t, 64) *)
    forward_call_u128_rshift v_t acc2 Tsh carry2 Hcarry2.
    assert (Hcarry2_val : u128_val carry2 = u128_val acc2 / 2^64) by exact Hcarry2.
    clear Hcarry2.

    (* ===== Round 3: t += ~a[3] + N_3 ===== *)

    (* _t'6 = a->d[3] -- still reads [a]'s limb 3 (limbs 0,1,2 were written) *)
    forward.

    (* secp256k1_u128_accum_u64(&t, ~a->d[3]) *)
    forward_call_u128_accum_u64 v_t carry2 (mkUInt64 (2^64 - 1 - a3) Hd3r) Tsh t3a Ht3a.
    (* Peel back [Znth 3] past the three earlier [upd_Znth] writes. *)
    rewrite !Znth_upd_Znth_diff by lia.
    { entailer!.
      simpl.
      unfold uint64_to_val.
      do 2 f_equal.
      change (Z.pow_pos 2 64) with (2^64).
      rewrite Int64_not_repr_complement by (apply Z.mod_pos_bound; lia).
      f_equal. }

    (* secp256k1_u128_accum_u64(&t, N_3) *)
    forward_call_u128_accum_u64 v_t t3a (mkUInt64 N_3 Hc3r) Tsh acc3 Hacc3_raw.
    { entailer!.
      simpl.
      unfold uint64_to_val.
      do 2 f_equal.
      f_equal.
      apply Int64.same_if_eq.
      vm_compute.
      reflexivity. }

    assert (Hacc3 : u128_val acc3 =
      (((2^64 - 1 - a0 + (N_0 + 1)) / 2^64 + (2^64 - 1 - a1) + N_1) / 2^64 + (2^64 - 1 - a2) + N_2) / 2^64 + (2^64 - 1 - a3) + N_3).
    { rewrite Hacc3_raw, Ht3a, Hcarry2_val, Hacc2.
      simpl u64_val.
      lia. }

    clear Hacc3_raw Ht3a Hcarry2_val carry2 t3a.

    (* lo3 = secp256k1_u128_to_u64(&t) *)
    forward_call_u128_to_u64 v_t acc3 Tsh lo3 Hlo3.
    (* r->d[3] = lo3 & nonzero *)
    forward.

    (* ===== Stage 4: Postcondition ===== *)

    (* property POST: [(a + (-a mod N)) mod N = 0]; entailer! discharges it from
       this fact, then the SEP limb-matching proceeds as before. *)
    assert (Hprop : Z.modulo (Z.add (scalar_val a) (scalar_val (scalar_negate a)))
                      secp256k1_N = 0) by apply scalar_negate_prop.

    Exists (scalar_negate a).
    entailer!.

    (* Goal: masked upd_Znth chain |-- scalar_to_val (scalar_negate a) *)
    apply derives_refl'.
    f_equal.

    (* Split on whether [a] is zero: the mask is then 0 or all-ones. *)
    destruct (Z.eq_dec (scalar_val a) 0) as [Ha0|Ha0].

    (* branch: a = 0 -- every masked limb is 0, and [scalar_negate 0 = 0]. *)
    + rewrite (scalar_negate_zero_limbs_eq a Ha0).
      rewrite !Int64.and_zero.
      reflexivity.

    (* branch: a <> 0 -- the mask is the identity; the carry chain gives [N - a]. *)
    + rewrite !Int64.and_mone.
      rewrite !u128_lo_val.
      rewrite Hacc0, Hacc1, Hacc2, Hacc3.
      unfold scalar_to_val.

      (* Name the four round accumulators. *)
      set (t0 := 2^64 - 1 - a0 + (N_0 + 1)).
      set (t1 := t0 / 2^64 + (2^64 - 1 - a1) + N_1).
      set (t2 := t1 / 2^64 + (2^64 - 1 - a2) + N_2).
      set (t3 := t2 / 2^64 + (2^64 - 1 - a3) + N_3).

      (* Collapse the [upd_Znth] chain to a plain 4-element list. *)
      transitivity [Vlong (Int64.repr (t0 mod 2^64));
                    Vlong (Int64.repr (t1 mod 2^64));
                    Vlong (Int64.repr (t2 mod 2^64));
                    Vlong (Int64.repr (t3 mod 2^64))].
      { reflexivity. }

      (* Reduce to four pure-Z limb equalities. *)
      cut (t0 mod 2^64 = scalar_negate a mod 2^64 /\
           t1 mod 2^64 = (scalar_negate a / 2^64) mod 2^64 /\
           t2 mod 2^64 = (scalar_negate a / 2^128) mod 2^64 /\
           t3 mod 2^64 = (scalar_negate a / 2^192) mod 2^64).
      { intros [-> [-> [-> ->]]].
        reflexivity. }

      (* ===== Stage 5: the chain limbs are the limbs of [N - a] ===== *)

      assert (Harange : 0 <= scalar_val a < secp256k1_N) by apply scalar_range.
      assert (Hadecomp : a0 + a1 * 2^64 + a2 * (2^64)^2 + a3 * (2^64)^3 = scalar_val a)
        by (subst a0 a1 a2 a3; apply scalar_negate_limbs_eval_eq).

      (* On this branch [negate a = N - a], whose limbs are the chain's. *)
      rewrite (scalar_negate_val_eq a Ha0).
      apply (scalar_negate_chain_limbs_eq a0 a1 a2 a3 (scalar_val a)
        Ha0r Ha1r Ha2r Ha3r ltac:(lia) Hadecomp).

  (* branch: alias = false -- the ordinary non-aliasing proof. *)
  (* [r] and [a] are distinct chunks: loads read the untouched [a], stores
     build the fresh [r] chunk. *)
  - specialize (H0 eq_refl).
    clear H.
    rename SH into Hsh_r.
    rename H0 into Hsh_a.

    (* ===== Stage 0: nonzero = is_zero(a) ? 0 : -1 ===== *)

    (* _t'1 = secp256k1_scalar_is_zero(a) *)
    forward_call (a_ptr, a, sh_a).
    (* The grouped SEP precondition leaves a frame entailment. *)
    cancel.

    (* nonzero = (-1) * (_t'1 == 0) *)
    forward.

    (* Name the mask value [nz] and characterise it by the zero test. *)
    set (nz := Int64.mul (Int64.repr (-1))
      (Int64.repr
         (Int.signed
            (Int.repr
               (Z.b2z
                  (Int.eq (Int.repr (if Z.eq_dec a 0 then 1 else 0))
                     (Int.repr 0))))))) in *.
    assert (Hnz : nz = if Z.eq_dec (scalar_val a) 0 then Int64.zero else Int64.mone)
      by (subst nz; apply Int64_neg1_mul_b2z_eq).
    clearbody nz.

    (* The four 64-bit limbs of [a]. *)
    set (a0 := limb (2^64) (scalar_val a) 0).
    set (a1 := limb (2^64) (scalar_val a) 1).
    set (a2 := limb (2^64) (scalar_val a) 2).
    set (a3 := limb (2^64) (scalar_val a) 3).

    (* The per-round complement and constant ranges. *)
    assert (Ha0r : 0 <= a0 < 2^64) by (subst a0; apply Z.mod_pos_bound; lia).
    assert (Ha1r : 0 <= a1 < 2^64) by (subst a1; apply Z.mod_pos_bound; lia).
    assert (Ha2r : 0 <= a2 < 2^64) by (subst a2; apply Z.mod_pos_bound; lia).
    assert (Ha3r : 0 <= a3 < 2^64) by (subst a3; apply Z.mod_pos_bound; lia).
    assert (Hd0r : 0 <= 2^64 - 1 - a0 < 2^64) by lia.
    assert (Hd1r : 0 <= 2^64 - 1 - a1 < 2^64) by lia.
    assert (Hd2r : 0 <= 2^64 - 1 - a2 < 2^64) by lia.
    assert (Hd3r : 0 <= 2^64 - 1 - a3 < 2^64) by lia.
    assert (Hc0r : 0 <= N_0 + 1 < 2^64) by (unfold N_0; lia).
    assert (Hc1r : 0 <= N_1 < 2^64) by (unfold N_1; lia).
    assert (Hc2r : 0 <= N_2 < 2^64) by (unfold N_2; lia).
    assert (Hc3r : 0 <= N_3 < 2^64) by (unfold N_3; lia).

    (* ===== Round 0: t = ~a[0] + (N_0 + 1) ===== *)

    (* _t'9 = a->d[0] *)
    forward.

    (* secp256k1_u128_from_u64(&t, ~a->d[0]) *)
    forward_call_u128_from_u64 v_t (mkUInt64 (2^64 - 1 - a0) Hd0r) Tsh t_init Ht_init.
    { entailer!.
      simpl.
      unfold uint64_to_val.
      simpl.
      do 2 f_equal.
      change (Z.pow_pos 2 64) with (2^64).
      assert (Ha0e : a0 = a mod 2^64).
      { subst a0.
        unfold limb.
        simpl Z.of_nat.
        rewrite Z.pow_0_r, Z.div_1_r.
        reflexivity. }
      rewrite Int64_not_repr_complement by (apply Z.mod_pos_bound; lia).
      rewrite Ha0e.
      reflexivity. }

    (* secp256k1_u128_accum_u64(&t, N_0 + 1) *)
    forward_call_u128_accum_u64 v_t t_init (mkUInt64 (N_0 + 1) Hc0r) Tsh acc0 Hacc0_raw.
    assert (Hacc0 : u128_val acc0 = (2^64 - 1 - a0) + (N_0 + 1))
      by (rewrite Hacc0_raw, Ht_init; reflexivity).
    clear Ht_init Hacc0_raw t_init.

    (* lo0 = secp256k1_u128_to_u64(&t) *)
    forward_call_u128_to_u64 v_t acc0 Tsh lo0 Hlo0.
    (* r->d[0] = lo0 & nonzero *)
    forward.

    (* secp256k1_u128_rshift(&t, 64) *)
    forward_call_u128_rshift v_t acc0 Tsh carry0 Hcarry0.
    assert (Hcarry0_val : u128_val carry0 = ((2^64 - 1 - a0) + (N_0 + 1)) / 2^64)
      by (rewrite Hcarry0, Hacc0; reflexivity).
    clear Hcarry0.

    (* The round-0 carry is a bit ([scalar_negate_carry0_bnd]); with it in
       context the wrapper discharges the [< 2^128] precondition of both
       round-1 accumulate calls. *)
    pose proof (scalar_negate_carry0_bnd a0 Ha0r) as Hcarry0_bnd.

    (* ===== Round 1: t += ~a[1] + N_1 ===== *)

    (* _t'8 = a->d[1] *)
    forward.

    (* secp256k1_u128_accum_u64(&t, ~a->d[1]) *)
    forward_call_u128_accum_u64 v_t carry0 (mkUInt64 (2^64 - 1 - a1) Hd1r) Tsh t1a Ht1a.
    { entailer!.
      simpl.
      unfold uint64_to_val.
      do 2 f_equal.
      change (Z.pow_pos 2 64) with (2^64).
      rewrite Int64_not_repr_complement by (apply Z.mod_pos_bound; lia).
      f_equal. }

    (* secp256k1_u128_accum_u64(&t, N_1) *)
    forward_call_u128_accum_u64 v_t t1a (mkUInt64 N_1 Hc1r) Tsh acc1 Hacc1_raw.
    { entailer!.
      simpl.
      unfold uint64_to_val.
      do 2 f_equal.
      f_equal.
      apply Int64.same_if_eq.
      vm_compute.
      reflexivity. }

    assert (Hacc1 : u128_val acc1 = ((2^64 - 1 - a0) + (N_0 + 1)) / 2^64 + (2^64 - 1 - a1) + N_1).
    { rewrite Hacc1_raw, Ht1a, Hcarry0_val.
      simpl u64_val.
      lia. }

    clear Hacc1_raw Ht1a Hcarry0_val Hcarry0_bnd carry0 t1a.

    (* lo1 = secp256k1_u128_to_u64(&t) *)
    forward_call_u128_to_u64 v_t acc1 Tsh lo1 Hlo1.
    (* r->d[1] = lo1 & nonzero *)
    forward.

    (* secp256k1_u128_rshift(&t, 64) *)
    forward_call_u128_rshift v_t acc1 Tsh carry1 Hcarry1.
    assert (Hcarry1_val : u128_val carry1 = u128_val acc1 / 2^64) by exact Hcarry1.
    clear Hcarry1.

    (* ===== Round 2: t += ~a[2] + N_2 ===== *)

    (* _t'7 = a->d[2] *)
    forward.

    (* secp256k1_u128_accum_u64(&t, ~a->d[2]) *)
    forward_call_u128_accum_u64 v_t carry1 (mkUInt64 (2^64 - 1 - a2) Hd2r) Tsh t2a Ht2a.
    { entailer!.
      simpl.
      unfold uint64_to_val.
      do 2 f_equal.
      change (Z.pow_pos 2 64) with (2^64).
      rewrite Int64_not_repr_complement by (apply Z.mod_pos_bound; lia).
      f_equal. }

    (* secp256k1_u128_accum_u64(&t, N_2) *)
    forward_call_u128_accum_u64 v_t t2a (mkUInt64 N_2 Hc2r) Tsh acc2 Hacc2_raw.
    { entailer!.
      simpl.
      unfold uint64_to_val.
      do 2 f_equal.
      f_equal.
      apply Int64.same_if_eq.
      vm_compute.
      reflexivity. }

    assert (Hacc2 : u128_val acc2 =
      ((2^64 - 1 - a0 + (N_0 + 1)) / 2^64 + (2^64 - 1 - a1) + N_1) / 2^64 + (2^64 - 1 - a2) + N_2).
    { rewrite Hacc2_raw, Ht2a, Hcarry1_val, Hacc1.
      simpl u64_val.
      lia. }

    clear Hacc2_raw Ht2a Hcarry1_val carry1 t2a.

    (* lo2 = secp256k1_u128_to_u64(&t) *)
    forward_call_u128_to_u64 v_t acc2 Tsh lo2 Hlo2.
    (* r->d[2] = lo2 & nonzero *)
    forward.

    (* secp256k1_u128_rshift(&t, 64) *)
    forward_call_u128_rshift v_t acc2 Tsh carry2 Hcarry2.
    assert (Hcarry2_val : u128_val carry2 = u128_val acc2 / 2^64) by exact Hcarry2.
    clear Hcarry2.

    (* ===== Round 3: t += ~a[3] + N_3 ===== *)

    (* _t'6 = a->d[3] *)
    forward.

    (* secp256k1_u128_accum_u64(&t, ~a->d[3]) *)
    forward_call_u128_accum_u64 v_t carry2 (mkUInt64 (2^64 - 1 - a3) Hd3r) Tsh t3a Ht3a.
    { entailer!.
      simpl.
      unfold uint64_to_val.
      do 2 f_equal.
      change (Z.pow_pos 2 64) with (2^64).
      rewrite Int64_not_repr_complement by (apply Z.mod_pos_bound; lia).
      f_equal. }

    (* secp256k1_u128_accum_u64(&t, N_3) *)
    forward_call_u128_accum_u64 v_t t3a (mkUInt64 N_3 Hc3r) Tsh acc3 Hacc3_raw.
    { entailer!.
      simpl.
      unfold uint64_to_val.
      do 2 f_equal.
      f_equal.
      apply Int64.same_if_eq.
      vm_compute.
      reflexivity. }

    assert (Hacc3 : u128_val acc3 =
      (((2^64 - 1 - a0 + (N_0 + 1)) / 2^64 + (2^64 - 1 - a1) + N_1) / 2^64 + (2^64 - 1 - a2) + N_2) / 2^64 + (2^64 - 1 - a3) + N_3).
    { rewrite Hacc3_raw, Ht3a, Hcarry2_val, Hacc2.
      simpl u64_val.
      lia. }

    clear Hacc3_raw Ht3a Hcarry2_val carry2 t3a.

    (* lo3 = secp256k1_u128_to_u64(&t) *)
    forward_call_u128_to_u64 v_t acc3 Tsh lo3 Hlo3.
    (* r->d[3] = lo3 & nonzero *)
    forward.

    (* ===== Stage 4: Postcondition ===== *)

    (* property POST: [(a + (-a mod N)) mod N = 0]; entailer! discharges it from
       this fact, then the SEP limb-matching proceeds as before. *)
    assert (Hprop : Z.modulo (Z.add (scalar_val a) (scalar_val (scalar_negate a)))
                      secp256k1_N = 0) by apply scalar_negate_prop.

    Exists (scalar_negate a).
    entailer!.

    (* Goal: masked upd_Znth chain |-- scalar_to_val (scalar_negate a) *)
    apply derives_refl'.
    f_equal.

    (* Split on whether [a] is zero: the mask is then 0 or all-ones. *)
    destruct (Z.eq_dec (scalar_val a) 0) as [Ha0|Ha0].

    (* branch: a = 0 -- every masked limb is 0, and [scalar_negate 0 = 0]. *)
    + rewrite (scalar_negate_zero_limbs_eq a Ha0).
      rewrite !Int64.and_zero.
      reflexivity.

    (* branch: a <> 0 -- the mask is the identity; the carry chain gives [N - a]. *)
    + rewrite !Int64.and_mone.
      rewrite !u128_lo_val.
      rewrite Hacc0, Hacc1, Hacc2, Hacc3.
      unfold scalar_to_val.

      (* Name the four round accumulators. *)
      set (t0 := 2^64 - 1 - a0 + (N_0 + 1)).
      set (t1 := t0 / 2^64 + (2^64 - 1 - a1) + N_1).
      set (t2 := t1 / 2^64 + (2^64 - 1 - a2) + N_2).
      set (t3 := t2 / 2^64 + (2^64 - 1 - a3) + N_3).

      (* Collapse the [upd_Znth] chain to a plain 4-element list. *)
      transitivity [Vlong (Int64.repr (t0 mod 2^64));
                    Vlong (Int64.repr (t1 mod 2^64));
                    Vlong (Int64.repr (t2 mod 2^64));
                    Vlong (Int64.repr (t3 mod 2^64))].
      { reflexivity. }

      (* Reduce to four pure-Z limb equalities. *)
      cut (t0 mod 2^64 = scalar_negate a mod 2^64 /\
           t1 mod 2^64 = (scalar_negate a / 2^64) mod 2^64 /\
           t2 mod 2^64 = (scalar_negate a / 2^128) mod 2^64 /\
           t3 mod 2^64 = (scalar_negate a / 2^192) mod 2^64).
      { intros [-> [-> [-> ->]]].
        reflexivity. }

      (* ===== Stage 5: the chain limbs are the limbs of [N - a] ===== *)

      assert (Harange : 0 <= scalar_val a < secp256k1_N) by apply scalar_range.
      assert (Hadecomp : a0 + a1 * 2^64 + a2 * (2^64)^2 + a3 * (2^64)^3 = scalar_val a)
        by (subst a0 a1 a2 a3; apply scalar_negate_limbs_eval_eq).

      (* On this branch [negate a = N - a], whose limbs are the chain's. *)
      rewrite (scalar_negate_val_eq a Ha0).
      apply (scalar_negate_chain_limbs_eq a0 a1 a2 a3 (scalar_val a)
        Ha0r Ha1r Ha2r Ha3r ltac:(lia) Hadecomp).
Qed.
