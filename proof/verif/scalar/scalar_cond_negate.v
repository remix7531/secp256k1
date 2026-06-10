(** * verif.scalar.scalar_cond_negate: Proof of body_secp256k1_scalar_cond_negate. *)
(** Copyright (C) 2026 remix7531
    SPDX-License-Identifier: MIT *)

Require Import secp256k1.vst.base.
Require Import secp256k1.contract.helper.notations.
Require Import secp256k1.contract.gprog.scalar.
Require Import secp256k1.tactics.core.
Require Import secp256k1.tactics.int128.
Require Import secp256k1.tactics.scalar.

(* ================================================================= *)
(** ** Pure-Z helper -- bitwise-not as arithmetic complement. *)

(** The bitwise-not-as-arithmetic identity [~x = 2^64 - 1 - x] is the shared
    [vst.integers.Int64_not_repr_complement]; the [flag = 1] branch is exactly
    [scalar_negate] over the same four-constant ripple-add carry chain. *)

(** XOR with the all-ones mask is bitwise complement: [x ^ (-1) = ~x].
    Definitional ([Int64.not x := Int64.xor x Int64.mone]); stated as a
    rewrite lemma so the masked [flag = 1] limbs (the C [r[i] ^ mask]
    with [mask = -1]) convert uniformly to the [scalar_negate] form. *)
Lemma Int64_xor_mone : forall x,
  Int64.xor x Int64.mone = Int64.not x.
Proof. reflexivity. Qed.

(* ================================================================= *)
(** ** secp256k1_scalar_cond_negate -- [flag ? -r0 mod N : r0]. *)

(** Constant-time conditional negate of [*r] modulo [N], returning [-1]
    if negated and [1] otherwise.  The extraction unit [#define]s
    [volatile] away (the [volatile int vflag] hardening hint becomes a
    plain temp -- no [EF_vstore] / [EF_vload] builtins), so the masked
    u128 ripple goes through.  The mask is [mask = -vflag]: with
    [flag = 1] ([mask = -1 = all ones]) each limb computes [~r[i]] plus
    the [N]-limb and the body is exactly [scalar_negate]; with [flag = 0]
    ([mask = 0]) the xor and the [N]-limb [and] vanish, so the
    accumulator is just [r[i]] and the result is [r0] unchanged.  The
    final [& nonzero] (with [nonzero = is_zero(r) ? 0 : -1]) maps the
    [r0 = 0] case (where [-0 = 0]) to all-zero limbs. *)
Lemma body_secp256k1_scalar_cond_negate:
  semax_body Vprog Gprog
    f_secp256k1_scalar_cond_negate spec_secp256k1_scalar_cond_negate.
Proof.
  start_function.

  (* ===== Stage 0: mask = -vflag, nonzero = is_zero(r) ? 0 : -1 ===== *)

  (* vflag = flag (a plain temp -- volatile neutralized in the extraction) *)
  forward.
  (* mask = (uint64_t)(-vflag); the cast cannot overflow as flag in {0,1} *)
  forward.
  entailer!.
  change (Int.signed Int.zero) with 0; rep_lia.
  (* _t'1 = secp256k1_scalar_is_zero(r) -- reads the chunk in place *)
  forward_call (r_ptr, r0, sh).
  (* nonzero = (uint64_t)((_t'1 != 0) - 1) *)
  forward.
  entailer!.
  destruct (negb (Int.eq (Int.repr (if Z.eq_dec r0 0 then 1 else 0)) (Int.repr 0))); simpl Z.b2z; rewrite ?Int.signed_repr; rep_lia.

  (* Name the [nonzero] mask [nz]; it is 0 when [r0 = 0] and all-ones else. *)
  set (nz := Int64.repr (Int.signed (Int.repr (Z.b2z (negb (Int.eq (Int.repr (if Z.eq_dec r0 0 then 1 else 0)) (Int.repr 0))) - 1)))) in *.
  assert (Hnz : nz = if Z.eq_dec (scalar_val r0) 0 then Int64.zero else Int64.mone).
  { subst nz.
    destruct (Z.eq_dec (scalar_val r0) 0) as [Hr0|Hr0]; apply Int64.same_if_eq; vm_compute; reflexivity. }
  clearbody nz.

  (* Name the [-vflag] mask [m]; it is all-ones when [flag = 1], 0 else. *)
  set (m := Int64.repr (Int.signed (Int.neg (Int.repr flag)))) in *.
  assert (Hm : m = if Z.eq_dec flag 1 then Int64.mone else Int64.zero).
  { subst m.
    destruct H as [Hf|Hf]; subst flag; apply Int64.same_if_eq; vm_compute; reflexivity. }
  clearbody m.

  (* Limbs of [r0] and the per-round complement/constant ranges. *)
  set (a0 := limb (2^64) (scalar_val r0) 0).
  set (a1 := limb (2^64) (scalar_val r0) 1).
  set (a2 := limb (2^64) (scalar_val r0) 2).
  set (a3 := limb (2^64) (scalar_val r0) 3).
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

  (* Split on [flag]: [flag = 0] is a no-op, [flag = 1] is [scalar_negate]. *)
  destruct H as [Hf|Hf]; subst flag.

  (* branch: flag = 0 -- mask = 0, so every limb keeps [r0]. *)
  (* The xor and the [N]-limb [and] both vanish; each accumulator is just
     [r0[i]] (no carry), and the final [& nonzero] either keeps [r0] (if
     [r0 <> 0]) or zeroes it (if [r0 = 0], where [r0 = 0] anyway). *)
  - replace m with Int64.zero in * by (rewrite Hm; reflexivity); clear Hm m.
    assert (Hzr : 0 <= 0 < 2^64) by lia.

    (* ===== Round 0: t = r0[0] ^ 0, accum 0 ===== *)

    (* _t'9 = r->d[0] *)
    forward.
    (* secp256k1_u128_from_u64(&t, r->d[0] ^ mask) *)
    forward_call_u128_from_u64 v_t (mkUInt64 a0 Ha0r) Tsh t_init Ht_init.
    { entailer!.
      simpl.
      unfold uint64_to_val.
      simpl.
      do 2 f_equal.
      rewrite Int64.xor_zero.
      change (Z.pow_pos 2 64) with (2^64).
      subst a0.
      unfold limb.
      simpl Z.of_nat.
      rewrite Z.pow_0_r, Z.div_1_r.
      reflexivity. }
    (* secp256k1_u128_accum_u64(&t, (N_0 + 1) & mask) = accum 0 *)
    forward_call_u128_accum_u64 v_t t_init (mkUInt64 0 Hzr) Tsh acc0 Hacc0_raw.
    assert (Hacc0 : u128_val acc0 = a0) by (rewrite Hacc0_raw, Ht_init; simpl u64_val; lia).
    clear Ht_init Hacc0_raw t_init.
    (* lo0 = secp256k1_u128_to_u64(&t); r->d[0] = lo0 & nonzero *)
    forward_call_u128_to_u64 v_t acc0 Tsh lo0 Hlo0.
    forward.
    (* secp256k1_u128_rshift(&t, 64) -- carry is 0 *)
    forward_call_u128_rshift v_t acc0 Tsh carry0 Hcarry0.
    assert (Hcarry0_val : u128_val carry0 = 0) by (rewrite Hcarry0, Hacc0; apply Z.div_small; lia).
    clear Hcarry0.

    (* ===== Round 1: t += r0[1] ^ 0, accum 0 ===== *)

    (* _t'8 = r->d[1] -- still reads [r0]'s limb 1 (only limb 0 was written) *)
    forward.
    (* secp256k1_u128_accum_u64(&t, r->d[1] ^ mask) *)
    forward_call_u128_accum_u64 v_t carry0 (mkUInt64 a1 Ha1r) Tsh t1a Ht1a.
    rewrite Znth_upd_Znth_diff by lia.
    { entailer!.
      simpl.
      unfold uint64_to_val.
      do 2 f_equal.
      f_equal.
      rewrite Int64.xor_zero.
      reflexivity. }
    assert (Hacc1 : u128_val t1a = a1) by (rewrite Ht1a, Hcarry0_val; simpl u64_val; lia).
    clear Ht1a Hcarry0_val carry0.
    (* secp256k1_u128_accum_u64(&t, N_1 & mask) = accum 0 *)
    forward_call_u128_accum_u64 v_t t1a (mkUInt64 0 Hzr) Tsh acc1 Hacc1_raw.
    assert (Hacc1v : u128_val acc1 = a1) by (rewrite Hacc1_raw, Hacc1; simpl u64_val; lia).
    clear Hacc1_raw Hacc1 t1a.
    (* lo1 = secp256k1_u128_to_u64(&t); r->d[1] = lo1 & nonzero *)
    forward_call_u128_to_u64 v_t acc1 Tsh lo1 Hlo1.
    forward.
    (* secp256k1_u128_rshift(&t, 64) -- carry is 0 *)
    forward_call_u128_rshift v_t acc1 Tsh carry1 Hcarry1.
    assert (Hcarry1_val : u128_val carry1 = 0) by (rewrite Hcarry1, Hacc1v; apply Z.div_small; lia).
    clear Hcarry1.

    (* ===== Round 2: t += r0[2] ^ 0, accum 0 ===== *)

    (* _t'7 = r->d[2] -- still reads [r0]'s limb 2 (limbs 0,1 were written) *)
    forward.
    (* secp256k1_u128_accum_u64(&t, r->d[2] ^ mask) *)
    forward_call_u128_accum_u64 v_t carry1 (mkUInt64 a2 Ha2r) Tsh t2a Ht2a.
    rewrite !Znth_upd_Znth_diff by lia.
    { entailer!.
      simpl.
      unfold uint64_to_val.
      do 2 f_equal.
      f_equal.
      rewrite Int64.xor_zero.
      reflexivity. }
    assert (Hacc2 : u128_val t2a = a2) by (rewrite Ht2a, Hcarry1_val; simpl u64_val; lia).
    clear Ht2a Hcarry1_val carry1.
    (* secp256k1_u128_accum_u64(&t, N_2 & mask) = accum 0 *)
    forward_call_u128_accum_u64 v_t t2a (mkUInt64 0 Hzr) Tsh acc2 Hacc2_raw.
    assert (Hacc2v : u128_val acc2 = a2) by (rewrite Hacc2_raw, Hacc2; simpl u64_val; lia).
    clear Hacc2_raw Hacc2 t2a.
    (* lo2 = secp256k1_u128_to_u64(&t); r->d[2] = lo2 & nonzero *)
    forward_call_u128_to_u64 v_t acc2 Tsh lo2 Hlo2.
    forward.
    (* secp256k1_u128_rshift(&t, 64) -- carry is 0 *)
    forward_call_u128_rshift v_t acc2 Tsh carry2 Hcarry2.
    assert (Hcarry2_val : u128_val carry2 = 0) by (rewrite Hcarry2, Hacc2v; apply Z.div_small; lia).
    clear Hcarry2.

    (* ===== Round 3: t += r0[3] ^ 0, accum 0 ===== *)

    (* _t'6 = r->d[3] -- still reads [r0]'s limb 3 (limbs 0,1,2 were written) *)
    forward.
    (* secp256k1_u128_accum_u64(&t, r->d[3] ^ mask) *)
    forward_call_u128_accum_u64 v_t carry2 (mkUInt64 a3 Ha3r) Tsh t3a Ht3a.
    rewrite !Znth_upd_Znth_diff by lia.
    { entailer!.
      simpl.
      unfold uint64_to_val.
      do 2 f_equal.
      f_equal.
      rewrite Int64.xor_zero.
      reflexivity. }
    assert (Hacc3 : u128_val t3a = a3) by (rewrite Ht3a, Hcarry2_val; simpl u64_val; lia).
    clear Ht3a Hcarry2_val carry2.
    (* secp256k1_u128_accum_u64(&t, N_3 & mask) = accum 0 *)
    forward_call_u128_accum_u64 v_t t3a (mkUInt64 0 Hzr) Tsh acc3 Hacc3_raw.
    assert (Hacc3v : u128_val acc3 = a3) by (rewrite Hacc3_raw, Hacc3; simpl u64_val; lia).
    clear Hacc3_raw Hacc3 t3a.
    (* lo3 = secp256k1_u128_to_u64(&t); r->d[3] = lo3 & nonzero *)
    forward_call_u128_to_u64 v_t acc3 Tsh lo3 Hlo3.
    forward.

    (* ===== Stage 4: return 2*(mask == 0) - 1 = 1, postcondition r = r0 ===== *)

    (* return 2 * (mask == 0) - 1 *)
    forward.
    Exists r0.
    entailer!.

    (* The masked store chain |-- scalar_at sh r_ptr r0. *)
    apply derives_refl'.
    f_equal.
    rewrite !u128_lo_val.
    rewrite Hacc0, Hacc1v, Hacc2v, Hacc3v.
    destruct (Z.eq_dec (scalar_val r0) 0) as [Hr0|Hr0].
    (* r0 = 0: nonzero = 0, every masked limb is 0, and scalar_to_val 0 = 0. *)
    + assert (Hz0 : limb (2^64) (scalar_val r0) 0 = 0) by (unfold limb; rewrite Hr0; reflexivity).
      assert (Hz1 : limb (2^64) (scalar_val r0) 1 = 0) by (unfold limb; rewrite Hr0; reflexivity).
      assert (Hz2 : limb (2^64) (scalar_val r0) 2 = 0) by (unfold limb; rewrite Hr0; reflexivity).
      assert (Hz3 : limb (2^64) (scalar_val r0) 3 = 0) by (unfold limb; rewrite Hr0; reflexivity).
      rewrite Hz0, Hz1, Hz2, Hz3.
      rewrite !Int64.and_zero.
      unfold scalar_to_val.
      rewrite Hr0.
      change (0 mod 2^64) with 0.
      change (0 / 2^64 mod 2^64) with 0.
      change (0 / 2^128 mod 2^64) with 0.
      change (0 / 2^192 mod 2^64) with 0.
      reflexivity.
    (* r0 <> 0: nonzero = -1, each masked limb is the original [r0] limb. *)
    + rewrite !Int64.and_mone.
      unfold scalar_to_val, limb.
      simpl Z.of_nat.
      rewrite Z.pow_0_r, Z.div_1_r, Z.pow_1_r.
      rewrite !Zmod_mod.
      change ((2^64)^2) with (2^128).
      change ((2^64)^3) with (2^192).
      reflexivity.

  (* branch: flag = 1 -- mask = -1, so the body is exactly [scalar_negate]. *)
  (* Each limb computes [~r0[i] + N_i] (the [N]-limb [and] is the identity),
     a four-constant ripple-add carry chain giving [N - r0]; the final
     [& nonzero] maps the [r0 = 0] case (where [-0 = 0]) to all-zero limbs. *)
  - replace m with Int64.mone in * by (rewrite Hm; reflexivity); clear Hm m.

    (* ===== Round 0: t = ~r0[0] + (N_0 + 1) ===== *)

    (* _t'9 = r->d[0] *)
    forward.
    (* secp256k1_u128_from_u64(&t, r->d[0] ^ mask) = from_u64(~r0[0]) *)
    forward_call_u128_from_u64 v_t (mkUInt64 (2^64 - 1 - a0) Hd0r) Tsh t_init Ht_init.
    { entailer!.
      simpl.
      unfold uint64_to_val.
      simpl.
      do 2 f_equal.
      rewrite Int64_xor_mone.
      change (Z.pow_pos 2 64) with (2^64).
      assert (Ha0e : a0 = r0 mod 2^64) by (subst a0; unfold limb; simpl Z.of_nat; rewrite Z.pow_0_r, Z.div_1_r; reflexivity).
      rewrite Int64_not_repr_complement by (apply Z.mod_pos_bound; lia).
      rewrite Ha0e.
      reflexivity. }
    (* secp256k1_u128_accum_u64(&t, (N_0 + 1) & mask) = accum (N_0 + 1) *)
    forward_call_u128_accum_u64 v_t t_init (mkUInt64 (N_0 + 1) Hc0r) Tsh acc0 Hacc0_raw.
    assert (Hacc0 : u128_val acc0 = (2^64 - 1 - a0) + (N_0 + 1))
      by (rewrite Hacc0_raw, Ht_init; reflexivity).
    clear Ht_init Hacc0_raw t_init.
    (* lo0 = secp256k1_u128_to_u64(&t); r->d[0] = lo0 & nonzero *)
    forward_call_u128_to_u64 v_t acc0 Tsh lo0 Hlo0.
    forward.
    (* secp256k1_u128_rshift(&t, 64) *)
    forward_call_u128_rshift v_t acc0 Tsh carry0 Hcarry0.
    assert (Hcarry0_val : u128_val carry0 = ((2^64 - 1 - a0) + (N_0 + 1)) / 2^64)
      by (rewrite Hcarry0, Hacc0; reflexivity).
    clear Hcarry0.

    (* ===== Round 1: t += ~r0[1] + N_1 ===== *)

    (* _t'8 = r->d[1] -- still reads [r0]'s limb 1 (only limb 0 was written) *)
    forward.
    (* secp256k1_u128_accum_u64(&t, r->d[1] ^ mask) = accum (~r0[1]) *)
    forward_call_u128_accum_u64 v_t carry0 (mkUInt64 (2^64 - 1 - a1) Hd1r) Tsh t1a Ht1a.
    rewrite Znth_upd_Znth_diff by lia.
    { entailer!.
      simpl.
      unfold uint64_to_val.
      do 2 f_equal.
      f_equal.
      rewrite Int64_xor_mone.
      rewrite Int64_not_repr_complement by (apply Z.mod_pos_bound; lia).
      f_equal. }
    { rewrite Hcarry0_val.
      simpl u64_val.
      assert (Hcb : (2 ^ 64 - 1 - a0 + (N_0 + 1)) / 2 ^ 64 < 2) by (apply Z.div_lt_upper_bound; unfold N_0; lia).
      assert (Hcnn : 0 <= (2 ^ 64 - 1 - a0 + (N_0 + 1)) / 2 ^ 64) by (apply Z.div_pos; unfold N_0; lia).
      lia. }
    (* secp256k1_u128_accum_u64(&t, N_1 & mask) = accum N_1 *)
    forward_call_u128_accum_u64 v_t t1a (mkUInt64 N_1 Hc1r) Tsh acc1 Hacc1_raw.
    { rewrite Ht1a, Hcarry0_val.
      simpl u64_val.
      assert (Hcb : (2 ^ 64 - 1 - a0 + (N_0 + 1)) / 2 ^ 64 < 2) by (apply Z.div_lt_upper_bound; unfold N_0; lia).
      assert (Hcnn : 0 <= (2 ^ 64 - 1 - a0 + (N_0 + 1)) / 2 ^ 64) by (apply Z.div_pos; unfold N_0; lia).
      unfold N_1.
      lia. }
    assert (Hacc1 : u128_val acc1 = ((2^64 - 1 - a0) + (N_0 + 1)) / 2^64 + (2^64 - 1 - a1) + N_1).
    { rewrite Hacc1_raw, Ht1a, Hcarry0_val.
      simpl u64_val.
      lia. }
    clear Hacc1_raw Ht1a Hcarry0_val carry0 t1a.
    (* lo1 = secp256k1_u128_to_u64(&t); r->d[1] = lo1 & nonzero *)
    forward_call_u128_to_u64 v_t acc1 Tsh lo1 Hlo1.
    forward.
    (* secp256k1_u128_rshift(&t, 64) *)
    forward_call_u128_rshift v_t acc1 Tsh carry1 Hcarry1.
    assert (Hcarry1_val : u128_val carry1 = u128_val acc1 / 2^64) by exact Hcarry1.
    clear Hcarry1.

    (* ===== Round 2: t += ~r0[2] + N_2 ===== *)

    (* _t'7 = r->d[2] -- still reads [r0]'s limb 2 (limbs 0,1 were written) *)
    forward.
    (* secp256k1_u128_accum_u64(&t, r->d[2] ^ mask) = accum (~r0[2]) *)
    forward_call_u128_accum_u64 v_t carry1 (mkUInt64 (2^64 - 1 - a2) Hd2r) Tsh t2a Ht2a.
    rewrite !Znth_upd_Znth_diff by lia.
    { entailer!.
      simpl.
      unfold uint64_to_val.
      do 2 f_equal.
      f_equal.
      rewrite Int64_xor_mone.
      rewrite Int64_not_repr_complement by (apply Z.mod_pos_bound; lia).
      f_equal. }
    (* secp256k1_u128_accum_u64(&t, N_2 & mask) = accum N_2 *)
    forward_call_u128_accum_u64 v_t t2a (mkUInt64 N_2 Hc2r) Tsh acc2 Hacc2_raw.
    assert (Hacc2 : u128_val acc2 =
      ((2^64 - 1 - a0 + (N_0 + 1)) / 2^64 + (2^64 - 1 - a1) + N_1) / 2^64 + (2^64 - 1 - a2) + N_2).
    { rewrite Hacc2_raw, Ht2a, Hcarry1_val, Hacc1.
      simpl u64_val.
      lia. }
    clear Hacc2_raw Ht2a Hcarry1_val carry1 t2a.
    (* lo2 = secp256k1_u128_to_u64(&t); r->d[2] = lo2 & nonzero *)
    forward_call_u128_to_u64 v_t acc2 Tsh lo2 Hlo2.
    forward.
    (* secp256k1_u128_rshift(&t, 64) *)
    forward_call_u128_rshift v_t acc2 Tsh carry2 Hcarry2.
    assert (Hcarry2_val : u128_val carry2 = u128_val acc2 / 2^64) by exact Hcarry2.
    clear Hcarry2.

    (* ===== Round 3: t += ~r0[3] + N_3 ===== *)

    (* _t'6 = r->d[3] -- still reads [r0]'s limb 3 (limbs 0,1,2 were written) *)
    forward.
    (* secp256k1_u128_accum_u64(&t, r->d[3] ^ mask) = accum (~r0[3]) *)
    forward_call_u128_accum_u64 v_t carry2 (mkUInt64 (2^64 - 1 - a3) Hd3r) Tsh t3a Ht3a.
    rewrite !Znth_upd_Znth_diff by lia.
    { entailer!.
      simpl.
      unfold uint64_to_val.
      do 2 f_equal.
      f_equal.
      rewrite Int64_xor_mone.
      rewrite Int64_not_repr_complement by (apply Z.mod_pos_bound; lia).
      f_equal. }
    (* secp256k1_u128_accum_u64(&t, N_3 & mask) = accum N_3 *)
    forward_call_u128_accum_u64 v_t t3a (mkUInt64 N_3 Hc3r) Tsh acc3 Hacc3_raw.
    assert (Hacc3 : u128_val acc3 =
      (((2^64 - 1 - a0 + (N_0 + 1)) / 2^64 + (2^64 - 1 - a1) + N_1) / 2^64 + (2^64 - 1 - a2) + N_2) / 2^64 + (2^64 - 1 - a3) + N_3).
    { rewrite Hacc3_raw, Ht3a, Hcarry2_val, Hacc2.
      simpl u64_val.
      lia. }
    clear Hacc3_raw Ht3a Hcarry2_val carry2 t3a.
    (* lo3 = secp256k1_u128_to_u64(&t); r->d[3] = lo3 & nonzero *)
    forward_call_u128_to_u64 v_t acc3 Tsh lo3 Hlo3.
    forward.

    (* ===== Stage 4: return 2*(mask == 0) - 1 = -1, postcondition r = -r0 ===== *)

    (* return 2 * (mask == 0) - 1 *)
    forward.
    Exists (scalar_negate r0).
    entailer!.

    (* The masked store chain |-- scalar_at sh r_ptr (scalar_negate r0). *)
    apply derives_refl'.
    f_equal.
    (* Split on whether [r0] is zero: the [nonzero] mask is then 0 or all-ones. *)
    destruct (Z.eq_dec (scalar_val r0) 0) as [Ha0|Ha0].
    (* r0 = 0: every masked limb is 0, and scalar_negate 0 = 0. *)
    + assert (Hneg0 : scalar_val (scalar_negate r0) = 0).
      { unfold scalar_negate.
        simpl.
        rewrite Ha0.
        rewrite Z.sub_0_r.
        apply Z_mod_same_full. }
      unfold scalar_to_val.
      rewrite Hneg0.
      rewrite !Int64.and_zero.
      change (0 mod 2^64) with 0.
      change (0 / 2^64 mod 2^64) with 0.
      change (0 / 2^128 mod 2^64) with 0.
      change (0 / 2^192 mod 2^64) with 0.
      reflexivity.
    (* r0 <> 0: the mask is the identity; the carry chain gives [N - r0]. *)
    + rewrite !Int64.and_mone.
      rewrite !u128_lo_val.
      rewrite Hacc0, Hacc1, Hacc2, Hacc3.
      unfold scalar_to_val.
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
      cut (t0 mod 2^64 = scalar_negate r0 mod 2^64 /\
           t1 mod 2^64 = (scalar_negate r0 / 2^64) mod 2^64 /\
           t2 mod 2^64 = (scalar_negate r0 / 2^128) mod 2^64 /\
           t3 mod 2^64 = (scalar_negate r0 / 2^192) mod 2^64).
      { intros [-> [-> [-> ->]]].
        reflexivity. }

      (* ===== Stage 5: pure Z arithmetic (the four-constant carry chain) ===== *)

      assert (Harange : 0 <= scalar_val r0 < secp256k1_N) by apply scalar_range.
      assert (Hapos : 0 < scalar_val r0) by (assert (scalar_val r0 <> 0) by (intro Hcon; apply Ha0; exact Hcon); lia).
      assert (Hadecomp : a0 + a1 * 2^64 + a2 * (2^64)^2 + a3 * (2^64)^3 = scalar_val r0).
      { subst a0 a1 a2 a3.
        pose proof (eval4_limbs (2^64) (scalar_val r0) ltac:(lia)) as E.
        unfold eval4 in E.
        apply E.
        change ((2^64)^4) with (2^256).
        unfold secp256k1_N in Harange.
        lia. }
      assert (Hnegval : scalar_val (scalar_negate r0) = secp256k1_N - scalar_val r0).
      { unfold scalar_negate.
        simpl.
        rewrite Z.mod_small by lia.
        reflexivity. }
      clear - Ha0r Ha1r Ha2r Ha3r Hc0r Hc1r Hc2r Hc3r Harange Hapos Hadecomp Hnegval t0 t1 t2 t3 a0 a1 a2 a3.
      rewrite Hnegval.
      set (B := 2^64) in *.
      (* Apply the four-constant carry-chain identity. *)
      pose proof (add4_carry_chain B (2^64 - 1 - a0) (2^64 - 1 - a1) (2^64 - 1 - a2) (2^64 - 1 - a3)
        (N_0 + 1) N_1 N_2 N_3
        ltac:(subst B; lia)
        ltac:(subst B; lia) ltac:(subst B; lia) ltac:(subst B; lia) ltac:(subst B; lia)
        ltac:(lia) ltac:(unfold N_1; lia) ltac:(unfold N_2; lia) ltac:(unfold N_3; lia)) as Hchain.
      cbv zeta in Hchain.
      unfold eval4 in Hchain.
      replace (B ^ 2) with (B * B) in Hchain by ring.
      replace (B ^ 3) with (B * B * B) in Hchain by ring.
      (* val = 2^256 - 1 - r0 and C = N + 1, so val + C = 2^256 + N - r0. *)
      assert (HC : N_0 + 1 + N_1 * B + N_2 * (B * B) + N_3 * (B * B * B) = secp256k1_N + 1).
      { subst B.
        rewrite secp256k1_N_limbs.
        ring. }
      assert (Hval : 2 ^ 64 - 1 - a0 + (2 ^ 64 - 1 - a1) * B + (2 ^ 64 - 1 - a2) * (B * B) + (2 ^ 64 - 1 - a3) * (B * B * B) = B * B * B * B - 1 - r0).
      { rewrite <- Hadecomp.
        subst B.
        ring. }
      assert (Hbnd : 0 <= 2 ^ 64 - 1 - a0 + (2 ^ 64 - 1 - a1) * B + (2 ^ 64 - 1 - a2) * (B * B) + (2 ^ 64 - 1 - a3) * (B * B * B) + (N_0 + 1 + N_1 * B + N_2 * (B * B) + N_3 * (B * B * B)) < 2 * (B * B * B * B)).
      { rewrite Hval, HC.
        subst B.
        unfold secp256k1_N in *.
        lia. }
      destruct (Hchain Hbnd) as [Heq [Hrz_bnd Hhi_bnd]].
      (* Identify the chain's [r_z] with [N - r0]. *)
      change (2 ^ 64) with B in Heq, Hrz_bnd, Hhi_bnd.
      fold t0 t1 t2 t3 in Heq, Hrz_bnd, Hhi_bnd.
      set (rz := t0 mod B + t1 mod B * B + t2 mod B * (B * B) + t3 mod B * (B * B * B)) in *.
      set (hi := t3 / B) in *.
      change (2 ^ 64) with B in Hval.
      rewrite Hval, HC in Heq.
      assert (Hrz_eq : rz = secp256k1_N - r0).
      { assert (HB4 : B * B * B * B = 2^256) by (subst B; reflexivity).
        rewrite HB4 in Heq, Hrz_bnd.
        unfold secp256k1_N in *.
        lia. }
      (* Extract the per-limb values via [limbs_eval4]. *)
      pose proof (limbs_eval4 B (t0 mod B) (t1 mod B) (t2 mod B) (t3 mod B)
        ltac:(subst B; lia)
        ltac:(apply Z.mod_pos_bound; subst B; lia)
        ltac:(apply Z.mod_pos_bound; subst B; lia)
        ltac:(apply Z.mod_pos_bound; subst B; lia)
        ltac:(apply Z.mod_pos_bound; subst B; lia)) as [Hl0 [Hl1 [Hl2 Hl3]]].
      unfold eval4 in Hl0, Hl1, Hl2, Hl3.
      replace (B^2) with (B * B) in Hl0, Hl1, Hl2, Hl3 by ring.
      replace (B^3) with (B * B * B) in Hl0, Hl1, Hl2, Hl3 by ring.
      fold rz in Hl0, Hl1, Hl2, Hl3.
      rewrite Hrz_eq in Hl0, Hl1, Hl2, Hl3.
      unfold limb in Hl0, Hl1, Hl2, Hl3.
      simpl Z.of_nat in Hl0, Hl1, Hl2, Hl3.
      rewrite Z.pow_0_r, Z.div_1_r, Z.pow_1_r in *.
      replace (B^2) with (2^128) in Hl2 by (subst B; reflexivity).
      replace (B^3) with (2^192) in Hl3 by (subst B; reflexivity).
      repeat split.
      * exact (eq_sym Hl0).
      * exact (eq_sym Hl1).
      * exact (eq_sym Hl2).
      * exact (eq_sym Hl3).
Qed.
