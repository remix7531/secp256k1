(** * verif.scalar.scalar_to_signed62: body proof for secp256k1_scalar_to_signed62 *)
(** Copyright (C) 2026 remix7531
    SPDX-License-Identifier: MIT *)

Require Import secp256k1.vst.base.
Require Import secp256k1.vst.integers.
Require Import secp256k1.contract.impl.modinv.
Require Import secp256k1.contract.impl.scalar.
Require Import secp256k1.contract.gprog.scalar.
Require Import secp256k1.theory.limb_window.

(* ================================================================= *)
(** ** secp256k1_scalar_to_signed62 -- 4-limb scalar -> 5-limb signed62. *)

(** Repack the scalar into 62-bit little-endian limbs; the stored result is
    [reprn 5 (scalar_val a)].  The spec + Gprog live in contract/modinv.v (the
    Signed62 owner).

    The C loads the four 64-bit limbs [a0..a3], then writes five 62-bit limbs:
    limb 0 is [a0 & M62], limbs 1..3 each [or] the high bits of one 64-bit limb
    with the low bits of the next (masked to 62 bits), and limb 4 is [a3 >> 56].
    After the five stores [forward] leaves a list equality between the stored
    [upd_Znth] chain and [map Vlong (reprn 5 (scalar_val a))].  The hard part is
    the per-limb bit identities.  The pure-Z window core is the shared
    [lor_disjoint_is_add] (the masked [or] of a low part [< 2^s2] and a
    [2^s2]-aligned high part is their sum) plus [low_aligned_recombine] (that
    sum mod 2^62 is [z mod 2^62]), both in theory/limb_window.v.  The Int64
    glue stays local:
      - [LIMB]: lowers the C [Int64] ops (shru/shl/or/and-with-M62) to [Z].
      - [MID]: the window identity for the three repacking limbs.
    Limbs 0 and 4 are direct mask / shift facts ([He0], [He4]). *)
Lemma body_secp256k1_scalar_to_signed62:
  semax_body Vprog Gprog
    f_secp256k1_scalar_to_signed62 spec_secp256k1_scalar_to_signed62.
Proof.
  start_function.

  (* ===== Stage 0: mask constant + load the four 64-bit limbs ===== *)
  (* _M62 = (uint64_t)(-1) >> 2 = 2^62 - 1 *)
  forward.
  forward. (* _a0 = a->d[0] *)
  forward. (* _a1 = a->d[1] *)
  forward. (* _a2 = a->d[2] *)
  forward. (* _a3 = a->d[3] *)

  (* ===== Stage 1: store the five repacked 62-bit limbs ===== *)
  forward. (* r->v[0] = a0 & M62 *)
  forward. (* r->v[1] = (a0 >> 62 | a1 << 2) & M62 *)
  forward. (* r->v[2] = (a1 >> 60 | a2 << 4) & M62 *)
  forward. (* r->v[3] = (a2 >> 58 | a3 << 6) & M62 *)
  forward. (* r->v[4] = a3 >> 56 *)

  (* ===== Postcondition: stored limbs = reprn 5 (scalar_val a) ===== *)
  (* The scalar is a valid field element, hence below 2^256. *)
  assert (HX : 0 <= types.scalar_val a < 2 ^ 256).
  { pose proof (types.scalar_range a).
    assert (constants.secp256k1_N <= 2 ^ 256) by (unfold constants.secp256k1_N; lia).
    lia. }

  (* Cancel the scalar [data_at]; reduce to the [r] limb-list equality. *)
  entailer!!.
  apply derives_refl'.
  f_equal.

  (* Expand [reprn 5] on the RHS into an explicit five-element list. *)
  cbn [Signed62.reprn map].

  (* ===== Int64 glue lemmas for the per-limb bit identities ===== *)

  (* Lower the C limb expression [(lo >> s1 | hi << s2) & M62] to a [Z] [lor]. *)
  assert (LIMB : forall lo hi s1 s2,
    0 <= lo < 2^64 -> 0 <= hi < 2^64 -> s1 + s2 = 64 -> 0 <= s2 <= 62 ->
    Int64.and
      (Int64.or (Int64.shru (Int64.repr lo) (Int64.repr s1))
                (Int64.shl (Int64.repr hi) (Int64.repr s2)))
      (Int64.shru (Int64.repr (-1)) (Int64.repr 2))
    = Int64.repr (Z.lor (lo / 2^s1) (hi * 2^s2) mod 2^62)).
  { intros lo hi s1 s2 Hlo Hhi Hs Hs2.
    rewrite Int64_shru_shiftr.
    rewrite (Int64_shru_shiftr (Int64.repr (-1))).
    rewrite Int64.shl_mul_two_p.
    rewrite mul64_repr.
    change (Int64.unsigned (Int64.repr (-1))) with (2^64 - 1).
    change (Int64.unsigned (Int64.repr 2)) with 2.
    rewrite (Int64.unsigned_repr lo)
      by (change Int64.max_unsigned with (2^64-1); lia).
    assert (Hs2u : Int64.unsigned (Int64.repr s2) = s2)
      by (rewrite Int64.unsigned_repr;
          [reflexivity | change Int64.max_unsigned with (2^64-1); lia]).
    assert (Hs1u : Int64.unsigned (Int64.repr s1) = s1)
      by (rewrite Int64.unsigned_repr;
          [reflexivity | change Int64.max_unsigned with (2^64-1); lia]).
    rewrite Hs1u, Hs2u.
    rewrite !Z.shiftr_div_pow2 by lia.
    rewrite (two_p_equiv s2).
    change (2^2) with 4.
    change ((2^64-1)/4) with (2^62-1).
    rewrite or64_repr.
    rewrite and64_repr.
    f_equal.
    change (2^62-1) with (Z.ones 62).
    rewrite Z.land_ones by lia.
    reflexivity. }

  (* Window identity for the three repacking limbs (start [w], shift [s2]). *)
  assert (MID : forall X w s2, 0 <= X -> 0 <= w -> 0 <= s2 <= 62 ->
    Int64.and
      (Int64.or
         (Int64.shru (Int64.repr ((X / 2^w) mod 2^64)) (Int64.repr (64 - s2)))
         (Int64.shl (Int64.repr ((X / 2^(w+64)) mod 2^64)) (Int64.repr s2)))
      (Int64.shru (Int64.repr (-1)) (Int64.repr 2))
    = Int64.repr ((X / 2^(w + (64 - s2))) mod 2^62)).
  { intros X w s2 HXp Hw Hs2.
    assert (Hp64 : 0 < 2^64) by (apply Z.pow_pos_nonneg; lia).
    assert (Hps1 : 0 < 2^(64-s2)) by (apply Z.pow_pos_nonneg; lia).
    assert (Hps2 : 0 < 2^s2) by (apply Z.pow_pos_nonneg; lia).
    assert (Hlo : 0 <= (X / 2^w) mod 2^64 < 2^64)
      by (apply Z.mod_pos_bound; lia).
    assert (Hhi : 0 <= (X / 2^(w+64)) mod 2^64 < 2^64)
      by (apply Z.mod_pos_bound; lia).
    rewrite (LIMB _ _ (64 - s2) s2 Hlo Hhi ltac:(lia) Hs2).
    set (z := X / 2^(w + (64 - s2))).
    assert (Bz : 0 <= z) by (apply Z.div_pos; lia).
    assert (Hpow64 : 2^(64 - s2) * 2^s2 = 2^64)
      by (rewrite <- Z.pow_add_r by lia; f_equal; lia).
    assert (B1 : (X / 2^w) mod 2^64 / 2^(64 - s2) = z mod 2^s2).
    { unfold z.
      rewrite <- Hpow64.
      rewrite Zaux.Zdiv_mod_mult by lia.
      rewrite Zdiv.Zdiv_Zdiv by lia.
      rewrite <- Z.pow_add_r by lia.
      reflexivity. }
    assert (B2 : (X / 2^(w+64)) mod 2^64 = (z / 2^s2) mod 2^64).
    { unfold z.
      rewrite Zdiv.Zdiv_Zdiv by lia.
      rewrite <- Z.pow_add_r by lia.
      replace (w + (64 - s2) + s2) with (w + 64) by lia.
      reflexivity. }
    rewrite B1, B2.
    f_equal.
    (* the masked [or] is the disjoint-bit sum ([lor_disjoint_is_add]), and that
       sum mod 2^62 recombines to [z mod 2^62] ([low_aligned_recombine]). *)
    assert (Hlo62 : 0 <= z mod 2 ^ s2 < 2 ^ s2) by (apply Z.mod_pos_bound; lia).
    assert (Hhinn : 0 <= z / 2 ^ s2 mod 2 ^ 64) by (apply Z.mod_pos_bound; lia).
    rewrite (lor_disjoint_is_add (z mod 2 ^ s2) (z / 2 ^ s2 mod 2 ^ 64) s2
               ltac:(lia) Hlo62 Hhinn).
    apply (low_aligned_recombine z s2 64 62 Bz ltac:(lia) ltac:(lia) ltac:(lia)). }

  (* ===== Normalise the goal to explicit divisions ===== *)
  change (Z.pow_pos 2 64) with (2^64).
  change (Z.pow_pos 2 128) with (2^128).
  change (Z.pow_pos 2 192) with (2^192).
  change (Z.pow_pos 2 62) with (2^62).
  set (X := types.scalar_val a) in *.
  fold (Z.div X (2^64)).
  fold (Z.div X (2^128)).
  fold (Z.div X (2^192)).
  rewrite !(Z.shiftr_div_pow2 X 62) by lia.
  rewrite !(Z.shiftr_div_pow2 (X/2^62) 62) by lia.
  rewrite !(Z.shiftr_div_pow2 (X/2^62/2^62) 62) by lia.
  rewrite !(Z.shiftr_div_pow2 (X/2^62/2^62/2^62) 62) by lia.
  rewrite !(Z.div_div X) by lia.
  change (2^62 * 2^62) with (2^124).
  change (2^124 * 2^62) with (2^186).
  change (2^186 * 2^62) with (2^248).

  (* ===== Per-limb equalities, then assemble the list ===== *)

  (* Limb 0: [a0 & M62 = (scalar_val a) mod 2^62]. *)
  assert (He0 : Int64.and (Int64.repr (X mod 2^64))
                  (Int64.shru (Int64.repr (-1)) (Int64.repr 2))
                = Int64.repr (X mod 2^62)).
  { rewrite Int64_shru_shiftr.
    change (Int64.unsigned (Int64.repr (-1))) with (2^64 - 1).
    change (Int64.unsigned (Int64.repr 2)) with 2.
    rewrite and64_repr.
    f_equal.
    rewrite Z.shiftr_div_pow2 by lia.
    change ((2^64-1)/2^2) with (2^62-1).
    change (2^62-1) with (Z.ones 62).
    rewrite Z.land_ones by lia.
    rewrite Z.mod_mod_divide.
    - reflexivity.
    - exists (2^2); reflexivity. }

  (* Limbs 1..3: window identities from [MID] (start [w], shift [s2]). *)
  assert (He1 := MID X 0 2 ltac:(lia) ltac:(lia) ltac:(lia)).
  assert (He2 := MID X 64 4 ltac:(lia) ltac:(lia) ltac:(lia)).
  assert (He3 := MID X 128 6 ltac:(lia) ltac:(lia) ltac:(lia)).
  cbn [Z.add Z.sub] in He1, He2, He3.
  rewrite Z.pow_0_r, Z.div_1_r in He1.
  change (64 - 2) with 62 in He1.
  change (Z.pos (64 + 64)) with 128 in He2.
  change (64 - 4) with 60 in He2.
  change (Z.pos (128 + 64)) with 192 in He3.
  change (64 - 6) with 58 in He3.
  change (0 + 62) with 62 in He1.
  change (64 + 60) with 124 in He2.
  change (128 + 58) with 186 in He3.

  (* Limb 4: [a3 >> 56 = (scalar_val a) >> 248]. *)
  assert (He4 : Int64.shru (Int64.repr ((X / 2^192) mod 2^64)) (Int64.repr 56)
                = Int64.repr (X / 2^248)).
  { rewrite Int64_shru_shiftr.
    assert (Hbnd : 0 <= (X/2^192) mod 2^64 < 2^64)
      by (apply Z.mod_pos_bound; apply Z.pow_pos_nonneg; lia).
    rewrite (Int64.unsigned_repr ((X/2^192) mod 2^64))
      by (change Int64.max_unsigned with (2^64-1); lia).
    change (Int64.unsigned (Int64.repr 56)) with 56.
    rewrite Z.shiftr_div_pow2 by lia.
    f_equal.
    assert (Hsmall : X / 2^192 < 2^64).
    { apply Z.div_lt_upper_bound.
      - apply Z.pow_pos_nonneg; lia.
      - rewrite <- Z.pow_add_r by lia.
        change (192 + 64) with 256.
        lia. }
    assert (Hpos192 : 0 <= X / 2^192)
      by (apply Z.div_pos; [lia | apply Z.pow_pos_nonneg; lia]).
    rewrite (Z.mod_small (X/2^192) (2^64)) by lia.
    rewrite Z.div_div by lia.
    rewrite <- Z.pow_add_r by lia.
    change (192 + 56) with 248.
    reflexivity. }

  (* Assemble the five limbs into the [reprn 5 X] list. *)
  rewrite He0, He1, He2, He3, He4.
  reflexivity.
Qed.
