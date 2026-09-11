(** * vst.scalar.verif.impl.scalar_from_signed62: body proof for secp256k1_scalar_from_signed62 *)
(** Copyright (C) 2026 remix7531
    SPDX-License-Identifier: MIT *)

Require Import secp256k1.vst.base.
Require Import secp256k1.vst.helper.structs_scalar.
Require Import secp256k1.vst.modinv.impl.
Require Import secp256k1.vst.scalar.impl.
Require Import secp256k1.vst.gprog.
Require secp256k1.specification.
Import specification.Math.
Import specification.Math.scalar.
Require Import secp256k1.theory.integers.limb_window.
Require Import secp256k1.theory.integers.bits.

(* ================================================================= *)
(** ** File-local Int64 / Z limb-combine bridges. *)

(** The C cross-limb combine [(lo >> c) | (hi << (62 - c))], as a [Z], is
    [lo / 2^c + (hi mod 2^(c+2)) * 2^(62-c)]: the low piece occupies bits
    [[0, 62-c)] and the high piece bits [[62-c, 64)], so the two ranges are
    disjoint and the [Int64.or] is an addition (the disjoint-OR core is the
    shared [lor_disjoint_is_add], theory/integers/limb_window.v). *)
Lemma from62_comb : forall lo hi c,
  0 <= c <= 62 -> 0 <= lo < 2 ^ 62 -> 0 <= hi < 2 ^ 62 ->
  Int64.or (Int64.shru (Int64.repr lo) (Int64.repr c))
           (Int64.shl (Int64.repr hi) (Int64.repr (62 - c)))
  = Int64.repr (lo / 2 ^ c + (hi mod 2 ^ (c + 2)) * 2 ^ (62 - c)).
Proof.
  intros lo hi c Hc Hlo Hhi.
  assert (Hcm : Int64.unsigned (Int64.repr c) = c) by (apply Int64.unsigned_repr; rep_lia).
  assert (Hcm2 : Int64.unsigned (Int64.repr (62 - c)) = 62 - c)
    by (apply Int64.unsigned_repr; rep_lia).
  rewrite Int64.shru_div_two_p, Hcm, two_p_correct.
  rewrite Int64.shl_mul_two_p, Hcm2, two_p_correct.
  rewrite (Int64.unsigned_repr lo) by rep_lia.
  unfold Int64.mul.
  rewrite (Int64.unsigned_repr hi) by rep_lia.
  assert (H2c : 0 < 2 ^ (62 - c) <= 2 ^ 62)
    by (split; [apply Z.pow_pos_nonneg; lia | apply Z.pow_le_mono_r; lia]).
  rewrite (Int64.unsigned_repr (2 ^ (62 - c))) by rep_lia.
  (* Reduce [hi * 2^(62-c)] modulo [2^64] to [(hi mod 2^(c+2)) * 2^(62-c)]. *)
  assert (Hhipow : 2 ^ (c + 2) * 2 ^ (62 - c) = 2 ^ 64)
    by (rewrite <- Z.pow_add_r by lia; f_equal; lia).
  assert (Hhired : Int64.repr (hi * 2 ^ (62 - c))
                   = Int64.repr ((hi mod 2 ^ (c + 2)) * 2 ^ (62 - c))).
  { apply Int64.eqm_samerepr.
    rewrite (Z_div_mod_eq_full hi (2 ^ (c + 2))) at 1.
    exists (hi / 2 ^ (c + 2)).
    change Int64.modulus with (2 ^ 64).
    rewrite <- Hhipow.
    ring. }
  rewrite Hhired.
  (* The two bit ranges are disjoint, so the OR is addition
     ([lor_disjoint_is_add]): the low piece [lo / 2^c < 2^(62-c)] and the high
     piece is [2^(62-c)]-aligned. *)
  rewrite or64_repr.
  f_equal.
  assert (Hlodiv : 0 <= lo / 2 ^ c < 2 ^ (62 - c)).
  { split; [apply Z.div_pos; [lia | apply Z.pow_pos_nonneg; lia] |].
    apply Z.div_lt_upper_bound; [apply Z.pow_pos_nonneg; lia |].
    rewrite <- Z.pow_add_r by lia.
    replace (c + (62 - c)) with 62 by lia.
    lia. }
  assert (Hhimod : 0 <= hi mod 2 ^ (c + 2))
    by (apply Z.mod_pos_bound; apply Z.pow_pos_nonneg; lia).
  apply (lor_disjoint_is_add (lo / 2 ^ c) (hi mod 2 ^ (c + 2)) (62 - c)
           ltac:(lia) Hlodiv Hhimod).
Qed.

(** The pure-[Z] repack identity [from62_zlimb] -- combining limb 0 of [z]
    (shifted down by [c]) with the wrap-in of limb 1 of [z] reconstructs
    the [64]-bit slice [(z / 2^c) mod 2^64] -- lives in [theory.bits];
    it is instantiated below with [z = x / 2^(62*i)] and [c = 2*i] to
    discharge each of the four scalar limbs. *)

(* ================================================================= *)
(** ** secp256k1_scalar_from_signed62 -- 5-limb signed62 -> 4-limb scalar. *)

(** Repack a normalized signed62 number (value [x] in [[0, N)]) into the
    scalar holding exactly [x].  The C reads the five 62-bit limbs of
    [reprn 5 x] and re-assembles the four 64-bit scalar limbs by the inverse
    shift/OR cascade [r->d[i] = a_i >> 2i | a_{i+1} << (62 - 2i)].  Each store
    matches limb [i] of [scalar_to_val x = (x / 2^(64*i)) mod 2^64] via
    [from62_comb] (the OR is bit-disjoint addition) + [from62_zlimb] (the
    resulting [Z] is the [64]-bit slice). *)
Lemma body_secp256k1_scalar_from_signed62:
  semax_body Vprog Gprog
    f_secp256k1_scalar_from_signed62 spec_secp256k1_scalar_from_signed62.
Proof.
  start_function.

  (* The five signed62 limbs have a fixed length-5 [reprn]. *)
  assert (Hlen : Zlength (Signed62.reprn 5 x) = 5)
    by (rewrite Signed62.reprn_Zlength; reflexivity).

  (* ===== Stage 0: load the five 62-bit limbs a0..a4 ===== *)
  forward. (* a0 = a->v[0] *)
  forward. (* a1 = a->v[1] *)
  forward. (* a2 = a->v[2] *)
  forward. (* a3 = a->v[3] *)
  forward. (* a4 = a->v[4] *)

  (* Keep [forward] from unfolding the shift/mod kernels in the store values. *)
  Arguments Int64.Z_mod_modulus : simpl never.
  Arguments Z.shiftr : simpl never.
  Arguments Z.shiftl : simpl never.

  (* ===== Stage 1: store the four repacked 64-bit limbs ===== *)
  forward. (* r->d[0] = a0      | a1 << 62 *)
  forward. (* r->d[1] = a1 >> 2 | a2 << 60 *)
  forward. (* r->d[2] = a2 >> 4 | a3 << 58 *)
  forward. (* r->d[3] = a3 >> 6 | a4 << 56 *)

  (* ===== Stage 2: the stored scalar is exactly [x] ===== *)
  Exists (mkScalar x H).
  entailer!.

  (* Reduce the postcondition [data_at] to the per-limb list equality. *)
  apply derives_refl'.
  unfold repr.scalar_to_val.
  cbn [scalar_val scalar_reduce].
  f_equal.

  (* Reduce the [Znth] selectors over the literal [reprn 5 x] list. *)
  rewrite !Znth_0_cons, !Znth_pos_cons by lia.
  rewrite !Znth_0_cons, !Znth_pos_cons by lia.
  rewrite !Znth_0_cons, !Znth_pos_cons by lia.
  rewrite !Znth_0_cons, !Znth_pos_cons by lia.
  rewrite !Znth_0_cons by lia.

  (* Collapse the [upd_Znth] chain over [default_val] to the 4-element list. *)
  change (default_val t_secp256k1_scalar) with [Vundef; Vundef; Vundef; Vundef].
  set (w0 := Int64.or (Int64.repr (x mod Z.pow_pos 2 62))
              (Int64.shl (Int64.repr (Z.shiftr x 62 mod Z.pow_pos 2 62)) (Int64.repr 62))).
  set (w1 := Int64.or
              (Int64.shru (Int64.repr (Z.shiftr x 62 mod Z.pow_pos 2 62)) (Int64.repr 2))
              (Int64.shl (Int64.repr (Z.shiftr (Z.shiftr x 62) 62 mod Z.pow_pos 2 62))
                 (Int64.repr 60))).
  set (w2 := Int64.or
              (Int64.shru (Int64.repr (Z.shiftr (Z.shiftr x 62) 62 mod Z.pow_pos 2 62))
                 (Int64.repr 4))
              (Int64.shl
                 (Int64.repr (Z.shiftr (Z.shiftr (Z.shiftr x 62) 62) 62 mod Z.pow_pos 2 62))
                 (Int64.repr 58))).
  set (w3 := Int64.or
              (Int64.shru
                 (Int64.repr (Z.shiftr (Z.shiftr (Z.shiftr x 62) 62) 62 mod Z.pow_pos 2 62))
                 (Int64.repr 6))
              (Int64.shl
                 (Int64.repr (Z.shiftr (Z.shiftr (Z.shiftr (Z.shiftr x 62) 62) 62) 62))
                 (Int64.repr 56))).
  replace (upd_Znth 3 (upd_Znth 2 (upd_Znth 1
             (upd_Znth 0 [Vundef; Vundef; Vundef; Vundef] (Vlong w0)) (Vlong w1))
             (Vlong w2)) (Vlong w3))
    with [Vlong w0; Vlong w1; Vlong w2; Vlong w3] by list_solve.
  unfold w0, w1, w2, w3; clear w0 w1 w2 w3.

  (* Split into the four per-limb identities. *)
  f_equal; [| f_equal; [| f_equal; [| f_equal]]].

  (* branch: limb 0 -- a0 | a1 << 62 = x mod 2^64 *)
  - f_equal.
    rewrite !Z.shiftr_div_pow2 by lia.
    change (Z.pow_pos 2 62) with (2 ^ 62).
    change (Z.pow_pos 2 64) with (2 ^ 64).
    (* phrase the un-shifted low limb as a [shru] by [0] so [from62_comb] (c=0) applies. *)
    rewrite <- (Int64.shru_zero (Int64.repr (x mod 2 ^ 62))).
    change Int64.zero with (Int64.repr 0).
    replace 62 with (62 - 0) at 3 by lia.
    rewrite from62_comb by (try (apply Z.mod_pos_bound; lia); lia).
    f_equal.
    change (62 - 0) with 62.
    change (0 + 2) with 2.
    change (2 ^ 0) with 1.
    rewrite Z.div_1_r.
    rewrite (Z.mod_mod_divide (x / 2 ^ 62) (2 ^ 62) (2 ^ 2)) by (exists (2 ^ 60); reflexivity).
    replace (2 ^ 64) with (2 ^ 2 * 2 ^ 62) by (rewrite <- Z.pow_add_r by lia; reflexivity).
    rewrite (Zmod_recombine x (2 ^ 2) (2 ^ 62)) by lia.
    ring.

  (* branch: limb 1 -- a1 >> 2 | a2 << 60 = (x / 2^64) mod 2^64 *)
  - f_equal.
    rewrite !Z.shiftr_div_pow2 by lia.
    change (Z.pow_pos 2 62) with (2 ^ 62).
    rewrite (from62_comb _ _ 2) by (try (apply Z.mod_pos_bound; lia); lia).
    f_equal.
    pose proof (from62_zlimb (x / 2 ^ 62) 2 ltac:(apply Z.div_pos; lia) ltac:(lia)) as Hz.
    rewrite (Z.div_div x (2 ^ 62) (2 ^ 2)) in Hz by lia.
    change (2 ^ 62 * 2 ^ 2) with (2 ^ 64) in Hz.
    exact Hz.

  (* branch: limb 2 -- a2 >> 4 | a3 << 58 = (x / 2^128) mod 2^64 *)
  - f_equal.
    rewrite !Z.shiftr_div_pow2 by lia.
    change (Z.pow_pos 2 62) with (2 ^ 62).
    rewrite (from62_comb _ _ 4) by (try (apply Z.mod_pos_bound; lia); lia).
    f_equal.
    pose proof (from62_zlimb (x / 2 ^ 124) 4 ltac:(apply Z.div_pos; lia) ltac:(lia)) as Hz.
    rewrite (Z.div_div x (2 ^ 124) (2 ^ 4)) in Hz by lia.
    change (2 ^ 124 * 2 ^ 4) with (2 ^ 128) in Hz.
    rewrite (Z.div_div x (2 ^ 62) (2 ^ 62)) by lia.
    change (2 ^ 62 * 2 ^ 62) with (2 ^ 124).
    exact Hz.

  (* branch: limb 3 -- a3 >> 6 | a4 << 56 = (x / 2^192) mod 2^64 *)
  - f_equal.
    rewrite !Z.shiftr_div_pow2 by lia.
    change (Z.pow_pos 2 62) with (2 ^ 62).
    (* collapse the nested limb divisions to single powers. *)
    rewrite !Z.div_div by lia.
    replace (2 ^ 62 * (2 ^ 62 * 2 ^ 62)) with (2 ^ 186)
      by (rewrite <- !Z.pow_add_r by lia; reflexivity).
    replace (2 ^ 186 * 2 ^ 62) with (2 ^ 248)
      by (rewrite <- Z.pow_add_r by lia; reflexivity).
    (* a4 = x / 2^248 < 2^8, so it is its own [mod 2^62]. *)
    assert (Hx248 : 0 <= x / 2 ^ 248 < 2 ^ 62).
    { split; [apply Z.div_pos; [lia | lia] |].
      apply Z.div_lt_upper_bound; [lia |].
      unfold secp256k1_N in H.
      apply Z.lt_le_trans with (2 ^ 256); [lia |].
      rewrite <- Z.pow_add_r by lia.
      apply Z.pow_le_mono_r; lia. }
    rewrite <- (Z.mod_small (x / 2 ^ 248) (2 ^ 62)) by exact Hx248.
    rewrite (from62_comb _ _ 6) by (try (apply Z.mod_pos_bound; lia); lia).
    f_equal.
    pose proof (from62_zlimb (x / 2 ^ 186) 6 ltac:(apply Z.div_pos; lia) ltac:(lia)) as Hz.
    rewrite (Z.div_div x (2 ^ 186) (2 ^ 6)) in Hz by lia.
    change (2 ^ 186 * 2 ^ 6) with (2 ^ 192) in Hz.
    rewrite (Z.div_div x (2 ^ 186) (2 ^ 62)) in Hz by lia.
    change (2 ^ 186 * 2 ^ 62) with (2 ^ 248) in Hz.
    exact Hz.
Qed.
