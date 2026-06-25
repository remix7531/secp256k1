(** * verif.modinv.impl.modinv64_normalize_62: body proof for secp256k1_modinv64_normalize_62. *)
(** Copyright (C) 2026 remix7531
    Ported from BlockstreamResearch/simplicity Coq/C/secp256k1/verif_modinv64_impl.v
    (commit c1dddedd), Copyright (c) 2018 Blockstream, originally MIT.
    Upstream notice reproduced in proof/README.md.
    SPDX-License-Identifier: MIT *)

(** Split out from the upstream-ported verif_modinv64_impl.v (one semax_body
    per file, per the project convention). *)

Require Import secp256k1.vst.base.
Require Import secp256k1.contract.impl.modinv.
Require Import secp256k1.contract.gprog.modinv.
Require Import secp256k1.theory.extra_math.
Require Import secp256k1.tactics.core.
Require Import secp256k1.tactics.hygiene.

(* ================================================================= *)
(** ** secp256k1_modinv64_normalize_62 -- conditional negate + reduce into [[0, m)]. *)

(** [secp256k1_modinv64_normalize_62(r, sign, modinfo)] takes a signed62 [r] in
    range (-2*modulus, modulus) with limbs in (-2^62, 2^62), and adds modulus
    multiples (conditionally negating when [sign < 0]) to land in [0, modulus).
    Postcondition: [r := (if sign < 0 then -r else r) mod m].

    Proof shape: the C body is two passes over the five limbs.  Pass 1 adds the
    modulus when [r < 0], negates when [sign < 0], and propagates the top bits;
    the resulting limbs are recombined into the closed form [s], which lies in
    (-m, m).  Pass 2 adds the modulus once more when [s < 0] and propagates
    again; that recombines into [t = (if sign < 0 then -r else r) mod m], which
    the five stores write back.

    The [Htc_*] hypotheses posed up front are stated in exactly the shape
    [forward]'s int64 type-check obligation takes for an interior limb, so the
    interior limb statements need no explicit side-goal block; the top-limb
    add (once per pass) and the top-limb negate, whose operand is not a 62-bit
    residue, still do (three explicit blocks in total). *)
Lemma body_secp256k1_modinv64_normalize_62: semax_body Vprog Gprog f_secp256k1_modinv64_normalize_62 spec_secp256k1_modinv64_normalize_62.
Proof.
  start_function.

  (* ===== Setup: input bounds and the mask / type-check vocabulary ===== *)

  rename H into Hm_bnd.
  rename H0 into Hr_lo.
  rename H1 into Hr_bnd.
  rename H2 into Hsign_bnd.

  assert (H5r := Signed62.reprn_Zlength 5 r).
  assert (H5m := Signed62.reprn_Zlength 5 m).

  (* the top limbs of r and of the modulus (the only ones not reduced mod 2^62) *)
  assert (Hr4 : - (2 ^ 62 - 1) <= Z.shiftr r 248 < 2 ^ 62) by (apply shiftr_bounds; lia).
  assert (Hm4 : 0 <= Z.shiftr m 248 < 2 ^ 62) by (apply shiftr_bounds; lia).
  pose proof mod62_range as Hmod62.

  (* Pure-Z mask vocabulary ([theory/bits.v]), posed under the names the rest of
     this proof rewrites with: [Hmask] turns an arithmetic shift that lands in
     [-1, 0] into the sign of its operand, and [Hand] / [Hxor] / [Hsub] evaluate
     the three masked operations on that sign. *)
  pose proof shiftr_sign_mask_eq as Hmask.
  pose proof land_sign_mask_eq as Hand.
  pose proof lxor_sign_mask_eq as Hxor.
  pose proof sub_sign_mask_eq as Hsub.

  (* The five int64 type-check shapes of the C body ([vst/integers.v]): the
     generic [+ (x & mask)], [(x ^ mask) - mask] and [x + (y >> 62)] range
     facts, and the two interior-limb specializations.  They are posed here, in
     exactly the shape [forward]'s type-check obligation takes, so the interior
     limb statements need no explicit side-goal block (52 silent discharges);
     the top-limb add and the top-limb negate, whose operand is not a 62-bit
     residue, still get one. *)
  pose proof Int64_add_mask_range as Htc_add.
  pose proof Int64_xor_sub_mask_range as Htc_neg.
  pose proof Int64_add_shr_range as Htc_prop.
  pose proof Int64_add_mask_mod62_range as Htc_add_mid.
  pose proof Int64_xor_sub_mask_mod62_range as Htc_neg_mid.

  (* ===== Load: M62 and the five input limbs r0..r4 ===== *)

  (* const int64_t M62 = (int64_t)(UINT64_MAX >> 2) *)
  forward.
  change (Int64.shru (Int64.repr (-1)) (Int64.repr (Int.unsigned (Int.repr 2))))
    with (Int64.repr (Z.ones 62)).

  (* int64_t r0 = r->v[0] -- VERIFY-off: no per-limb range-check loop in the AST *)
  forward.
  (* int64_t r1 = r->v[1] *)
  forward.
  (* int64_t r2 = r->v[2] *)
  forward.
  (* int64_t r3 = r->v[3] *)
  forward.
  (* int64_t r4 = r->v[4] *)
  forward.

  (* Expose the modinfo limbs for the conditional adds below. (VERIFY-off: the
     two input range checks r > -2*modulus / r < modulus are not in the AST.) *)
  unfold make_modinfo.

  (* ===== Pass 1: cond_add (r < 0), then cond_negate (sign < 0) ===== *)

  (* cond_add = r4 >> 63 -- the all-ones mask iff r < 0 *)
  forward.
  replace 4 with (Zlength (Signed62.reprn 5 r) - 1) by (rewrite Signed62.reprn_Zlength; reflexivity).
  rewrite Znth_last.
  rewrite Signed62.reprn_last by lia.
  repeat (rewrite Signed62.reprn_Znth by lia).
  change (62 * (Z.of_nat 5 - 1)) with 248.
  autorewrite with int_to_z.
  rewrite Int64.signed_repr by rep_lia.
  change (Int64.unsigned (Int64.repr (Int.unsigned (Int.repr 63)))) with 63.
  rewrite Z.shiftr_shiftr by lia.
  change (248 + 63) with 311.
  assert (Hr311 : -1 <= Z.shiftr r 311 < 1) by (apply shiftr_bounds; lia).
  rewrite (Hmask r 311) by lia.

  (* _t'10 = modinfo->modulus.v[0] *)
  forward.
  rewrite Signed62.reprn_Znth by lia.

  (* r0 += _t'10 & cond_add *)
  forward.

  (* _t'9 = modinfo->modulus.v[1] *)
  forward.
  rewrite Signed62.reprn_Znth by lia.

  (* r1 += _t'9 & cond_add *)
  forward.

  (* _t'8 = modinfo->modulus.v[2] *)
  forward.
  rewrite Signed62.reprn_Znth by lia.

  (* r2 += _t'8 & cond_add *)
  forward.

  (* _t'7 = modinfo->modulus.v[3] *)
  forward.
  rewrite Signed62.reprn_Znth by lia.

  (* r3 += _t'7 & cond_add *)
  forward.

  (* _t'6 = modinfo->modulus.v[4] *)
  forward.
  change 4 with (Zlength (Signed62.reprn 5 m) - 1).
  rewrite Znth_last.
  rewrite Signed62.reprn_last by lia.
  change (62 * (Z.of_nat 5 - 1)) with 248.

  (* r4 += _t'6 & cond_add *)
  forward.
  { (* tc: the top-limb add stays inside int64 *)
    entailer!!.
    rewrite Hand.
    rewrite Int64.signed_repr by (destruct (r <? 0); rep_lia).
    destruct (r <? 0); rep_lia. }

  autorewrite with int_to_z.
  rewrite !Hand.

  (* cond_negate = sign >> 63 -- the all-ones mask iff sign < 0 *)
  forward.
  autorewrite with int_to_z.
  rewrite Int64.signed_repr by rep_lia.
  change (Int64.unsigned (Int64.repr (Int.unsigned (Int.repr 63)))) with 63.
  assert (Hs63 : -1 <= Z.shiftr sign 63 < 1) by (apply shiftr_bounds; rep_lia).
  rewrite (Hmask sign 63) by lia.

  (* r0 = (r0 ^ cond_negate) - cond_negate *)
  forward.

  (* r1 = (r1 ^ cond_negate) - cond_negate *)
  forward.

  (* r2 = (r2 ^ cond_negate) - cond_negate *)
  forward.

  (* r3 = (r3 ^ cond_negate) - cond_negate *)
  forward.

  (* r4 = (r4 ^ cond_negate) - cond_negate *)
  forward.
  { (* tc: the top-limb negate stays inside int64 *)
    entailer!!.
    apply Htc_neg.
    destruct (r <? 0); lia. }

  autorewrite with int_to_z.
  rewrite !Hxor.
  rewrite !Hsub.

  (* Name the five limbs after the conditional add and negate. *)
  set (s4 := if sign <? 0 then _ else _).
  set (s3 := if sign <? 0 then _ else _).
  set (s2 := if sign <? 0 then _ else _).
  set (s1 := if sign <? 0 then _ else _).
  set (s0 := if sign <? 0 then _ else _).

  assert (Hs0 : - 2 ^ 63 + 2 <= s0 <= 2 ^ 63 - 2).
  { unfold s0.
    pose proof (Hmod62 (Z.shiftr r (62 * 0))).
    pose proof (Hmod62 (Z.shiftr m (62 * 0))).
    destruct (sign <? 0); destruct (r <? 0); lia. }

  assert (Hs1 : - 2 ^ 63 + 2 <= s1 <= 2 ^ 63 - 2).
  { unfold s1.
    pose proof (Hmod62 (Z.shiftr r (62 * 1))).
    pose proof (Hmod62 (Z.shiftr m (62 * 1))).
    destruct (sign <? 0); destruct (r <? 0); lia. }

  assert (Hs2 : - 2 ^ 63 + 2 <= s2 <= 2 ^ 63 - 2).
  { unfold s2.
    pose proof (Hmod62 (Z.shiftr r (62 * 2))).
    pose proof (Hmod62 (Z.shiftr m (62 * 2))).
    destruct (sign <? 0); destruct (r <? 0); lia. }

  assert (Hs3 : - 2 ^ 63 + 2 <= s3 <= 2 ^ 63 - 2).
  { unfold s3.
    pose proof (Hmod62 (Z.shiftr r (62 * 3))).
    pose proof (Hmod62 (Z.shiftr m (62 * 3))).
    destruct (sign <? 0); destruct (r <? 0); lia. }

  assert (Hs4 : - 2 ^ 63 + 2 <= s4 <= 2 ^ 63 - 2).
  { unfold s4.
    destruct (sign <? 0); destruct (r <? 0); lia. }

  assert (Hp0 : - 2 ^ 63 <= s0 <= 2 ^ 63 - 1) by lia.

  (* ===== Pass 1 carry propagation: ri+1 += ri >> 62; ri &= M62 ===== *)

  (* r1 += r0 >> 62 *)
  forward.
  autorewrite with int_to_z.
  change (Int64.unsigned (Int64.repr (Int.unsigned (Int.repr 62)))) with 62.
  rewrite Int64.signed_repr by rep_lia.
  assert (Hp1 : - 2 ^ 63 <= s1 + Z.shiftr s0 62 <= 2 ^ 63 - 1).
  { assert (Hc : -2 <= Z.shiftr s0 62 < 2) by (apply shiftr_bounds; lia).
    lia. }

  (* r0 &= M62 *)
  forward.
  autorewrite with int_to_z.
  rewrite Z.land_ones by lia.

  (* r2 += r1 >> 62 *)
  forward.
  autorewrite with int_to_z.
  change (Int64.unsigned (Int64.repr (Int.unsigned (Int.repr 62)))) with 62.
  rewrite Int64.signed_repr by rep_lia.
  assert (Hp2 : - 2 ^ 63 <= s2 + Z.shiftr (s1 + Z.shiftr s0 62) 62 <= 2 ^ 63 - 1).
  { assert (Hc : -2 <= Z.shiftr (s1 + Z.shiftr s0 62) 62 < 2) by (apply shiftr_bounds; lia).
    lia. }

  (* r1 &= M62 *)
  forward.
  autorewrite with int_to_z.
  rewrite Z.land_ones by lia.

  (* r3 += r2 >> 62 *)
  forward.
  autorewrite with int_to_z.
  change (Int64.unsigned (Int64.repr (Int.unsigned (Int.repr 62)))) with 62.
  rewrite Int64.signed_repr by rep_lia.
  assert (Hp3 : - 2 ^ 63 <= s3 + Z.shiftr (s2 + Z.shiftr (s1 + Z.shiftr s0 62) 62) 62 <= 2 ^ 63 - 1).
  { assert (Hc : -2 <= Z.shiftr (s2 + Z.shiftr (s1 + Z.shiftr s0 62) 62) 62 < 2)
      by (apply shiftr_bounds; lia).
    lia. }

  (* r2 &= M62 *)
  forward.
  autorewrite with int_to_z.
  rewrite Z.land_ones by lia.

  (* r4 += r3 >> 62 *)
  forward.
  autorewrite with int_to_z.
  change (Int64.unsigned (Int64.repr (Int.unsigned (Int.repr 62)))) with 62.
  rewrite Int64.signed_repr by rep_lia.

  (* r3 &= M62 *)
  forward.
  autorewrite with int_to_z.
  rewrite Z.land_ones by lia.

  (* ===== Pass 1 recombination: the five limbs denote s, now in (-m, m) ===== *)

  pose (s' := s0 + s1 * 2 ^ 62 + s2 * 2 ^ 62 * 2 ^ 62 + s3 * 2 ^ 62 * 2 ^ 62 * 2 ^ 62
        + s4 * 2 ^ 62 * 2 ^ 62 * 2 ^ 62 * 2 ^ 62).

  assert (Hrec4 : Z.shiftr s' (62 * 4) =
                  s4 + Z.shiftr (s3 + Z.shiftr (s2 + Z.shiftr (s1 + Z.shiftr s0 62) 62) 62) 62).
  { rewrite !Z.shiftr_div_pow2 by lia.
    rewrite !(Z.add_comm _ (_ / _)).
    rewrite <- !Z_div_plus by lia.
    rewrite !Zdiv_Zdiv by lia.
    reflexivity. }
  rewrite <- Hrec4.

  assert (Hrec3 : Z.shiftr s' (62 * 3) mod 2 ^ 62 =
                  (s3 + Z.shiftr (s2 + Z.shiftr (s1 + Z.shiftr s0 62) 62) 62) mod 2 ^ 62).
  { rewrite !Z.shiftr_div_pow2 by lia.
    rewrite !(Z.add_comm _ (_ / _)).
    rewrite <- !Z_div_plus by lia.
    rewrite !Zdiv_Zdiv by lia.
    unfold s'.
    rewrite <- !Z.mul_assoc.
    change (2 ^ 62 * (2 ^ 62 * 2 ^ 62)) with (2 ^ (62 * 3)).
    rewrite !Z.mul_assoc.
    rewrite !Z_div_plus_full by lia.
    rewrite !Z_mod_plus_full.
    reflexivity. }
  rewrite <- Hrec3.

  assert (Hrec2 : Z.shiftr s' (62 * 2) mod 2 ^ 62 =
                  (s2 + Z.shiftr (s1 + Z.shiftr s0 62) 62) mod 2 ^ 62).
  { rewrite !Z.shiftr_div_pow2 by lia.
    rewrite !(Z.add_comm _ (_ / _)).
    rewrite <- !Z_div_plus by lia.
    rewrite !Zdiv_Zdiv by lia.
    unfold s'.
    rewrite <- !Z.mul_assoc.
    change (2 ^ 62 * 2 ^ 62) with (2 ^ (62 * 2)).
    rewrite !Z.mul_assoc.
    rewrite !Z_div_plus_full by lia.
    rewrite !Z_mod_plus_full.
    reflexivity. }
  rewrite <- Hrec2.

  assert (Hrec1 : Z.shiftr s' (62 * 1) mod 2 ^ 62 = (s1 + Z.shiftr s0 62) mod 2 ^ 62).
  { rewrite !Z.shiftr_div_pow2 by lia.
    rewrite !(Z.add_comm _ (_ / _)).
    rewrite <- !Z_div_plus by lia.
    unfold s'.
    rewrite Z.mul_1_r.
    rewrite !Z_div_plus_full by lia.
    rewrite !Z_mod_plus_full.
    reflexivity. }
  rewrite <- Hrec1.

  assert (Hrec0 : Z.shiftr s' (62 * 0) mod 2 ^ 62 = s0 mod 2 ^ 62).
  { change (Z.shiftr s' (62 * 0)) with s'.
    unfold s'.
    rewrite !Z_mod_plus_full.
    reflexivity. }
  rewrite <- Hrec0.

  pose (s := if sign <? 0 then - (r + if r <? 0 then m else 0) else r + if r <? 0 then m else 0).
  assert (Hs' : s = s').
  { unfold s, s'.
    destruct (sign <? 0) in *;
      destruct (r <? 0) in *;
      change r with (Z.shiftr r 0);
      change m with (Z.shiftr m 0);
      do 4 rewrite (Z_div_mod_eq (Z.shiftr r _) (2 ^ 62)), <- Z.shiftr_div_pow2, Z.shiftr_shiftr by lia;
      try do 4 rewrite (Z_div_mod_eq (Z.shiftr m _) (2 ^ 62)), <- Z.shiftr_div_pow2, Z.shiftr_shiftr by lia;
      unfold s0, s1, s2, s3, s4;
      cbn;
      ring. }
  rewrite <- Hs'.
  clear Hrec4 Hrec3 Hrec2 Hrec1 Hrec0 Hs' s' Hp0 Hp1 Hp2 Hp3 Hs0 Hs1 Hs2 Hs3 Hs4 s0 s1 s2 s3 s4.
  change (62 * 4) with 248.

  (* ===== Pass 2: cond_add again if s is still negative ===== *)

  assert (Hs_rng : - m < s < m).
  { unfold s.
    destruct (Z.ltb_spec r 0); destruct (Z.ltb_spec sign 0); lia. }
  assert (Hs_top : - (2 ^ 62 - 1) <= Z.shiftr s 248 < 2 ^ 62) by (apply shiftr_bounds; lia).

  (* cond_add = r4 >> 63 -- the all-ones mask iff s < 0 *)
  forward.
  autorewrite with int_to_z.
  rewrite Int64.signed_repr by rep_lia.
  change (Int64.unsigned (Int64.repr (Int.unsigned (Int.repr 63)))) with 63.
  rewrite Z.shiftr_shiftr by lia.
  change (248 + 63) with 311.
  assert (Hs311 : -1 <= Z.shiftr s 311 < 1) by (apply shiftr_bounds; lia).
  rewrite (Hmask s 311) by lia.

  (* _t'5 = modinfo->modulus.v[0] *)
  forward.
  rewrite Signed62.reprn_Znth by lia.

  (* r0 += _t'5 & cond_add *)
  forward.

  (* _t'4 = modinfo->modulus.v[1] *)
  forward.
  rewrite Signed62.reprn_Znth by lia.

  (* r1 += _t'4 & cond_add *)
  forward.

  (* _t'3 = modinfo->modulus.v[2] *)
  forward.
  rewrite Signed62.reprn_Znth by lia.

  (* r2 += _t'3 & cond_add *)
  forward.

  (* _t'2 = modinfo->modulus.v[3] *)
  forward.
  rewrite Signed62.reprn_Znth by lia.

  (* r3 += _t'2 & cond_add *)
  forward.

  (* _t'1 = modinfo->modulus.v[4] *)
  forward.
  change 4 with (Zlength (Signed62.reprn 5 m) - 1).
  rewrite Znth_last.
  rewrite Signed62.reprn_last by lia.
  change (62 * (Z.of_nat 5 - 1)) with 248.

  (* r4 += _t'1 & cond_add *)
  forward.
  { (* tc: the top-limb add stays inside int64 *)
    entailer!!.
    rewrite Hand.
    rewrite Int64.signed_repr by (destruct (s <? 0); rep_lia).
    destruct (s <? 0); rep_lia. }

  autorewrite with int_to_z.
  rewrite !Hand.

  (* Name the five limbs after the second conditional add. *)
  set (t4 := Z.shiftr s 248 + _).
  set (t3 := _ mod _ + _).
  set (t2 := _ mod _ + _).
  set (t1 := _ mod _ + _).
  set (t0 := _ mod _ + _).

  assert (Ht0 : - 2 ^ 63 + 2 <= t0 <= 2 ^ 63 - 2).
  { unfold t0.
    pose proof (Hmod62 (Z.shiftr s (62 * 0))).
    pose proof (Hmod62 (Z.shiftr m (62 * 0))).
    destruct (s <? 0); lia. }

  assert (Ht1 : - 2 ^ 63 + 2 <= t1 <= 2 ^ 63 - 2).
  { unfold t1.
    pose proof (Hmod62 (Z.shiftr s (62 * 1))).
    pose proof (Hmod62 (Z.shiftr m (62 * 1))).
    destruct (s <? 0); lia. }

  assert (Ht2 : - 2 ^ 63 + 2 <= t2 <= 2 ^ 63 - 2).
  { unfold t2.
    pose proof (Hmod62 (Z.shiftr s (62 * 2))).
    pose proof (Hmod62 (Z.shiftr m (62 * 2))).
    destruct (s <? 0); lia. }

  assert (Ht3 : - 2 ^ 63 + 2 <= t3 <= 2 ^ 63 - 2).
  { unfold t3.
    pose proof (Hmod62 (Z.shiftr s (62 * 3))).
    pose proof (Hmod62 (Z.shiftr m (62 * 3))).
    destruct (s <? 0); lia. }

  assert (Ht4 : - 2 ^ 63 + 2 <= t4 <= 2 ^ 63 - 2).
  { unfold t4.
    destruct (s <? 0); lia. }

  assert (Hq0 : - 2 ^ 63 <= t0 <= 2 ^ 63 - 1) by lia.

  (* ===== Pass 2 carry propagation: ri+1 += ri >> 62; ri &= M62 ===== *)

  (* r1 += r0 >> 62 *)
  forward.
  autorewrite with int_to_z.
  change (Int64.unsigned (Int64.repr (Int.unsigned (Int.repr 62)))) with 62.
  rewrite Int64.signed_repr by rep_lia.
  assert (Hq1 : - 2 ^ 63 <= t1 + Z.shiftr t0 62 <= 2 ^ 63 - 1).
  { assert (Hc : -2 <= Z.shiftr t0 62 < 2) by (apply shiftr_bounds; lia).
    lia. }

  (* r0 &= M62 *)
  forward.
  autorewrite with int_to_z.
  rewrite Z.land_ones by lia.

  (* r2 += r1 >> 62 *)
  forward.
  autorewrite with int_to_z.
  change (Int64.unsigned (Int64.repr (Int.unsigned (Int.repr 62)))) with 62.
  rewrite Int64.signed_repr by rep_lia.
  assert (Hq2 : - 2 ^ 63 <= t2 + Z.shiftr (t1 + Z.shiftr t0 62) 62 <= 2 ^ 63 - 1).
  { assert (Hc : -2 <= Z.shiftr (t1 + Z.shiftr t0 62) 62 < 2) by (apply shiftr_bounds; lia).
    lia. }

  (* r1 &= M62 *)
  forward.
  autorewrite with int_to_z.
  rewrite Z.land_ones by lia.

  (* r3 += r2 >> 62 *)
  forward.
  autorewrite with int_to_z.
  change (Int64.unsigned (Int64.repr (Int.unsigned (Int.repr 62)))) with 62.
  rewrite Int64.signed_repr by rep_lia.
  assert (Hq3 : - 2 ^ 63 <= t3 + Z.shiftr (t2 + Z.shiftr (t1 + Z.shiftr t0 62) 62) 62 <= 2 ^ 63 - 1).
  { assert (Hc : -2 <= Z.shiftr (t2 + Z.shiftr (t1 + Z.shiftr t0 62) 62) 62 < 2)
      by (apply shiftr_bounds; lia).
    lia. }

  (* r2 &= M62 *)
  forward.
  autorewrite with int_to_z.
  rewrite Z.land_ones by lia.

  (* r4 += r3 >> 62 *)
  forward.
  autorewrite with int_to_z.
  change (Int64.unsigned (Int64.repr (Int.unsigned (Int.repr 62)))) with 62.
  rewrite Int64.signed_repr by rep_lia.

  (* r3 &= M62 *)
  forward.
  autorewrite with int_to_z.
  rewrite Z.land_ones by lia.

  (* ===== Pass 2 recombination: the five limbs denote the postcondition value ===== *)

  pose (t' := t0 + t1 * 2 ^ 62 + t2 * 2 ^ 62 * 2 ^ 62 + t3 * 2 ^ 62 * 2 ^ 62 * 2 ^ 62
        + t4 * 2 ^ 62 * 2 ^ 62 * 2 ^ 62 * 2 ^ 62).

  assert (Hrec4 : Z.shiftr t' (62 * 4) =
                  t4 + Z.shiftr (t3 + Z.shiftr (t2 + Z.shiftr (t1 + Z.shiftr t0 62) 62) 62) 62).
  { rewrite !Z.shiftr_div_pow2 by lia.
    rewrite !(Z.add_comm _ (_ / _)).
    rewrite <- !Z_div_plus by lia.
    rewrite !Zdiv_Zdiv by lia.
    reflexivity. }
  rewrite <- Hrec4.

  assert (Hrec3 : Z.shiftr t' (62 * 3) mod 2 ^ 62 =
                  (t3 + Z.shiftr (t2 + Z.shiftr (t1 + Z.shiftr t0 62) 62) 62) mod 2 ^ 62).
  { rewrite !Z.shiftr_div_pow2 by lia.
    rewrite !(Z.add_comm _ (_ / _)).
    rewrite <- !Z_div_plus by lia.
    rewrite !Zdiv_Zdiv by lia.
    unfold t'.
    rewrite <- !Z.mul_assoc.
    change (2 ^ 62 * (2 ^ 62 * 2 ^ 62)) with (2 ^ (62 * 3)).
    rewrite !Z.mul_assoc.
    rewrite !Z_div_plus_full by lia.
    rewrite !Z_mod_plus_full.
    reflexivity. }
  rewrite <- Hrec3.

  assert (Hrec2 : Z.shiftr t' (62 * 2) mod 2 ^ 62 =
                  (t2 + Z.shiftr (t1 + Z.shiftr t0 62) 62) mod 2 ^ 62).
  { rewrite !Z.shiftr_div_pow2 by lia.
    rewrite !(Z.add_comm _ (_ / _)).
    rewrite <- !Z_div_plus by lia.
    rewrite !Zdiv_Zdiv by lia.
    unfold t'.
    rewrite <- !Z.mul_assoc.
    change (2 ^ 62 * 2 ^ 62) with (2 ^ (62 * 2)).
    rewrite !Z.mul_assoc.
    rewrite !Z_div_plus_full by lia.
    rewrite !Z_mod_plus_full.
    reflexivity. }
  rewrite <- Hrec2.

  assert (Hrec1 : Z.shiftr t' (62 * 1) mod 2 ^ 62 = (t1 + Z.shiftr t0 62) mod 2 ^ 62).
  { rewrite !Z.shiftr_div_pow2 by lia.
    rewrite !(Z.add_comm _ (_ / _)).
    rewrite <- !Z_div_plus by lia.
    unfold t'.
    rewrite Z.mul_1_r.
    rewrite !Z_div_plus_full by lia.
    rewrite !Z_mod_plus_full.
    reflexivity. }
  rewrite <- Hrec1.

  assert (Hrec0 : Z.shiftr t' (62 * 0) mod 2 ^ 62 = t0 mod 2 ^ 62).
  { change (Z.shiftr t' (62 * 0)) with t'.
    unfold t'.
    rewrite !Z_mod_plus_full.
    reflexivity. }
  rewrite <- Hrec0.

  pose (t := (if sign <? 0 then - r else r) mod m).
  assert (Ht' : t = t').
  { transitivity (if s <? 0 then s + m else s).
    - (* the final conditional add lands in [0, m) and is congruent to +-r *)
      unfold t.
      apply Zdivide_mod_minus.
      + (* it lies in [0, m), since s lies in (-m, m) *)
        destruct (Z.ltb_spec s 0); lia.
      + (* it differs from (if sign < 0 then -r else r) by a multiple of m *)
        unfold s.
        destruct (sign <? 0); destruct (r <? 0); destruct (_ <? 0);
          solve [ exists 0; ring | exists 1; ring | exists (-1); ring | exists (-2); ring ].
    - (* the conditional add is exactly the limb recombination t' *)
      unfold t'.
      destruct (s <? 0) in *;
        change s with (Z.shiftr s 0);
        change m with (Z.shiftr m 0);
        do 4 rewrite (Z_div_mod_eq (Z.shiftr s _) (2 ^ 62)), <- Z.shiftr_div_pow2, Z.shiftr_shiftr by lia;
        try do 4 rewrite (Z_div_mod_eq (Z.shiftr m _) (2 ^ 62)), <- Z.shiftr_div_pow2, Z.shiftr_shiftr by lia;
        unfold t0, t1, t2, t3, t4;
        cbn;
        ring. }
  rewrite <- Ht'.
  clear Hrec4 Hrec3 Hrec2 Hrec1 Hrec0 Ht' t' Hq0 Hq1 Hq2 Hq3 Ht0 Ht1 Ht2 Ht3 Ht4 t0 t1 t2 t3 t4.

  (* ===== Store back: r->v[i] = ri, closing the postcondition. (VERIFY-off:
     the per-limb [ri >> 62 == 0] checks and the two output range checks
     r >= 0 / r < modulus that followed the stores are not in the AST.) ===== *)

  (* r->v[0] = r0 *)
  forward.

  (* r->v[1] = r1 *)
  forward.

  (* r->v[2] = r2 *)
  forward.

  (* r->v[3] = r3 *)
  forward.

  (* r->v[4] = r4 *)
  forward.
  entailer!!.
Qed.
