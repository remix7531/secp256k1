(** * vst.modinv.verif.impl.modinv64_update_de_62: body proof for secp256k1_modinv64_update_de_62. *)
(** Copyright (C) 2026 remix7531
    Ported from BlockstreamResearch/simplicity Coq/C/secp256k1/verif_modinv64_impl.v
    (commit c1dddedd), Copyright (c) 2018 Blockstream, originally MIT.
    Upstream notice reproduced in proof/README.md.
    SPDX-License-Identifier: MIT *)

(** Split out from the upstream-ported verif_modinv64_impl.v (one semax_body
    per file, per the project convention). *)

Require Import secp256k1.vst.base.
Require Import secp256k1.vst.int128.contract.
Require Import secp256k1.theory.int128.int128.
Require Import secp256k1.vst.helper.notations.
Require Import secp256k1.vst.modinv.impl.
Require Import secp256k1.vst.gprog.
Require Import secp256k1.theory.integers.extra_math.
Require Import secp256k1.theory.integers.bits.
Require Import secp256k1.theory.modinv.construction.inverse.
Require secp256k1.theory.modinv.construction.divstep.
Require secp256k1.theory.modinv.construction.divstep_trans.
Require secp256k1.theory.modinv.construction.divstep_zeta.
Require Import secp256k1.vst.tactics.core.
Require Import secp256k1.vst.tactics.hygiene.

(* ================================================================= *)
(** ** secp256k1_modinv64_update_de_62 -- apply the divstep matrix to [(d,e)] mod [m]. *)

(** [secp256k1_modinv64_update_de_62(d, e, t, modinfo)] applies the 2x2 transition
    matrix [t] to [(d,e)] mod the modulus, producing [divstep_zeta.update_de m d e mtx].
    Each output limb [k] is one [update_de_limb] accumulation block of [u*dn+v*en]
    (and [q*dn+r*en]) plus the [md,me] modulus correction, shifted down 62 bits.

    Under the unified VERIFY-OFF extraction the [VERIFY_CHECK] asserts are
    absent from the AST, so this proof drops the verify blocks (including the
    check that the corrected low limb has 62 zero bottom bits -- the C shifts
    them away either way); the 128-bit accumulators [cd],[ce] are carried as
    model-typed [Int128] records (their running [i128_val] tracked through the
    chain), and every i128 helper call threads its [int128.v] model-typed
    funspec (so each accum/mul/rshift/to_u64 yields a fresh existential to
    [Intros]).

    Proof shape: after the loads, [md,me] are the sign-masked matrix entries
    corrected so that [t*[d,e] + modulus*[md,me]] has 62 zero bottom bits.  The
    body then walks limbs 1..4, each an [update_de_limb] call followed by a
    62-bit store and a down-shift; [Hcarry] is the single carry identity that
    turns one such step into the next window ([mod 2^(n+124)] from
    [mod 2^(n+62)]), and the four instances [Hcd124]/[Hcd186]/[Hcd248]/[Hcd310]
    chain the accumulators up to the full [cd = u*d+v*e+m*md].  The closing
    entailment re-assembles the five stored limbs into [reprn 5 (cd >> 62)] and
    identifies that with [fst (update_de m d e mtx)]. *)
Lemma body_secp256k1_modinv64_update_de_62: semax_body Vprog Gprog f_secp256k1_modinv64_update_de_62 spec_secp256k1_modinv64_update_de_62.
Proof.
  start_function.

  (* ===== Setup: name the input bounds; sign-mask and window vocabulary ===== *)

  rename H into Hodd.
  rename H0 into Hm_bnd.
  rename H1 into Hd_bnd.
  rename H2 into He_bnd.
  destruct H3 as [[Huv _] [Hqr _]].

  (* m odd => 2^n is invertible mod m; the md,me correction below needs it *)
  assert (Hoddm : forall n, 0 <= n -> Z.gcd m (2 ^ n) = 1).
  { intros n Hn; apply gcd_odd_pow2_1; [apply Zodd_equiv, Hodd | exact Hn]. }

  (* The generic window / sign-mask facts ([theory/integers/bits.v]), posed under the
     names the limb blocks below rewrite with. *)
  pose proof mod62_range as Hmod62.
  pose proof land_sign_mask_eq as Hland.

  (* the top limbs of d and e are exact: |d|, |e| < 2*m <= 2^309 *)
  assert (Hd248 : -2 ^ 61 <= Z.shiftr d 248 < 2 ^ 61) by (apply shiftr_bounds; lia).
  assert (He248 : -2 ^ 61 <= Z.shiftr e 248 < 2 ^ 61) by (apply shiftr_bounds; lia).

  (* H311: d4 >> 63 (= d >> 311) collapses to the sign bit, -1 if negative else 0 *)
  assert (H311 : forall x, -2 * m < x < m -> Z.shiftr x 311 = if x <? 0 then -1 else 0).
  { intros x Hx.
    destruct (Z.ltb_spec0 x 0) as [Hx0 | Hx0].
    - (* branch: x < 0 -- the shift lands in [-1, 0) *)
      assert (Hb : -1 <= Z.shiftr x 311 < 0) by (apply shiftr_bounds; lia).
      lia.
    - (* branch: 0 <= x -- the shift lands in [0, 1) *)
      assert (Hb : 0 <= Z.shiftr x 311 < 1) by (apply shiftr_bounds; lia).
      lia. }

  (* ===== Load: M62, the d/e limbs and the matrix entries u,v,q,r ===== *)

  unfold Trans_repr, Signed62.reprn.

  (* const uint64_t M62 = UINT64_MAX >> 2 *)
  forward.

  (* const int64_t d0 = d->v[0] *)
  forward.
  (* const int64_t d1 = d->v[1] *)
  forward.
  (* const int64_t d2 = d->v[2] *)
  forward.
  (* const int64_t d3 = d->v[3] *)
  forward.
  (* const int64_t d4 = d->v[4] *)
  forward.

  (* const int64_t e0 = e->v[0] *)
  forward.
  (* const int64_t e1 = e->v[1] *)
  forward.
  (* const int64_t e2 = e->v[2] *)
  forward.
  (* const int64_t e3 = e->v[3] *)
  forward.
  (* const int64_t e4 = e->v[4] *)
  forward.

  (* const int64_t u = t->u *)
  forward.
  (* const int64_t v = t->v *)
  forward.
  (* const int64_t q = t->q *)
  forward.
  (* const int64_t r = t->r *)
  forward.

  (* normalize the loaded limbs: M62 as a 62-bit mask, and each d/e limb as a
     single window [d >> 62*k] (the nested shifts collapse by [Z.shiftr_shiftr]) *)
  change (Int64.shru (Int64.repr (-1)) (Int64.repr (Int.unsigned (Int.repr 2))))
    with (Int64.repr (Z.ones 62)).
  unfold Znth.
  simpl (Vlong _).
  rewrite !Z.shiftr_shiftr by lia.
  simpl (62 + _).

  (* Expose the modinfo limbs for the modulus loads below. *)
  unfold make_modinfo.

  (* ===== Sign masks: sd = d4 >> 63, se = e4 >> 63; md, me ===== *)

  (* sd = d4 >> 63 *)
  forward.
  (* se = e4 >> 63 *)
  forward.

  autorewrite with int_to_z.
  change (Int64.unsigned (Int64.repr (Int.unsigned (Int.repr 63)))) with 63.
  rewrite !Int64.signed_repr by rep_lia.
  rewrite !Z.shiftr_shiftr by lia.
  change (248 + 63) with 311.
  rewrite !H311 by lia.

  (* md = (u & sd) + (v & se) *)
  forward.
  { (* tc: |u| + |v| <= 2^62, so the masked sum stays inside int64 *)
    entailer!!.
    rewrite !Hland.
    destruct (d <? 0); destruct (e <? 0); rewrite !Int64.signed_repr by rep_lia; rep_lia. }

  autorewrite with int_to_z.
  rewrite !Hland.

  (* me = (q & sd) + (r & se) *)
  forward.
  { (* tc: |q| + |r| <= 2^62, so the masked sum stays inside int64 *)
    entailer!!.
    rewrite !Hland.
    destruct (d <? 0); destruct (e <? 0); rewrite !Int64.signed_repr by rep_lia; rep_lia. }

  autorewrite with int_to_z.
  rewrite !Hland.
  clear H311.

  (* name md0 = u*[d<0] + v*[e<0] and me0 = q*[d<0] + r*[e<0]; bound each by 2^62 *)
  set (md0 := (if d <? 0 then divstep_trans.Trans.u mtx else 0)
              + (if e <? 0 then divstep_trans.Trans.v mtx else 0)) in *.
  set (me0 := (if d <? 0 then divstep_trans.Trans.q mtx else 0)
              + (if e <? 0 then divstep_trans.Trans.r mtx else 0)) in *.
  assert (Hmd0 : -2 ^ 62 <= md0 <= 2 ^ 62) by (unfold md0; destruct (d <? 0); destruct (e <? 0); lia).
  assert (Hme0 : -2 ^ 62 <= me0 <= 2 ^ 62) by (unfold me0; destruct (d <? 0); destruct (e <? 0); lia).

  (* ===== Low limb: cd0 = u*d0 + v*e0, ce0 = q*d0 + r*e0 ===== *)

  (* the bottom windows of d, e, m, and the resulting product bounds *)
  pose proof (Hmod62 d) as Hd62.
  pose proof (Hmod62 e) as He62.
  pose proof (Hmod62 m) as Hm62.

  assert (Hudve : - (2 ^ 62 * (2 ^ 62 - 1))
                  <= divstep_trans.Trans.u mtx * (d mod 2 ^ 62)
                     + divstep_trans.Trans.v mtx * (e mod 2 ^ 62)
                  <= 2 ^ 62 * (2 ^ 62 - 1))
    by (clear -Huv Hd62 He62; nia).
  assert (Hqrve : - (2 ^ 62 * (2 ^ 62 - 1))
                  <= divstep_trans.Trans.q mtx * (d mod 2 ^ 62)
                     + divstep_trans.Trans.r mtx * (e mod 2 ^ 62)
                  <= 2 ^ 62 * (2 ^ 62 - 1))
    by (clear -Hqr Hd62 He62; nia).

  (* model-typed Int64 wrappers for the matrix entries and the bottom d,e limbs *)
  assert (HuB : -2 ^ 63 <= divstep_trans.Trans.u mtx < 2 ^ 63) by lia.
  assert (HvB : -2 ^ 63 <= divstep_trans.Trans.v mtx < 2 ^ 63) by lia.
  assert (HqB : -2 ^ 63 <= divstep_trans.Trans.q mtx < 2 ^ 63) by lia.
  assert (HrB : -2 ^ 63 <= divstep_trans.Trans.r mtx < 2 ^ 63) by lia.
  assert (Hd0B : -2 ^ 63 <= d mod 2 ^ 62 < 2 ^ 63) by lia.
  assert (He0B : -2 ^ 63 <= e mod 2 ^ 62 < 2 ^ 63) by lia.

  set (uI := mkInt64 (divstep_trans.Trans.u mtx) HuB).
  set (vI := mkInt64 (divstep_trans.Trans.v mtx) HvB).
  set (qI := mkInt64 (divstep_trans.Trans.q mtx) HqB).
  set (rI := mkInt64 (divstep_trans.Trans.r mtx) HrB).
  set (d0I := mkInt64 (d mod 2 ^ 62) Hd0B).
  set (e0I := mkInt64 (e mod 2 ^ 62) He0B).

  assert (HuI : i64_val uI = divstep_trans.Trans.u mtx) by reflexivity.
  assert (HvI : i64_val vI = divstep_trans.Trans.v mtx) by reflexivity.
  assert (HqI : i64_val qI = divstep_trans.Trans.q mtx) by reflexivity.
  assert (HrI : i64_val rI = divstep_trans.Trans.r mtx) by reflexivity.
  assert (Hd0I : i64_val d0I = d mod 2 ^ 62) by reflexivity.
  assert (He0I : i64_val e0I = e mod 2 ^ 62) by reflexivity.

  (* secp256k1_i128_mul(&cd, u, d0) *)
  forward_call (v_cd, uI, d0I, Tsh).

  (* secp256k1_i128_accum_mul(&cd, v, e0) *)
  forward_call (v_cd, mul_i64 uI d0I, vI, e0I, Tsh).
  { cbn [i128_val mul_i64].
    rewrite HuI, HvI, Hd0I, He0I.
    lia. }
  Intros Rcd0.
  rename H into Hcd0.
  cbn [i128_val mul_i64] in Hcd0.
  rewrite HuI, HvI, Hd0I, He0I in Hcd0.

  (* secp256k1_i128_mul(&ce, q, d0) *)
  forward_call (v_ce, qI, d0I, Tsh).

  (* secp256k1_i128_accum_mul(&ce, r, e0) *)
  forward_call (v_ce, mul_i64 qI d0I, rI, e0I, Tsh).
  { cbn [i128_val mul_i64].
    rewrite HqI, HrI, Hd0I, He0I.
    lia. }
  Intros Rce0.
  rename H into Hce0.
  cbn [i128_val mul_i64] in Hce0.
  rewrite HqI, HrI, Hd0I, He0I in Hce0.

  (* name cd0 = u*d0+v*e0, ce0 = q*d0+r*e0; both fit in 2^124 *)
  set (cd0 := divstep_trans.Trans.u mtx * (d mod 2 ^ 62)
              + divstep_trans.Trans.v mtx * (e mod 2 ^ 62)) in *.
  set (ce0 := divstep_trans.Trans.q mtx * (d mod 2 ^ 62)
              + divstep_trans.Trans.r mtx * (e mod 2 ^ 62)) in *.
  assert (Hcd0b : -2 ^ 124 <= cd0 <= 2 ^ 124) by (clear -Hudve; lia).
  assert (Hce0b : -2 ^ 124 <= ce0 <= 2 ^ 124) by (clear -Hqrve; lia).

  (* ===== Correction: md -= (minv*cd + md) & M62; likewise me ===== *)

  (* _t'1 = secp256k1_i128_to_u64(&cd) *)
  forward_call (v_cd, Rcd0, Tsh).
  Intros cdu.
  rename H into Hcdu.
  rewrite Hcd0 in Hcdu.

  (* _t'20 = modinfo->modulus_inv62 *)
  forward.
  (* md = md - ((_t'20 * _t'1 + md) & M62) *)
  forward.

  (* _t'2 = secp256k1_i128_to_u64(&ce) *)
  forward_call (v_ce, Rce0, Tsh).
  Intros ceu.
  rename H into Hceu.
  rewrite Hce0 in Hceu.

  (* _t'19 = modinfo->modulus_inv62 *)
  forward.
  (* me = me - ((_t'19 * _t'2 + me) & M62) *)
  forward.

  (* the C multiplies the [to_u64] truncation (mod 2^64); the outer & M62 absorbs it *)
  assert (Hdrop : forall a x b, (a * (x mod 2 ^ 64) + b) mod 2 ^ 62 = (a * x + b) mod 2 ^ 62).
  { intros a x b.
    rewrite <- Zplus_mod_idemp_l, <- (Zplus_mod_idemp_l (a * x)).
    f_equal.
    f_equal.
    rewrite (Zmult_mod a (x mod 2 ^ 64)), (Zmult_mod a x).
    f_equal.
    f_equal.
    symmetry.
    apply Zmod_div_mod; [lia | lia | exists (2 ^ 2); reflexivity]. }

  autorewrite with int_to_z.
  rewrite !Z.land_ones by lia.
  rewrite Hcdu, Hceu.
  rewrite !Hdrop.
  clear Hdrop.

  (* expose the five modulus limbs for the accum_mul and update_de_limb loads *)
  simpl (Signed62.reprn 5 m).

  (* name md,me (the corrected multipliers); each stays inside int64 *)
  set (md := md0 - (mod_inv m (2 ^ 62) * cd0 + md0) mod 2 ^ 62) in *.
  set (me := me0 - (mod_inv m (2 ^ 62) * ce0 + me0) mod 2 ^ 62) in *.

  assert (Hmd : -2 ^ 63 < md <= 2 ^ 62).
  { pose proof (Hmod62 (mod_inv m (2 ^ 62) * cd0 + md0)) as Hx.
    unfold md.
    lia. }

  assert (Hme : -2 ^ 63 < me <= 2 ^ 62).
  { pose proof (Hmod62 (mod_inv m (2 ^ 62) * ce0 + me0)) as Hx.
    unfold me.
    lia. }

  (* model-typed wrappers for md, me and the bottom modulus limb m mod 2^62 *)
  assert (HmdB : -2 ^ 63 <= md < 2 ^ 63) by lia.
  assert (HmeB : -2 ^ 63 <= me < 2 ^ 63) by lia.
  assert (Hm0B : -2 ^ 63 <= m mod 2 ^ 62 < 2 ^ 63) by lia.

  set (mdI := mkInt64 md HmdB).
  set (meI := mkInt64 me HmeB).
  set (m0I := mkInt64 (m mod 2 ^ 62) Hm0B).

  assert (HmdI : i64_val mdI = md) by reflexivity.
  assert (HmeI : i64_val meI = me) by reflexivity.
  assert (Hm0I : i64_val m0I = m mod 2 ^ 62) by reflexivity.

  (* the corrected low accumulators fit in 2^126, hence inside int128 *)
  assert (Hcd0'b : -2 ^ 127 <= cd0 + m mod 2 ^ 62 * md <= 2 ^ 127 - 1).
  { assert (Hb : -2 ^ 126 <= cd0 + m mod 2 ^ 62 * md <= 2 ^ 126) by (clear -Hcd0b Hmd Hm62; nia).
    lia. }

  assert (Hce0'b : -2 ^ 127 <= ce0 + m mod 2 ^ 62 * me <= 2 ^ 127 - 1).
  { assert (Hb : -2 ^ 126 <= ce0 + m mod 2 ^ 62 * me <= 2 ^ 126) by (clear -Hce0b Hme Hm62; nia).
    lia. }

  (* _t'18 = modinfo->modulus.v[0] *)
  forward.
  (* secp256k1_i128_accum_mul(&cd, _t'18, md) *)
  forward_call (v_cd, Rcd0, m0I, mdI, Tsh).
  Intros Rcd0'.
  rename H into Hcd0'.
  rewrite Hcd0, Hm0I, HmdI in Hcd0'.

  (* _t'17 = modinfo->modulus.v[0] *)
  forward.
  (* secp256k1_i128_accum_mul(&ce, _t'17, me) *)
  forward_call (v_ce, Rce0, m0I, meI, Tsh).
  Intros Rce0'.
  rename H into Hce0'.
  rewrite Hce0, Hm0I, HmeI in Hce0'.

  (* name the corrected low accumulators *)
  set (cd0' := cd0 + m mod 2 ^ 62 * md) in *.
  set (ce0' := ce0 + m mod 2 ^ 62 * me) in *.

  (* secp256k1_i128_rshift(&cd, 62) -- drop the (verified-zero) low limb *)
  forward_call (v_cd, Rcd0', 62, Tsh).
  Intros Rcd1s.
  rename H into Hcd1s.
  rewrite Hcd0', <- Z.shiftr_div_pow2 in Hcd1s by lia.

  (* secp256k1_i128_rshift(&ce, 62) -- drop the (verified-zero) low limb *)
  forward_call (v_ce, Rce0', 62, Tsh).
  Intros Rce1s.
  rename H into Hce1s.
  rewrite Hce0', <- Z.shiftr_div_pow2 in Hce1s by lia.

  (* ===== Shared helpers for the limb loop: accumulator bounds, carry, stores ===== *)

  (* HboundA/HboundB: one shifted accumulator plus one (or two) limb products
     stays in 2^126, so every [i128_accum_mul] inside [update_de_limb] is safe *)
  assert (HboundA : forall x y z, -2 ^ 127 <= x < 2 ^ 127 -> -2 ^ 62 <= y <= 2 ^ 62 ->
          -2 ^ 126 <= Z.shiftr x 62 + y * (z mod 2 ^ 62) <= 2 ^ 126 - 1).
  { intros x y z Hx Hy.
    assert (Hs : -2 ^ 65 <= Z.shiftr x 62 < 2 ^ 65) by (apply shiftr_bounds; lia).
    assert (Hz : 0 <= z mod 2 ^ 62 < 2 ^ 62) by (apply Z.mod_pos_bound; lia).
    clear -Hs Hy Hz.
    nia. }

  assert (HboundB : forall x y0 z0 y1 z1, -2 ^ 127 <= x < 2 ^ 127 ->
          -2 ^ 62 <= y0 <= 2 ^ 62 -> -2 ^ 62 <= y1 <= 2 ^ 62 ->
          -2 ^ 126 <= Z.shiftr x 62 + y0 * (z0 mod 2 ^ 62) + y1 * (z1 mod 2 ^ 62) <= 2 ^ 126 - 1).
  { intros x y0 z0 y1 z1 Hx Hy0 Hy1.
    assert (Hs : -2 ^ 65 <= Z.shiftr x 62 < 2 ^ 65) by (apply shiftr_bounds; lia).
    assert (Hz0 : 0 <= z0 mod 2 ^ 62 < 2 ^ 62) by (apply Z.mod_pos_bound; lia).
    assert (Hz1 : 0 <= z1 mod 2 ^ 62 < 2 ^ 62) by (apply Z.mod_pos_bound; lia).
    clear -Hs Hy0 Hy1 Hz0 Hz1.
    nia. }

  (* Hcarry: the carry identity -- one shifted accumulator step plus the limb-n
     products is the next-window accumulator (mod 2^(n+124) instead of 2^(n+62)) *)
  assert (Hcarry : forall n a x y z, 0 <= n ->
          a = Z.shiftr (x * (d mod 2 ^ (n + 62)) + y * (e mod 2 ^ (n + 62))
                        + (m mod 2 ^ (n + 62)) * z) n ->
          Z.shiftr a 62 + x * (Z.shiftr d (n + 62) mod 2 ^ 62)
            + y * (Z.shiftr e (n + 62) mod 2 ^ 62)
            + (Z.shiftr m (n + 62) mod 2 ^ 62) * z
          = Z.shiftr (x * (d mod 2 ^ (n + 124)) + y * (e mod 2 ^ (n + 124))
                      + (m mod 2 ^ (n + 124)) * z) (n + 62)).
  { intros n a x y z Hn ->.
    rewrite !Z.shiftr_div_pow2 by lia.
    rewrite Z.div_div by lia.
    rewrite <- !Z.add_assoc, Z.add_comm, !Z.add_assoc, <- Z.div_add_l, <- !Z.pow_add_r by lia.
    replace ((x * ((d / 2 ^ (n + 62)) mod 2 ^ 62)
              + y * ((e / 2 ^ (n + 62)) mod 2 ^ 62)
              + (m / 2 ^ (n + 62)) mod 2 ^ 62 * z) * 2 ^ (n + 62)
             + (x * (d mod 2 ^ (n + 62)) + y * (e mod 2 ^ (n + 62))
                + m mod 2 ^ (n + 62) * z))
      with (x * (d mod 2 ^ (n + 62) + 2 ^ (n + 62) * ((d / 2 ^ (n + 62)) mod 2 ^ 62))
            + y * (e mod 2 ^ (n + 62) + 2 ^ (n + 62) * ((e / 2 ^ (n + 62)) mod 2 ^ 62))
            + (m mod 2 ^ (n + 62) + 2 ^ (n + 62) * ((m / 2 ^ (n + 62)) mod 2 ^ 62)) * z)
      by ring.
    rewrite <- !Z.rem_mul_r, <- !Z.pow_add_r, <- !Z.add_assoc by lia.
    reflexivity. }

  (* cond_mul: the helper's [if (mod_n)] guard is a no-op on the math side *)
  assert (cond_mul : forall a b : Z, (if a =? 0 then 0 else a * b) = a * b)
    by (intros a b; destruct (a =? 0) eqn:Eq; [apply Z.eqb_eq in Eq; subst; ring | reflexivity]).

  (* Hstore: one stored limb [(x mod 2^64) & M62] normalizes to [Int64.repr (x mod 2^62)] *)
  assert (Habs64 : forall x, (x mod 2 ^ 64) mod 2 ^ 62 = x mod 2 ^ 62).
  { intros x.
    symmetry.
    apply Zmod_div_mod; [lia | lia | exists (2 ^ 2); reflexivity]. }

  assert (Hstore : forall x, Int64.and (Int64.repr (x mod 2 ^ 64)) (Int64.repr (Z.ones 62))
                             = Int64.repr (x mod 2 ^ 62)).
  { intros x.
    rewrite and64_repr, Z.land_ones, Habs64 by lia.
    reflexivity. }

  (* ===== Limb 1 (output limb 0): update_de_limb on d1, e1, modulus.v[1] ===== *)

  (* the limb-1 accumulator bounds, partial (') and full ('') for cd and ce *)
  assert (Hcd1' : -2 ^ 126 <= Z.shiftr cd0' 62
                              + divstep_trans.Trans.u mtx * (Z.shiftr d 62 mod 2 ^ 62) <= 2 ^ 126 - 1)
    by (apply HboundA; lia).
  assert (Hcd1'' : -2 ^ 126 <= Z.shiftr cd0' 62
                               + divstep_trans.Trans.u mtx * (Z.shiftr d 62 mod 2 ^ 62)
                               + divstep_trans.Trans.v mtx * (Z.shiftr e 62 mod 2 ^ 62) <= 2 ^ 126 - 1)
    by (apply HboundB; lia).
  assert (Hce1' : -2 ^ 126 <= Z.shiftr ce0' 62
                              + divstep_trans.Trans.q mtx * (Z.shiftr d 62 mod 2 ^ 62) <= 2 ^ 126 - 1)
    by (apply HboundA; lia).
  assert (Hce1'' : -2 ^ 126 <= Z.shiftr ce0' 62
                               + divstep_trans.Trans.q mtx * (Z.shiftr d 62 mod 2 ^ 62)
                               + divstep_trans.Trans.r mtx * (Z.shiftr e 62 mod 2 ^ 62) <= 2 ^ 126 - 1)
    by (apply HboundB; lia).

  (* _t'16 = modinfo->modulus.v[1] *)
  forward.
  unfold Znth.
  simpl (temp _ _).

  (* abbreviate the (still unmodified) d and e limb lists; name m1 = m >> 62 *)
  set (dval := map Vlong [Int64.repr (d mod 2 ^ 62); Int64.repr (Z.shiftr d 62 mod 2 ^ 62);
                          Int64.repr (Z.shiftr d 124 mod 2 ^ 62); Int64.repr (Z.shiftr d 186 mod 2 ^ 62);
                          Int64.repr (Z.shiftr d 248)]).
  set (eval := map Vlong [Int64.repr (e mod 2 ^ 62); Int64.repr (Z.shiftr e 62 mod 2 ^ 62);
                          Int64.repr (Z.shiftr e 124 mod 2 ^ 62); Int64.repr (Z.shiftr e 186 mod 2 ^ 62);
                          Int64.repr (Z.shiftr e 248)]).
  set (m1 := Z.shiftr m 62 mod 2 ^ 62) in *.

  assert (Hm1 : 0 <= m1 < 2 ^ 62) by (apply Z.mod_pos_bound; lia).
  assert (Hm1md : -2 ^ 125 <= m1 * md <= 2 ^ 125) by (clear -Hm1 Hmd; nia).
  assert (Hm1me : -2 ^ 125 <= m1 * me <= 2 ^ 125) by (clear -Hm1 Hme; nia).

  (* model-typed wrappers for the limb-1 dn, en and the modulus limb m1 *)
  assert (Hd1B : -2 ^ 63 <= Z.shiftr d 62 mod 2 ^ 62 < 2 ^ 63) by (pose proof (Hmod62 (Z.shiftr d 62)); lia).
  assert (He1B : -2 ^ 63 <= Z.shiftr e 62 mod 2 ^ 62 < 2 ^ 63) by (pose proof (Hmod62 (Z.shiftr e 62)); lia).
  assert (Hm1B : -2 ^ 63 <= m1 < 2 ^ 63) by lia.

  set (d1I := mkInt64 (Z.shiftr d 62 mod 2 ^ 62) Hd1B).
  set (e1I := mkInt64 (Z.shiftr e 62 mod 2 ^ 62) He1B).
  set (m1I := mkInt64 m1 Hm1B).

  assert (Hd1I : i64_val d1I = Z.shiftr d 62 mod 2 ^ 62) by reflexivity.
  assert (He1I : i64_val e1I = Z.shiftr e 62 mod 2 ^ 62) by reflexivity.
  assert (Hm1I : i64_val m1I = m1) by reflexivity.

  (* secp256k1_modinv64_update_de_limb(&cd, &ce, u, v, q, r, d1, e1, md, me, _t'16) *)
  forward_call (v_cd, v_ce, Tsh, Tsh, Rcd1s, Rce1s,
                uI, vI, qI, rI, d1I, e1I, mdI, meI, m1I).
  Intros vret1.
  destruct vret1 as [Rcd1 Rce1].
  simpl fst in *.
  simpl snd in *.
  rename H into Hcd1eq.
  rename H0 into Hce1eq.
  rewrite Hcd1s, HuI, HvI, Hd1I, He1I, HmdI, Hm1I in Hcd1eq.
  rewrite Hce1s, HqI, HrI, Hd1I, He1I, HmeI, Hm1I in Hce1eq.

  rewrite !cond_mul in Hcd1eq, Hce1eq.

  (* name cd1,ce1 (the limb-1 accumulators); Hcd124/Hce124 are their carry form *)
  set (cd1 := i128_val Rcd1) in *.
  set (ce1 := i128_val Rce1) in *.
  change (cd1 = Z.shiftr cd0' 62 + divstep_trans.Trans.u mtx * (Z.shiftr d 62 mod 2 ^ 62)
          + divstep_trans.Trans.v mtx * (Z.shiftr e 62 mod 2 ^ 62) + m1 * md) in Hcd1eq.
  change (ce1 = Z.shiftr ce0' 62 + divstep_trans.Trans.q mtx * (Z.shiftr d 62 mod 2 ^ 62)
          + divstep_trans.Trans.r mtx * (Z.shiftr e 62 mod 2 ^ 62) + m1 * me) in Hce1eq.

  assert (Hcd1 : -2 ^ 127 <= cd1 <= 2 ^ 127 - 1) by (rewrite Hcd1eq; lia).
  assert (Hce1 : -2 ^ 127 <= ce1 <= 2 ^ 127 - 1) by (rewrite Hce1eq; lia).

  assert (Hcd124 : cd1 = Z.shiftr (divstep_trans.Trans.u mtx * (d mod 2 ^ 124)
                                   + divstep_trans.Trans.v mtx * (e mod 2 ^ 124)
                                   + (m mod 2 ^ 124) * md) 62)
    by (rewrite Hcd1eq; apply (Hcarry 0); [lia | reflexivity]).
  assert (Hce124 : ce1 = Z.shiftr (divstep_trans.Trans.q mtx * (d mod 2 ^ 124)
                                   + divstep_trans.Trans.r mtx * (e mod 2 ^ 124)
                                   + (m mod 2 ^ 124) * me) 62)
    by (rewrite Hce1eq; apply (Hcarry 0); [lia | reflexivity]).

  assert (HRcd1 : i128_val Rcd1 = cd1) by reflexivity.
  assert (HRce1 : i128_val Rce1 = ce1) by reflexivity.

  clear Hcd1eq Hce1eq.

  (* _t'3 = secp256k1_i128_to_u64(&cd) *)
  forward_call (v_cd, Rcd1, Tsh).
  Intros cd1u.
  rename H into Hcd1u.
  rewrite HRcd1 in Hcd1u.

  (* d->v[0] = _t'3 & M62 *)
  forward.
  rewrite Hcd1u, Hstore.

  (* secp256k1_i128_rshift(&cd, 62) *)
  forward_call (v_cd, Rcd1, 62, Tsh).
  Intros Rcd2s.
  rename H into Hcd2s.
  rewrite HRcd1, <- Z.shiftr_div_pow2 in Hcd2s by lia.

  (* _t'4 = secp256k1_i128_to_u64(&ce) *)
  forward_call (v_ce, Rce1, Tsh).
  Intros ce1u.
  rename H into Hce1u.
  rewrite HRce1 in Hce1u.

  (* e->v[0] = _t'4 & M62 *)
  forward.
  rewrite Hce1u, Hstore.

  (* secp256k1_i128_rshift(&ce, 62) *)
  forward_call (v_ce, Rce1, 62, Tsh).
  Intros Rce2s.
  rename H into Hce2s.
  rewrite HRce1, <- Z.shiftr_div_pow2 in Hce2s by lia.

  (* ===== Limb 2 (output limb 1): update_de_limb on d2, e2, modulus.v[2] ===== *)

  (* the limb-2 accumulator bounds, partial (') and full ('') for cd and ce *)
  assert (Hcd2' : -2 ^ 126 <= Z.shiftr cd1 62
                              + divstep_trans.Trans.u mtx * (Z.shiftr d 124 mod 2 ^ 62) <= 2 ^ 126 - 1)
    by (apply HboundA; lia).
  assert (Hcd2'' : -2 ^ 126 <= Z.shiftr cd1 62
                               + divstep_trans.Trans.u mtx * (Z.shiftr d 124 mod 2 ^ 62)
                               + divstep_trans.Trans.v mtx * (Z.shiftr e 124 mod 2 ^ 62) <= 2 ^ 126 - 1)
    by (apply HboundB; lia).
  assert (Hce2' : -2 ^ 126 <= Z.shiftr ce1 62
                              + divstep_trans.Trans.q mtx * (Z.shiftr d 124 mod 2 ^ 62) <= 2 ^ 126 - 1)
    by (apply HboundA; lia).
  assert (Hce2'' : -2 ^ 126 <= Z.shiftr ce1 62
                               + divstep_trans.Trans.q mtx * (Z.shiftr d 124 mod 2 ^ 62)
                               + divstep_trans.Trans.r mtx * (Z.shiftr e 124 mod 2 ^ 62) <= 2 ^ 126 - 1)
    by (apply HboundB; lia).

  (* _t'15 = modinfo->modulus.v[2] *)
  forward.
  unfold Znth.
  simpl (temp _ _).

  (* commit output limb 0 into the d,e limb lists; name m2 = m >> 124 *)
  set (dval1 := upd_Znth 0 dval (Vlong (Int64.repr (cd1 mod 2 ^ 62)))).
  set (eval1 := upd_Znth 0 eval (Vlong (Int64.repr (ce1 mod 2 ^ 62)))).
  set (m2 := Z.shiftr m 124 mod 2 ^ 62) in *.

  assert (Hm2 : 0 <= m2 < 2 ^ 62) by (apply Z.mod_pos_bound; lia).
  assert (Hm2md : -2 ^ 125 <= m2 * md <= 2 ^ 125) by (clear -Hm2 Hmd; nia).
  assert (Hm2me : -2 ^ 125 <= m2 * me <= 2 ^ 125) by (clear -Hm2 Hme; nia).

  (* model-typed wrappers for the limb-2 dn, en and the modulus limb m2 *)
  assert (Hd2B : -2 ^ 63 <= Z.shiftr d 124 mod 2 ^ 62 < 2 ^ 63) by (pose proof (Hmod62 (Z.shiftr d 124)); lia).
  assert (He2B : -2 ^ 63 <= Z.shiftr e 124 mod 2 ^ 62 < 2 ^ 63) by (pose proof (Hmod62 (Z.shiftr e 124)); lia).
  assert (Hm2B : -2 ^ 63 <= m2 < 2 ^ 63) by lia.

  set (d2I := mkInt64 (Z.shiftr d 124 mod 2 ^ 62) Hd2B).
  set (e2I := mkInt64 (Z.shiftr e 124 mod 2 ^ 62) He2B).
  set (m2I := mkInt64 m2 Hm2B).

  assert (Hd2I : i64_val d2I = Z.shiftr d 124 mod 2 ^ 62) by reflexivity.
  assert (He2I : i64_val e2I = Z.shiftr e 124 mod 2 ^ 62) by reflexivity.
  assert (Hm2I : i64_val m2I = m2) by reflexivity.

  (* secp256k1_modinv64_update_de_limb(&cd, &ce, u, v, q, r, d2, e2, md, me, _t'15) *)
  forward_call (v_cd, v_ce, Tsh, Tsh, Rcd2s, Rce2s,
                uI, vI, qI, rI, d2I, e2I, mdI, meI, m2I).
  Intros vret2.
  destruct vret2 as [Rcd2 Rce2].
  simpl fst in *.
  simpl snd in *.
  rename H into Hcd2eq.
  rename H0 into Hce2eq.
  rewrite Hcd2s, HuI, HvI, Hd2I, He2I, HmdI, Hm2I in Hcd2eq.
  rewrite Hce2s, HqI, HrI, Hd2I, He2I, HmeI, Hm2I in Hce2eq.

  rewrite !cond_mul in Hcd2eq, Hce2eq.

  (* name cd2,ce2 (the limb-2 accumulators); Hcd186/Hce186 are their carry form *)
  set (cd2 := i128_val Rcd2) in *.
  set (ce2 := i128_val Rce2) in *.
  change (cd2 = Z.shiftr cd1 62 + divstep_trans.Trans.u mtx * (Z.shiftr d 124 mod 2 ^ 62)
          + divstep_trans.Trans.v mtx * (Z.shiftr e 124 mod 2 ^ 62) + m2 * md) in Hcd2eq.
  change (ce2 = Z.shiftr ce1 62 + divstep_trans.Trans.q mtx * (Z.shiftr d 124 mod 2 ^ 62)
          + divstep_trans.Trans.r mtx * (Z.shiftr e 124 mod 2 ^ 62) + m2 * me) in Hce2eq.

  assert (Hcd2 : -2 ^ 127 <= cd2 <= 2 ^ 127 - 1) by (rewrite Hcd2eq; lia).
  assert (Hce2 : -2 ^ 127 <= ce2 <= 2 ^ 127 - 1) by (rewrite Hce2eq; lia).

  assert (Hcd186 : cd2 = Z.shiftr (divstep_trans.Trans.u mtx * (d mod 2 ^ 186)
                                   + divstep_trans.Trans.v mtx * (e mod 2 ^ 186)
                                   + (m mod 2 ^ 186) * md) 124)
    by (rewrite Hcd2eq; apply (Hcarry 62); [lia | assumption]).
  assert (Hce186 : ce2 = Z.shiftr (divstep_trans.Trans.q mtx * (d mod 2 ^ 186)
                                   + divstep_trans.Trans.r mtx * (e mod 2 ^ 186)
                                   + (m mod 2 ^ 186) * me) 124)
    by (rewrite Hce2eq; apply (Hcarry 62); [lia | assumption]).

  assert (HRcd2 : i128_val Rcd2 = cd2) by reflexivity.
  assert (HRce2 : i128_val Rce2 = ce2) by reflexivity.

  clear Hcd2eq Hce2eq.

  (* _t'5 = secp256k1_i128_to_u64(&cd) *)
  forward_call (v_cd, Rcd2, Tsh).
  Intros cd2u.
  rename H into Hcd2u.
  rewrite HRcd2 in Hcd2u.

  (* d->v[1] = _t'5 & M62 *)
  forward.
  rewrite Hcd2u, Hstore.

  (* secp256k1_i128_rshift(&cd, 62) *)
  forward_call (v_cd, Rcd2, 62, Tsh).
  Intros Rcd3s.
  rename H into Hcd3s.
  rewrite HRcd2, <- Z.shiftr_div_pow2 in Hcd3s by lia.

  (* _t'6 = secp256k1_i128_to_u64(&ce) *)
  forward_call (v_ce, Rce2, Tsh).
  Intros ce2u.
  rename H into Hce2u.
  rewrite HRce2 in Hce2u.

  (* e->v[1] = _t'6 & M62 *)
  forward.
  rewrite Hce2u, Hstore.

  (* secp256k1_i128_rshift(&ce, 62) *)
  forward_call (v_ce, Rce2, 62, Tsh).
  Intros Rce3s.
  rename H into Hce3s.
  rewrite HRce2, <- Z.shiftr_div_pow2 in Hce3s by lia.

  (* ===== Limb 3 (output limb 2): update_de_limb on d3, e3, modulus.v[3] ===== *)

  (* the limb-3 accumulator bounds, partial (') and full ('') for cd and ce *)
  assert (Hcd3' : -2 ^ 126 <= Z.shiftr cd2 62
                              + divstep_trans.Trans.u mtx * (Z.shiftr d 186 mod 2 ^ 62) <= 2 ^ 126 - 1)
    by (apply HboundA; lia).
  assert (Hcd3'' : -2 ^ 126 <= Z.shiftr cd2 62
                               + divstep_trans.Trans.u mtx * (Z.shiftr d 186 mod 2 ^ 62)
                               + divstep_trans.Trans.v mtx * (Z.shiftr e 186 mod 2 ^ 62) <= 2 ^ 126 - 1)
    by (apply HboundB; lia).
  assert (Hce3' : -2 ^ 126 <= Z.shiftr ce2 62
                              + divstep_trans.Trans.q mtx * (Z.shiftr d 186 mod 2 ^ 62) <= 2 ^ 126 - 1)
    by (apply HboundA; lia).
  assert (Hce3'' : -2 ^ 126 <= Z.shiftr ce2 62
                               + divstep_trans.Trans.q mtx * (Z.shiftr d 186 mod 2 ^ 62)
                               + divstep_trans.Trans.r mtx * (Z.shiftr e 186 mod 2 ^ 62) <= 2 ^ 126 - 1)
    by (apply HboundB; lia).

  (* _t'14 = modinfo->modulus.v[3] *)
  forward.
  unfold Znth.
  simpl (temp _ _).

  (* commit output limb 1 into the d,e limb lists; name m3 = m >> 186 *)
  set (dval2 := upd_Znth 1 dval1 (Vlong (Int64.repr (cd2 mod 2 ^ 62)))).
  set (eval2 := upd_Znth 1 eval1 (Vlong (Int64.repr (ce2 mod 2 ^ 62)))).
  set (m3 := Z.shiftr m 186 mod 2 ^ 62) in *.

  assert (Hm3 : 0 <= m3 < 2 ^ 62) by (apply Z.mod_pos_bound; lia).
  assert (Hm3md : -2 ^ 125 <= m3 * md <= 2 ^ 125) by (clear -Hm3 Hmd; nia).
  assert (Hm3me : -2 ^ 125 <= m3 * me <= 2 ^ 125) by (clear -Hm3 Hme; nia).

  (* model-typed wrappers for the limb-3 dn, en and the modulus limb m3 *)
  assert (Hd3B : -2 ^ 63 <= Z.shiftr d 186 mod 2 ^ 62 < 2 ^ 63) by (pose proof (Hmod62 (Z.shiftr d 186)); lia).
  assert (He3B : -2 ^ 63 <= Z.shiftr e 186 mod 2 ^ 62 < 2 ^ 63) by (pose proof (Hmod62 (Z.shiftr e 186)); lia).
  assert (Hm3B : -2 ^ 63 <= m3 < 2 ^ 63) by lia.

  set (d3I := mkInt64 (Z.shiftr d 186 mod 2 ^ 62) Hd3B).
  set (e3I := mkInt64 (Z.shiftr e 186 mod 2 ^ 62) He3B).
  set (m3I := mkInt64 m3 Hm3B).

  assert (Hd3I : i64_val d3I = Z.shiftr d 186 mod 2 ^ 62) by reflexivity.
  assert (He3I : i64_val e3I = Z.shiftr e 186 mod 2 ^ 62) by reflexivity.
  assert (Hm3I : i64_val m3I = m3) by reflexivity.

  (* secp256k1_modinv64_update_de_limb(&cd, &ce, u, v, q, r, d3, e3, md, me, _t'14) *)
  forward_call (v_cd, v_ce, Tsh, Tsh, Rcd3s, Rce3s,
                uI, vI, qI, rI, d3I, e3I, mdI, meI, m3I).
  Intros vret3.
  destruct vret3 as [Rcd3 Rce3].
  simpl fst in *.
  simpl snd in *.
  rename H into Hcd3eq.
  rename H0 into Hce3eq.
  rewrite Hcd3s, HuI, HvI, Hd3I, He3I, HmdI, Hm3I in Hcd3eq.
  rewrite Hce3s, HqI, HrI, Hd3I, He3I, HmeI, Hm3I in Hce3eq.

  rewrite !cond_mul in Hcd3eq, Hce3eq.

  (* name cd3,ce3 (the limb-3 accumulators); Hcd248/Hce248 are their carry form *)
  set (cd3 := i128_val Rcd3) in *.
  set (ce3 := i128_val Rce3) in *.
  change (cd3 = Z.shiftr cd2 62 + divstep_trans.Trans.u mtx * (Z.shiftr d 186 mod 2 ^ 62)
          + divstep_trans.Trans.v mtx * (Z.shiftr e 186 mod 2 ^ 62) + m3 * md) in Hcd3eq.
  change (ce3 = Z.shiftr ce2 62 + divstep_trans.Trans.q mtx * (Z.shiftr d 186 mod 2 ^ 62)
          + divstep_trans.Trans.r mtx * (Z.shiftr e 186 mod 2 ^ 62) + m3 * me) in Hce3eq.

  assert (Hcd3 : -2 ^ 127 <= cd3 <= 2 ^ 127 - 1) by (rewrite Hcd3eq; lia).
  assert (Hce3 : -2 ^ 127 <= ce3 <= 2 ^ 127 - 1) by (rewrite Hce3eq; lia).

  assert (Hcd248 : cd3 = Z.shiftr (divstep_trans.Trans.u mtx * (d mod 2 ^ 248)
                                   + divstep_trans.Trans.v mtx * (e mod 2 ^ 248)
                                   + (m mod 2 ^ 248) * md) 186)
    by (rewrite Hcd3eq; apply (Hcarry 124); [lia | assumption]).
  assert (Hce248 : ce3 = Z.shiftr (divstep_trans.Trans.q mtx * (d mod 2 ^ 248)
                                   + divstep_trans.Trans.r mtx * (e mod 2 ^ 248)
                                   + (m mod 2 ^ 248) * me) 186)
    by (rewrite Hce3eq; apply (Hcarry 124); [lia | assumption]).

  assert (HRcd3 : i128_val Rcd3 = cd3) by reflexivity.
  assert (HRce3 : i128_val Rce3 = ce3) by reflexivity.

  clear Hcd3eq Hce3eq.

  (* _t'7 = secp256k1_i128_to_u64(&cd) *)
  forward_call (v_cd, Rcd3, Tsh).
  Intros cd3u.
  rename H into Hcd3u.
  rewrite HRcd3 in Hcd3u.

  (* d->v[2] = _t'7 & M62 *)
  forward.
  rewrite Hcd3u, Hstore.

  (* secp256k1_i128_rshift(&cd, 62) *)
  forward_call (v_cd, Rcd3, 62, Tsh).
  Intros Rcd4s.
  rename H into Hcd4s.
  rewrite HRcd3, <- Z.shiftr_div_pow2 in Hcd4s by lia.

  (* _t'8 = secp256k1_i128_to_u64(&ce) *)
  forward_call (v_ce, Rce3, Tsh).
  Intros ce3u.
  rename H into Hce3u.
  rewrite HRce3 in Hce3u.

  (* e->v[2] = _t'8 & M62 *)
  forward.
  rewrite Hce3u, Hstore.

  (* secp256k1_i128_rshift(&ce, 62) *)
  forward_call (v_ce, Rce3, 62, Tsh).
  Intros Rce4s.
  rename H into Hce4s.
  rewrite HRce3, <- Z.shiftr_div_pow2 in Hce4s by lia.

  (* ===== Limb 4 (output limb 3): update_de_limb on the exact top limbs ===== *)

  (* the top limbs d>>248, e>>248 are exact, so the limb-4 bounds are tighter *)
  assert (Hcd3sh : -2 ^ 65 <= Z.shiftr cd3 62 < 2 ^ 65) by (apply shiftr_bounds; lia).
  assert (Hce3sh : -2 ^ 65 <= Z.shiftr ce3 62 < 2 ^ 65) by (apply shiftr_bounds; lia).

  assert (Hcd4' : -2 ^ 124 <= Z.shiftr cd3 62
                              + divstep_trans.Trans.u mtx * Z.shiftr d 248 <= 2 ^ 124 - 1)
    by (clear -Hd248 Hcd3sh Huv; nia).
  assert (Hcd4'' : -2 ^ 124 <= Z.shiftr cd3 62
                               + divstep_trans.Trans.u mtx * Z.shiftr d 248
                               + divstep_trans.Trans.v mtx * Z.shiftr e 248 <= 2 ^ 124 - 1)
    by (clear -Hd248 He248 Hcd3sh Huv; nia).
  assert (Hce4' : -2 ^ 124 <= Z.shiftr ce3 62
                              + divstep_trans.Trans.q mtx * Z.shiftr d 248 <= 2 ^ 124 - 1)
    by (clear -Hd248 Hce3sh Hqr; nia).
  assert (Hce4'' : -2 ^ 124 <= Z.shiftr ce3 62
                               + divstep_trans.Trans.q mtx * Z.shiftr d 248
                               + divstep_trans.Trans.r mtx * Z.shiftr e 248 <= 2 ^ 124 - 1)
    by (clear -Hd248 He248 Hce3sh Hqr; nia).

  (* _t'13 = modinfo->modulus.v[4] *)
  forward.
  unfold Znth.
  simpl (temp _ _).

  (* commit output limb 2 into the d,e limb lists; name m4 = m >> 248 (the top limb) *)
  set (dval3 := upd_Znth 2 dval2 (Vlong (Int64.repr (cd3 mod 2 ^ 62)))).
  set (eval3 := upd_Znth 2 eval2 (Vlong (Int64.repr (ce3 mod 2 ^ 62)))).
  set (m4 := Z.shiftr m 248) in *.

  assert (Hm4 : 0 <= m4 < 2 ^ 61) by (unfold m4; apply shiftr_bounds; lia).
  assert (Hm4md : -2 ^ 124 <= m4 * md <= 2 ^ 124) by (clear -Hm4 Hmd; nia).
  assert (Hm4me : -2 ^ 124 <= m4 * me <= 2 ^ 124) by (clear -Hm4 Hme; nia).

  (* model-typed wrappers for the limb-4 dn, en (exact) and the top modulus limb m4 *)
  assert (Hd4B : -2 ^ 63 <= Z.shiftr d 248 < 2 ^ 63) by lia.
  assert (He4B : -2 ^ 63 <= Z.shiftr e 248 < 2 ^ 63) by lia.
  assert (Hm4B : -2 ^ 63 <= m4 < 2 ^ 63) by lia.

  set (d4I := mkInt64 (Z.shiftr d 248) Hd4B).
  set (e4I := mkInt64 (Z.shiftr e 248) He4B).
  set (m4I := mkInt64 m4 Hm4B).

  assert (Hd4I : i64_val d4I = Z.shiftr d 248) by reflexivity.
  assert (He4I : i64_val e4I = Z.shiftr e 248) by reflexivity.
  assert (Hm4I : i64_val m4I = m4) by reflexivity.

  (* secp256k1_modinv64_update_de_limb(&cd, &ce, u, v, q, r, d4, e4, md, me, _t'13) *)
  forward_call (v_cd, v_ce, Tsh, Tsh, Rcd4s, Rce4s,
                uI, vI, qI, rI, d4I, e4I, mdI, meI, m4I).
  Intros vret4.
  destruct vret4 as [Rcd4 Rce4].
  simpl fst in *.
  simpl snd in *.
  rename H into Hcd4eq.
  rename H0 into Hce4eq.
  rewrite Hcd4s, HuI, HvI, Hd4I, He4I, HmdI, Hm4I in Hcd4eq.
  rewrite Hce4s, HqI, HrI, Hd4I, He4I, HmeI, Hm4I in Hce4eq.

  rewrite !cond_mul in Hcd4eq, Hce4eq.

  (* name cd4,ce4 (the limb-4 accumulators); Hcd310/Hce310 close them to the full cd,ce *)
  set (cd4 := i128_val Rcd4) in *.
  set (ce4 := i128_val Rce4) in *.
  change (cd4 = Z.shiftr cd3 62 + divstep_trans.Trans.u mtx * Z.shiftr d 248
          + divstep_trans.Trans.v mtx * Z.shiftr e 248 + m4 * md) in Hcd4eq.
  change (ce4 = Z.shiftr ce3 62 + divstep_trans.Trans.q mtx * Z.shiftr d 248
          + divstep_trans.Trans.r mtx * Z.shiftr e 248 + m4 * me) in Hce4eq.

  assert (Hcd4 : -2 ^ 125 <= cd4 <= 2 ^ 125 - 1) by (rewrite Hcd4eq; lia).
  assert (Hce4 : -2 ^ 125 <= ce4 <= 2 ^ 125 - 1) by (rewrite Hce4eq; lia).

  assert (Hcd310 : cd4 = Z.shiftr (divstep_trans.Trans.u mtx * d
                                   + divstep_trans.Trans.v mtx * e
                                   + m * md) 248).
  { rewrite Hcd4eq.
    unfold m4.
    symmetry.
    rewrite (Z_div_mod_eq_full d (2 ^ 248)) at 1.
    rewrite (Z_div_mod_eq_full e (2 ^ 248)) at 1.
    rewrite (Z_div_mod_eq_full m (2 ^ 248)) at 1.
    replace (divstep_trans.Trans.u mtx * (2 ^ 248 * (d / 2 ^ 248) + d mod 2 ^ 248)
             + divstep_trans.Trans.v mtx * (2 ^ 248 * (e / 2 ^ 248) + e mod 2 ^ 248)
             + (2 ^ 248 * (m / 2 ^ 248) + m mod 2 ^ 248) * md)
      with ((divstep_trans.Trans.u mtx * (d / 2 ^ 248) + divstep_trans.Trans.v mtx * (e / 2 ^ 248)
             + (m / 2 ^ 248) * md) * 2 ^ 248
            + (divstep_trans.Trans.u mtx * (d mod 2 ^ 248) + divstep_trans.Trans.v mtx * (e mod 2 ^ 248)
               + (m mod 2 ^ 248) * md))
      by ring.
    rewrite Hcd248, Z.shiftr_shiftr, !Z.shiftr_div_pow2, Z.div_add_l by lia.
    change (186 + 62) with 248.
    ring. }

  assert (Hce310 : ce4 = Z.shiftr (divstep_trans.Trans.q mtx * d
                                   + divstep_trans.Trans.r mtx * e
                                   + m * me) 248).
  { rewrite Hce4eq.
    unfold m4.
    symmetry.
    rewrite (Z_div_mod_eq_full d (2 ^ 248)) at 1.
    rewrite (Z_div_mod_eq_full e (2 ^ 248)) at 1.
    rewrite (Z_div_mod_eq_full m (2 ^ 248)) at 1.
    replace (divstep_trans.Trans.q mtx * (2 ^ 248 * (d / 2 ^ 248) + d mod 2 ^ 248)
             + divstep_trans.Trans.r mtx * (2 ^ 248 * (e / 2 ^ 248) + e mod 2 ^ 248)
             + (2 ^ 248 * (m / 2 ^ 248) + m mod 2 ^ 248) * me)
      with ((divstep_trans.Trans.q mtx * (d / 2 ^ 248) + divstep_trans.Trans.r mtx * (e / 2 ^ 248)
             + (m / 2 ^ 248) * me) * 2 ^ 248
            + (divstep_trans.Trans.q mtx * (d mod 2 ^ 248) + divstep_trans.Trans.r mtx * (e mod 2 ^ 248)
               + (m mod 2 ^ 248) * me))
      by ring.
    rewrite Hce248, Z.shiftr_shiftr, !Z.shiftr_div_pow2, Z.div_add_l by lia.
    change (186 + 62) with 248.
    ring. }

  assert (HRcd4 : i128_val Rcd4 = cd4) by reflexivity.
  assert (HRce4 : i128_val Rce4 = ce4) by reflexivity.

  clear Hcd4eq Hce4eq.

  (* _t'9 = secp256k1_i128_to_u64(&cd) *)
  forward_call (v_cd, Rcd4, Tsh).
  Intros cd4u.
  rename H into Hcd4u.
  rewrite HRcd4 in Hcd4u.

  (* d->v[3] = _t'9 & M62 *)
  forward.
  rewrite Hcd4u, Hstore.

  (* secp256k1_i128_rshift(&cd, 62) *)
  forward_call (v_cd, Rcd4, 62, Tsh).
  Intros Rcd5s.
  rename H into Hcd5s.
  rewrite HRcd4, <- Z.shiftr_div_pow2 in Hcd5s by lia.

  (* _t'10 = secp256k1_i128_to_u64(&ce) *)
  forward_call (v_ce, Rce4, Tsh).
  Intros ce4u.
  rename H into Hce4u.
  rewrite HRce4 in Hce4u.

  (* e->v[3] = _t'10 & M62 *)
  forward.
  rewrite Hce4u, Hstore.

  (* secp256k1_i128_rshift(&ce, 62) *)
  forward_call (v_ce, Rce4, 62, Tsh).
  Intros Rce5s.
  rename H into Hce5s.
  rewrite HRce4, <- Z.shiftr_div_pow2 in Hce5s by lia.

  (* ===== Postcondition: the five stored limbs are reprn 5 of update_de ===== *)

  (* _t'11 = secp256k1_i128_to_i64(&cd) *)
  forward_call (v_cd, Rcd5s, Tsh).
  { rewrite Hcd5s.
    assert (HB : -2 ^ 63 <= Z.shiftr cd4 62 < 2 ^ 63) by (apply shiftr_bounds; lia).
    lia. }
  Intros cdr.
  rename H into Hcdr.
  rewrite Hcd5s in Hcdr.

  (* d->v[4] = _t'11 *)
  forward.
  unfold int64_to_val.
  rewrite Hcdr.

  (* _t'12 = secp256k1_i128_to_i64(&ce) *)
  forward_call (v_ce, Rce5s, Tsh).
  { rewrite Hce5s.
    assert (HB : -2 ^ 63 <= Z.shiftr ce4 62 < 2 ^ 63) by (apply shiftr_bounds; lia).
    lia. }
  Intros cer.
  rename H into Hcer.
  rewrite Hce5s in Hcer.

  (* e->v[4] = _t'12 *)
  forward.
  unfold int64_to_val.
  rewrite Hcer.

  (* name the assembled limb lists and the two full accumulators *)
  set (dval4 := upd_Znth 4 _ _).
  set (eval4 := upd_Znth 4 _ _).

  set (cd := divstep_trans.Trans.u mtx * d + divstep_trans.Trans.v mtx * e + m * md) in *.
  set (ce := divstep_trans.Trans.q mtx * d + divstep_trans.Trans.r mtx * e + m * me) in *.

  (* the assembled d limbs are reprn 5 (cd >> 62): the per-limb carries chain up
     to mod 2^310, so each stored window agrees with the corresponding [reprn] one *)
  assert (Hdval4 : map Vlong (Signed62.reprn 5 (Z.shiftr cd 62)) = dval4).
  { cbn.
    rewrite !Z.shiftr_shiftr by lia.
    change dval4 with
      [Vlong (Int64.repr (cd1 mod 2 ^ 62));
       Vlong (Int64.repr (cd2 mod 2 ^ 62));
       Vlong (Int64.repr (cd3 mod 2 ^ 62));
       Vlong (Int64.repr (cd4 mod 2 ^ 62));
       Vlong (Int64.repr (Z.shiftr cd4 62))].
    cbn.
    rewrite <- !Z.land_ones by lia.
    rewrite Hcd124, Hcd186, Hcd248, Hcd310.
    rewrite <- (Z.shiftr_land _ (Z.ones 124) 62).
    rewrite <- (Z.shiftr_land _ (Z.ones 186) 124).
    rewrite <- (Z.shiftr_land _ (Z.ones 248) 186).
    rewrite <- (Z.shiftr_land _ (Z.ones 310) 248).
    symmetry.
    rewrite <- (Z.shiftr_land _ (Z.ones 124) 62).
    rewrite <- (Z.shiftr_land _ (Z.ones 186) 124).
    rewrite <- (Z.shiftr_land _ (Z.ones 248) 186).
    rewrite !Z.land_ones by lia.
    repeat (apply eqm_refl || apply Zmod_eqm || apply Zplus_eqm || apply Zmult_eqm || f_equal). }
  rewrite <- Hdval4.

  (* same for the e limbs *)
  assert (Heval4 : map Vlong (Signed62.reprn 5 (Z.shiftr ce 62)) = eval4).
  { cbn.
    rewrite !Z.shiftr_shiftr by lia.
    change eval4 with
      [Vlong (Int64.repr (ce1 mod 2 ^ 62));
       Vlong (Int64.repr (ce2 mod 2 ^ 62));
       Vlong (Int64.repr (ce3 mod 2 ^ 62));
       Vlong (Int64.repr (ce4 mod 2 ^ 62));
       Vlong (Int64.repr (Z.shiftr ce4 62))].
    cbn.
    rewrite <- !Z.land_ones by lia.
    rewrite Hce124, Hce186, Hce248, Hce310.
    rewrite <- (Z.shiftr_land _ (Z.ones 124) 62).
    rewrite <- (Z.shiftr_land _ (Z.ones 186) 124).
    rewrite <- (Z.shiftr_land _ (Z.ones 248) 186).
    rewrite <- (Z.shiftr_land _ (Z.ones 310) 248).
    symmetry.
    rewrite <- (Z.shiftr_land _ (Z.ones 124) 62).
    rewrite <- (Z.shiftr_land _ (Z.ones 186) 124).
    rewrite <- (Z.shiftr_land _ (Z.ones 248) 186).
    rewrite !Z.land_ones by lia.
    repeat (apply eqm_refl || apply Zmod_eqm || apply Zplus_eqm || apply Zmult_eqm || f_equal). }
  rewrite <- Heval4.

  (* re-express cd,ce in the sign-corrected form the model uses (d + [d<0]*m etc.) *)
  assert (Hcd' : cd = divstep_trans.Trans.u mtx * (d + if d <? 0 then m else 0)
                      + divstep_trans.Trans.v mtx * (e + if e <? 0 then m else 0)
                      - m * ((mod_inv m (2 ^ 62) * cd0 + md0) mod 2 ^ 62)).
  { unfold cd, md.
    set (X := mod_inv _ _ * _ + _).
    unfold md0.
    destruct (d <? 0); destruct (e <? 0); ring. }

  assert (Hce' : ce = divstep_trans.Trans.q mtx * (d + if d <? 0 then m else 0)
                      + divstep_trans.Trans.r mtx * (e + if e <? 0 then m else 0)
                      - m * ((mod_inv m (2 ^ 62) * ce0 + me0) mod 2 ^ 62)).
  { unfold ce, me.
    set (X := mod_inv _ _ * _ + _).
    unfold me0.
    destruct (d <? 0); destruct (e <? 0); ring. }

  (* cd >> 62 = fst (update_de m d e mtx): the mod_inv correction matches the
     model's mod 2^62 factor, branch by branch on the two sign masks *)
  assert (Hcdfst : fst (divstep_zeta.update_de m d e mtx) = Z.shiftr cd 62).
  { unfold divstep_zeta.update_de.
    rewrite <- !Z.shiftr_div_pow2 by lia.
    cbn.
    rewrite Hcd'.
    f_equal.
    f_equal.
    rewrite Z.mul_comm.
    f_equal.

    transitivity
      (((if d <? 0
         then (divstep_trans.Trans.u mtx * (mod_inv m (2 ^ 62) * d + mod_inv m (2 ^ 62) * m)) mod 2 ^ 62
         else (mod_inv m (2 ^ 62) * (divstep_trans.Trans.u mtx * d)) mod 2 ^ 62)
        + (if e <? 0
           then (divstep_trans.Trans.v mtx * (mod_inv m (2 ^ 62) * e + mod_inv m (2 ^ 62) * m)) mod 2 ^ 62
           else (mod_inv m (2 ^ 62) * (divstep_trans.Trans.v mtx * e)) mod 2 ^ 62))
       mod 2 ^ 62).
    { destruct (d <? 0); destruct (e <? 0); rewrite <- !Z.add_mod by lia; f_equal; ring. }
    rewrite <- (Zmult_mod_idemp_r _ (divstep_trans.Trans.u mtx)),
            <- (Zmult_mod_idemp_r _ (divstep_trans.Trans.v mtx)),
            <- !(Zplus_mod_idemp_r (_ * m)).
    rewrite mod_inv_mul_l, Hoddm by lia.

    transitivity
      (((if d <? 0
         then divstep_trans.Trans.u mtx * (mod_inv m (2 ^ 62) * (d mod 2 ^ 62) + 1)
         else mod_inv m (2 ^ 62) * (divstep_trans.Trans.u mtx * (d mod 2 ^ 62)))
        + (if e <? 0
           then divstep_trans.Trans.v mtx * (mod_inv m (2 ^ 62) * (e mod 2 ^ 62) + 1)
           else mod_inv m (2 ^ 62) * (divstep_trans.Trans.v mtx * (e mod 2 ^ 62))))
       mod 2 ^ 62).
    { destruct (d <? 0); destruct (e <? 0);
        repeat (apply eqm_refl || apply Zmod_eqm || apply Zplus_eqm || apply Zmult_eqm
                || (unfold eqm; rewrite Zmod_mod)). }
    unfold cd0, md0.
    f_equal.
    destruct (d <? 0); destruct (e <? 0); ring. }

  (* ce >> 62 = snd (update_de m d e mtx): the same argument on the e component *)
  assert (Hcesnd : snd (divstep_zeta.update_de m d e mtx) = Z.shiftr ce 62).
  { unfold divstep_zeta.update_de.
    rewrite <- !Z.shiftr_div_pow2 by lia.
    cbn.
    rewrite Hce'.
    f_equal.
    f_equal.
    rewrite Z.mul_comm.
    f_equal.

    transitivity
      (((if d <? 0
         then (divstep_trans.Trans.q mtx * (mod_inv m (2 ^ 62) * d + mod_inv m (2 ^ 62) * m)) mod 2 ^ 62
         else (mod_inv m (2 ^ 62) * (divstep_trans.Trans.q mtx * d)) mod 2 ^ 62)
        + (if e <? 0
           then (divstep_trans.Trans.r mtx * (mod_inv m (2 ^ 62) * e + mod_inv m (2 ^ 62) * m)) mod 2 ^ 62
           else (mod_inv m (2 ^ 62) * (divstep_trans.Trans.r mtx * e)) mod 2 ^ 62))
       mod 2 ^ 62).
    { destruct (d <? 0); destruct (e <? 0); rewrite <- !Z.add_mod by lia; f_equal; ring. }
    rewrite <- (Zmult_mod_idemp_r _ (divstep_trans.Trans.q mtx)),
            <- (Zmult_mod_idemp_r _ (divstep_trans.Trans.r mtx)),
            <- !(Zplus_mod_idemp_r (_ * m)).
    rewrite mod_inv_mul_l, Hoddm by lia.

    transitivity
      (((if d <? 0
         then divstep_trans.Trans.q mtx * (mod_inv m (2 ^ 62) * (d mod 2 ^ 62) + 1)
         else mod_inv m (2 ^ 62) * (divstep_trans.Trans.q mtx * (d mod 2 ^ 62)))
        + (if e <? 0
           then divstep_trans.Trans.r mtx * (mod_inv m (2 ^ 62) * (e mod 2 ^ 62) + 1)
           else mod_inv m (2 ^ 62) * (divstep_trans.Trans.r mtx * (e mod 2 ^ 62))))
       mod 2 ^ 62).
    { destruct (d <? 0); destruct (e <? 0);
        repeat (apply eqm_refl || apply Zmod_eqm || apply Zplus_eqm || apply Zmult_eqm
                || (unfold eqm; rewrite Zmod_mod)). }
    unfold ce0, me0.
    f_equal.
    destruct (d <? 0); destruct (e <? 0); ring. }

  rewrite <- Hcdfst, <- Hcesnd.

  (* close: the assembled limbs are exactly the postcondition reprs; the cd,ce
     scratch storage is dropped to its uninitialised form on return *)
  entailer!!.
Qed.
