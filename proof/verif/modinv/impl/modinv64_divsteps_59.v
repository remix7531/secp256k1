(** * verif.modinv.impl.modinv64_divsteps_59: body proof for secp256k1_modinv64_divsteps_59
    (the constant-time divstep core).
    The 59-iteration zeta loop and the [scale_m 8 (ztrans_n 59 st)] matrix
    accumulation are proved in full: [f]/[g] track the model limbs mod
    [2^(64-n)], the matrix words hold the exact in-range entries, and the
    branchless [zeta = (zeta ^ mask1) - 1] update matches the model
    [divstep_zeta.zstep] in all three (H/D/S) branches -- the model's zeta H-update
    (in theory/modinv/construction/divstep_zeta.v) now decrements [zeta], matching the C and the upstream
    [zeta = -(delta+1/2)] convention.  Proof is [Qed]; no [admit]/axioms. *)
(** Copyright (C) 2026 remix7531
    SPDX-License-Identifier: MIT *)

Require Import secp256k1.vst.base.
Require Import secp256k1.vst.integers.
Require Import secp256k1.theory.bits.
Require Import secp256k1.contract.helper.structs_modinv.
Require Import secp256k1.contract.impl.modinv.
Require Import secp256k1.contract.gprog.modinv.
Require secp256k1.theory.modinv.construction.divstep.
Require secp256k1.theory.modinv.construction.divstep_trans.
Require secp256k1.theory.modinv.construction.divstep_zeta.

(* The branchless mask / shift identities ([Int64_shr_sign_mask],
   [Int64_and_low1], [Int64_xor_sub_mask], [Int64_and_mask], [Int64_shl1],
   [Int64_shru1]) and the matrix recurrence [scale_m_ztrans_n_s] used below are
   shared lemmas: the [Int64] mask family lives in [vst.integers] and
   [scale_m_ztrans_n_s] in [theory.modinv.construction.divstep_zeta].  The C
   shift/mask amounts ([Int.unsigned (Int.repr 63)], [Int.signed (Int.repr 1)],
   [Int.unsigned (Int.repr 1)]) are [change]d to literals before each rewrite so
   the wrapper-free lemma statements apply. *)

(** [secp256k1_modinv64_divsteps_59(zeta, f0, g0, t)] runs 59 constant-time
    zeta-divsteps from the bottom limbs [f0]/[g0] and the running [zeta],
    writing the [2^62]-scaled transition matrix [scale_m 8 (ztrans_n 59 st)] to
    [*t] and returning the new [zeta = zeta (fst (zstep_n 59 st))].

    Invariant ([forward_for_simple_bound 62] starting at [i = 3], so [n := i-3]
    divsteps are complete): the unsigned words [f]/[g] agree mod [2^(64-n)] with
    the model [zf]/[zg] of [fst (zstep_n n st)]; the [int64] matrix words [u,v,q,r]
    hold the EXACT (in-range, [<= 2^62]) entries of [scale_m 8 (ztrans_n n st)]; and
    [zeta] holds the model [zeta] exactly.  Per iteration the branchless mask code
    realizes one model [zstep]: [Int64_shr_sign_mask] / [Int64_and_low1] turn the
    sign/parity masks into [Int64.repr (if .. then -1 else 0)],
    [Int64_xor_sub_mask] / [Int64_and_mask] select the conditional [+-]operands,
    and the [<<1] / [>>1] shifts halve [g] and
    double the matrix row.  The H/D/S branch is read off [zstep s] by destructing
    on [Zeven_odd_dec (zg s)] and the sign [zeta s <? 0]; [scale_m_ztrans_n_s] left-
    multiplies the emitted step's [trans] onto the accumulator.

    The zeta word [Int64.repr ((zeta ^ mask1) - 1)] equals [Int64.repr
    (zeta (fst (zstep s)))] in all three branches: [xor64_repr] /
    [sub64_repr] reduce it to the Z goal [Z.lxor (zeta s) mask - 1 =
    zeta (fst (zstep s))], then for H ([zg] even) the mask is [0]
    ([Z.lxor_0_r], model [zeta - 1]); for D ([zg] odd, [zeta<0]) the mask is
    [-1] ([Z.lxor z (-1) = Z.lnot z = - z - 1] via [Z.lnot_eq_pred_opp], model
    [- zeta - 2]); for S ([zg] odd, [zeta>=0]) the mask is [0] (model
    [zeta - 1]).  Each closes by [lia]/[reflexivity]. *)
Lemma body_secp256k1_modinv64_divsteps_59:
  semax_body Vprog Gprog
    f_secp256k1_modinv64_divsteps_59 spec_secp256k1_modinv64_divsteps_59.
Proof.
  start_function.

  (* ===== Init: u=8, v=0, q=0, r=8, f=f0, g=g0; loop i = 3..61 (59 divsteps) ===== *)

  (* uint64_t u = 8 *)
  forward.
  (* uint64_t v = 0 *)
  forward.
  (* uint64_t q = 0 *)
  forward.
  (* uint64_t r = 8 *)
  forward.

  (* uint64_t f = f0 *)
  forward.
  (* uint64_t g = g0 *)
  forward.

  (* for (i = 3; i < 62; ++i) -- 59 constant-time divsteps *)
  forward_for_simple_bound 62
    (EX i:Z, EX f:Z, EX g:Z,
     PROP (eqm (2^(64 - (i-3))) f (divstep_zeta.zf (fst (divstep_zeta.zstep_n (Z.to_nat (i-3)) st)));
           eqm (2^(64 - (i-3))) g (divstep_zeta.zg (fst (divstep_zeta.zstep_n (Z.to_nat (i-3)) st))))
     LOCAL (temp _g (Vlong (Int64.repr g)); temp _f (Vlong (Int64.repr f));
       temp _r (Vlong (Int64.repr (divstep_trans.Trans.r (divstep_zeta.scale_m 8 (divstep_zeta.ztrans_n (Z.to_nat (i-3)) st)))));
       temp _q (Vlong (Int64.repr (divstep_trans.Trans.q (divstep_zeta.scale_m 8 (divstep_zeta.ztrans_n (Z.to_nat (i-3)) st)))));
       temp _v (Vlong (Int64.repr (divstep_trans.Trans.v (divstep_zeta.scale_m 8 (divstep_zeta.ztrans_n (Z.to_nat (i-3)) st)))));
       temp _u (Vlong (Int64.repr (divstep_trans.Trans.u (divstep_zeta.scale_m 8 (divstep_zeta.ztrans_n (Z.to_nat (i-3)) st)))));
       temp _zeta (Vlong (Int64.repr (divstep_zeta.zeta (fst (divstep_zeta.zstep_n (Z.to_nat (i-3)) st)))));
       temp _f0 (Vlong (Int64.repr (divstep_zeta.zf st)));
       temp _g0 (Vlong (Int64.repr (divstep_zeta.zg st))); temp _t t)
     SEP (data_at_ sh t_secp256k1_modinv64_trans2x2 t))%assert.

  (* ===== Loop entry: the i=3 (n=0) invariant holds for ztrans_n 0 = 8*I ===== *)
  - Exists (divstep_zeta.zf st) (divstep_zeta.zg st).
    change (Z.to_nat (3-3)) with 0%nat.
    change (64 - (3-3)) with 64.

    unfold divstep_zeta.ztrans_n, divstep_zeta.zstep_n.
    cbn [snd map divstep_trans.Trans.prod fold_right].
    unfold divstep_zeta.scale_m, divstep_trans.Trans.I.
    cbn [divstep_trans.Trans.u divstep_trans.Trans.v divstep_trans.Trans.q divstep_trans.Trans.r].
    entailer!!.

  (* ===== Loop body: one constant-time zeta-divstep ===== *)
  - Intros.
    rename H1 into Hf.
    rename H2 into Hg.
    set (n := Z.to_nat (i-3)) in *.
    assert (Hni : Z.of_nat n = i - 3) by (subst n; rewrite Z2Nat.id; lia).
    assert (Hn59 : (n <= 59)%nat) by lia.
    set (s := fst (divstep_zeta.zstep_n n st)) in *.

    (* Setup: zeta-range (for the signed >>63), parity bridge g <-> zg s *)
    assert (Hzbnd : -1181 <= divstep_zeta.zeta s <= 1181).
    { assert (HB := divstep_zeta.zeta_bounds n st).
      subst s.
      assert (Z.abs (divstep_zeta.zeta st) <= 1063) by lia.
      lia. }

    assert (Hmod2 : g mod 2 = divstep_zeta.zg s mod 2).
    { assert (Hdvd2 : (2 | 2 ^ (64 - (i - 3)))) by (apply divide_2_pow; lia).
      assert (Hpow2 : 0 < 2 ^ (64 - (i - 3))) by (apply Z.pow_pos_nonneg; lia).
      rewrite (Zmod_div_mod 2 (2 ^ (64 - (i - 3))) g) by (lia || exact Hdvd2).
      rewrite (Zmod_div_mod 2 (2 ^ (64 - (i - 3))) (divstep_zeta.zg s)) by (lia || exact Hdvd2).
      unfold eqm in Hg.
      rewrite Hg.
      reflexivity. }

    assert (Hpar : Z.odd g = Z.odd (divstep_zeta.zg s)).
    { generalize Hmod2.
      rewrite (Zmod_odd g), (Zmod_odd (divstep_zeta.zg s)).
      destruct (Z.odd g), (Z.odd (divstep_zeta.zg s)); congruence. }

    (* ===== Masks: c1/mask1 = (zeta<0), c2/mask2 = (g&1); x,y,z = +-f,u,v ===== *)

    (* c1 = zeta >> 63 *)
    forward.
    (* mask1 = c1 *)
    forward.
    (* c2 = g & 1 *)
    forward.
    (* mask2 = -c2 *)
    forward.

    (* x = (f ^ mask1) - mask1 *)
    forward.
    (* y = (u ^ mask1) - mask1 *)
    forward.
    (* z = (v ^ mask1) - mask1 *)
    forward.

    (* normalize the three masks to clean Int64.repr forms *)
    change (Int.unsigned (Int.repr 63)) with 63.
    rewrite (Int64_shr_sign_mask (divstep_zeta.zeta s)) by rep_lia.

    rewrite (Int64_xor_sub_mask f (divstep_zeta.zeta s <? 0)).
    rewrite (Int64_xor_sub_mask (divstep_trans.Trans.u (divstep_zeta.scale_m 8 (divstep_zeta.ztrans_n n st))) (divstep_zeta.zeta s <? 0)).
    rewrite (Int64_xor_sub_mask (divstep_trans.Trans.v (divstep_zeta.scale_m 8 (divstep_zeta.ztrans_n n st))) (divstep_zeta.zeta s <? 0)).

    change (Int.signed (Int.repr 1)) with 1.
    rewrite Int64_and_low1.

    assert (Hm2v : Int64.neg (Int64.repr (g mod 2)) =
                   Int64.repr (if Z.odd (divstep_zeta.zg s) then -1 else 0)).
    { rewrite Int64.neg_repr, Zmod_odd, Hpar.
      destruct (Z.odd (divstep_zeta.zg s)); reflexivity. }

    rewrite Hm2v.

    (* ===== Conditional add of x,y,z to g,q,r (taken when g is odd) ===== *)

    (* g += x & mask2 *)
    forward.
    (* q += y & mask2 *)
    forward.
    (* r += z & mask2 *)
    forward.
    rewrite !Int64_and_mask.
    rewrite !add64_repr.

    (* ===== D-mask (g odd AND zeta<0), then the branchless zeta update ===== *)

    (* mask1 &= mask2 *)
    forward.
    rewrite Int64_and_mask.

    set (cD := (Z.odd (divstep_zeta.zg s) && (divstep_zeta.zeta s <? 0))%bool).
    assert (HcD : (if Z.odd (divstep_zeta.zg s) then (if divstep_zeta.zeta s <? 0 then -1 else 0) else 0) =
                  (if cD then -1 else 0)).
    { unfold cD.
      destruct (Z.odd (divstep_zeta.zg s)), (divstep_zeta.zeta s <? 0); reflexivity. }

    rewrite !HcD.

    (* zeta = (zeta ^ mask1) - 1 *)
    forward.

    (* ===== Conditional add of g,q,r to f,u,v, then the three shifts ===== *)

    (* f += g & mask1 *)
    forward.
    (* u += q & mask1 *)
    forward.
    (* v += r & mask1 *)
    forward.

    (* g >>= 1 *)
    forward.
    (* u <<= 1 *)
    forward.
    (* v <<= 1 *)
    forward.

    (* ===== Loop back: collapse the words and re-establish the invariant at n+1 ===== *)

    rewrite !Int64_and_mask.
    rewrite !add64_repr.
    change (Int.unsigned (Int.repr 1)) with 1.
    rewrite !Int64_shl1.
    rewrite Int64_shru1.

    assert (HSn : Z.to_nat (i + 1 - 3) = S n).
    { subst n.
      rewrite <- Z2Nat.inj_succ by lia.
      f_equal.
      lia. }

    rewrite !HSn.
    change (Int.signed (Int.repr 1)) with 1.

    Exists (f + (if cD then (g + (if Z.odd (divstep_zeta.zg s) then if divstep_zeta.zeta s <? 0 then - f else f else 0)) else 0)).
    Exists (Z.shiftr ((g + (if Z.odd (divstep_zeta.zg s) then if divstep_zeta.zeta s <? 0 then - f else f else 0)) mod Int64.modulus) 1).

    rewrite (divstep_zeta.scale_m_ztrans_n_s 8 n st).
    rewrite (divstep_zeta.zstep_n_fst_s n st).
    fold s.

    (* the zeta word [(zeta ^ mask1) - 1] matches the model in all three branches *)
    assert (Hzeta : Int64.sub (Int64.xor (Int64.repr (divstep_zeta.zeta s)) (Int64.repr (if cD then -1 else 0))) (Int64.repr 1) =
                    Int64.repr (divstep_zeta.zeta (fst (divstep_zeta.zstep s)))).
    { (* reduce the [Int64] LHS to [Z.lxor (zeta s) mask - 1] over Z *)
      rewrite xor64_repr, sub64_repr.
      f_equal.
      unfold cD, divstep_zeta.zstep.

      destruct (Zeven_odd_dec (divstep_zeta.zg s)) as [Hev|Hodd].
      + (* H: zg even -> mask 0, [Z.lxor z 0 = z]; model H-case [zeta s - 1] *)
        assert (Hoddf : Z.odd (divstep_zeta.zg s) = false).
        { apply Zeven_bool_iff in Hev.
          rewrite Zodd_even_bool, Hev.
          reflexivity. }

        rewrite Hoddf.
        simpl andb.
        rewrite Z.lxor_0_r.
        cbn [fst divstep_zeta.zeta].
        reflexivity.

      + (* zg odd: the sign of zeta selects D ([zeta<0]) or S ([zeta>=0]) *)
        assert (Hoddt : Z.odd (divstep_zeta.zg s) = true) by (rewrite Zodd_bool_iff; exact Hodd).
        rewrite Hoddt.
        simpl andb.
        destruct (divstep_zeta.zeta s <? 0) eqn:Hsgn.

        * (* D: mask -1, [Z.lxor z (-1) = Z.lnot z = - z - 1]; model D-case [- zeta s - 2] *)
          rewrite Z.lxor_m1_r, Z.lnot_eq_pred_opp.
          cbn [fst divstep_zeta.zeta].
          lia.

        * (* S: mask 0, [Z.lxor z 0 = z]; model S-case [zeta s - 1] *)
          rewrite Z.lxor_0_r.
          cbn [fst divstep_zeta.zeta].
          lia. }

    rewrite Hzeta.

    unfold divstep_zeta.zstep.
    destruct (Zeven_odd_dec (divstep_zeta.zg s)) as [Hev|Hodd].

    + (* H case: g even -- f kept, g halved, matrix row u/v doubled *)
      assert (Hoddf : Z.odd (divstep_zeta.zg s) = false).
      { apply Zeven_bool_iff in Hev.
        rewrite Zodd_even_bool, Hev.
        reflexivity. }
      assert (HcDf : cD = false) by (unfold cD; rewrite Hoddf; reflexivity).

      rewrite Hoddf, HcDf.
      cbn [fst snd divstep_trans.Trans.trans divstep_trans.Trans.mul divstep_trans.Trans.u divstep_trans.Trans.v
           divstep_trans.Trans.q divstep_trans.Trans.r divstep_zeta.scale_m divstep_zeta.zf divstep_zeta.zg].
      rewrite !Z.add_0_r, !Z.mul_0_l, !Z.mul_1_l, !Z.add_0_l.

      entailer!!.
      split.

      * (* f unchanged: weaken modulus 2^(64-n) -> 2^(63-n) *)
        replace (64 - (i + 1 - 3)) with (63 - (i - 3)) by lia.
        apply (extra_math.eqm_2_pow_le (63 - (i-3)) (64 - (i-3))).
        { lia. }
        exact Hf.

      * (* g halved: (g mod 2^64)/2 ~ (zg s)/2 mod 2^(63-n) *)
        replace (64 - (i + 1 - 3)) with (63 - (i - 3)) by lia.
        rewrite Z.shiftr_div_pow2 by lia.
        change (2^1) with 2.

        assert (Hgmod : eqm (2 ^ (64 - (i - 3))) (g mod Int64.modulus) (divstep_zeta.zg s)).
        { assert (Hdvd : (2^(64-(i-3)) | Int64.modulus)).
          { change Int64.modulus with (2^64).
            apply divide_pow2_pow2.
            lia. }
          unfold eqm.
          rewrite (Z.mod_mod_divide g Int64.modulus (2^(64-(i-3))) Hdvd).
          exact Hg. }

        unfold eqm.
        unfold eqm in Hgmod.
        rewrite <- !Z.land_ones by lia.
        rewrite <- !(Z.shiftr_div_pow2 _ 1) by lia.
        replace (63 - (i-3)) with (64 - (i-3) - 1) by lia.
        rewrite <- !extra_math.Z_shiftr_ones, <- !Z.shiftr_land by lia.
        rewrite !extra_math.Z_shiftr_ones by lia.
        rewrite !Z.land_ones by lia.
        rewrite Hgmod.
        reflexivity.

    + (* D/S case: g odd -- sign of zeta selects D (zeta<0) or S (zeta>=0) *)
      assert (Hoddt : Z.odd (divstep_zeta.zg s) = true) by (rewrite Zodd_bool_iff; exact Hodd).
      rewrite Hoddt.
      destruct (divstep_zeta.zeta s <? 0) eqn:Hsgn.

      * (* D: f := g, g := (g-f)/2, matrix left-mult by trans D *)
        assert (HcDt : cD = true) by (unfold cD; rewrite Hoddt; reflexivity).
        rewrite HcDt.
        cbn [fst snd divstep_trans.Trans.trans divstep_trans.Trans.mul divstep_trans.Trans.u divstep_trans.Trans.v
             divstep_trans.Trans.q divstep_trans.Trans.r divstep_zeta.scale_m divstep_zeta.zf divstep_zeta.zg].
        rewrite !Z.mul_0_l, !Z.mul_1_l, !Z.add_0_l.

        entailer!!.
        repeat split; try (f_equal; f_equal; ring).

        -- (* f0 = g: model zf' = zg s *)
           replace (f + (g + - f)) with g by ring.
           replace (64 - (i + 1 - 3)) with (63 - (i - 3)) by lia.
           apply (extra_math.eqm_2_pow_le (63 - (i-3)) (64 - (i-3))).
           { lia. }
           exact Hg.

        -- (* g0 = (g-f)/2: model zg' = (zg s - zf s)/2 *)
           replace (g + - f) with (g - f) by ring.
           replace (64 - (i + 1 - 3)) with (63 - (i - 3)) by lia.
           rewrite Z.shiftr_div_pow2 by lia.
           change (2^1) with 2.

           assert (Hgfmod : eqm (2 ^ (64 - (i - 3))) ((g - f) mod Int64.modulus) (divstep_zeta.zg s - divstep_zeta.zf s)).
           { assert (Hdvd : (2^(64-(i-3)) | Int64.modulus)).
             { change Int64.modulus with (2^64).
               apply divide_pow2_pow2.
               lia. }
             unfold eqm.
             rewrite (Z.mod_mod_divide (g - f) Int64.modulus (2^(64-(i-3))) Hdvd).
             apply Zminus_eqm.
             - exact Hg.
             - exact Hf. }

           unfold eqm.
           unfold eqm in Hgfmod.
           rewrite <- !Z.land_ones by lia.
           rewrite <- !(Z.shiftr_div_pow2 _ 1) by lia.
           replace (63 - (i-3)) with (64 - (i-3) - 1) by lia.
           rewrite <- !extra_math.Z_shiftr_ones, <- !Z.shiftr_land by lia.
           rewrite !extra_math.Z_shiftr_ones by lia.
           rewrite !Z.land_ones by lia.
           rewrite Hgfmod.
           reflexivity.

      * (* S: f kept, g := (g+f)/2, matrix left-mult by trans S *)
        assert (HcDf : cD = false) by (unfold cD; apply andb_false_r).
        rewrite HcDf.
        cbn [fst snd divstep_trans.Trans.trans divstep_trans.Trans.mul divstep_trans.Trans.u divstep_trans.Trans.v
             divstep_trans.Trans.q divstep_trans.Trans.r divstep_zeta.scale_m divstep_zeta.zf divstep_zeta.zg].

        entailer!!.
        repeat split; try (f_equal; f_equal; ring).

        -- (* f0 = f: model zf' = zf s *)
           replace (f + 0) with f by ring.
           replace (64 - (i + 1 - 3)) with (63 - (i - 3)) by lia.
           apply (extra_math.eqm_2_pow_le (63 - (i-3)) (64 - (i-3))).
           { lia. }
           exact Hf.

        -- (* g0 = (g+f)/2: model zg' = (zg s + zf s)/2 *)
           replace (64 - (i + 1 - 3)) with (63 - (i - 3)) by lia.
           rewrite Z.shiftr_div_pow2 by lia.
           change (2^1) with 2.

           assert (Hgfmod : eqm (2 ^ (64 - (i - 3))) ((g + f) mod Int64.modulus) (divstep_zeta.zg s + divstep_zeta.zf s)).
           { assert (Hdvd : (2^(64-(i-3)) | Int64.modulus)).
             { change Int64.modulus with (2^64).
               apply divide_pow2_pow2.
               lia. }
             unfold eqm.
             rewrite (Z.mod_mod_divide (g + f) Int64.modulus (2^(64-(i-3))) Hdvd).
             apply Zplus_eqm.
             - exact Hg.
             - exact Hf. }

           unfold eqm.
           unfold eqm in Hgfmod.
           rewrite <- !Z.land_ones by lia.
           rewrite <- !(Z.shiftr_div_pow2 _ 1) by lia.
           replace (63 - (i-3)) with (64 - (i-3) - 1) by lia.
           rewrite <- !extra_math.Z_shiftr_ones, <- !Z.shiftr_land by lia.
           rewrite !extra_math.Z_shiftr_ones by lia.
           rewrite !Z.land_ones by lia.
           rewrite Hgfmod.
           reflexivity.

  (* ===== After the loop (i=62, n=59): store t->{u,v,q,r}; return zeta ===== *)
  - Intros f g.
    change (Z.to_nat (62 - 3)) with 59%nat.

    (* t->u = (int64_t)u *)
    forward.
    (* t->v = (int64_t)v *)
    forward.
    (* t->q = (int64_t)q *)
    forward.
    (* t->r = (int64_t)r *)
    forward.

    (* return zeta *)
    forward.
Qed.
