(** * verif.modinv.modinv64: body proof for secp256k1_modinv64 (constant-time driver). *)
(** Copyright (C) 2026 remix7531
    Ported from BlockstreamResearch/simplicity Coq/C/secp256k1/verif_modinv64_impl.v
    (commit c1dddedd), Copyright (c) 2018 Blockstream, originally MIT.
    Upstream notice reproduced in proof/README.md.
    SPDX-License-Identifier: MIT *)

Require Import secp256k1.vst.base.

Require Import secp256k1.contract.helper.structs_modinv.
Require Import secp256k1.contract.impl.modinv.
Require Import secp256k1.contract.gprog.modinv.

Require Import secp256k1.theory.extra_math.
Require Import secp256k1.theory.modinv.divsteps.bound590.
Require Import secp256k1.theory.modinv.construction.inverse.
Require secp256k1.theory.modinv.construction.divstep.
Require secp256k1.theory.modinv.construction.divstep_trans.
Require secp256k1.theory.modinv.construction.divstep_zeta.

Require Import secp256k1.tactics.hygiene.

(* ================================================================= *)
(** ** secp256k1_modinv64 -- constant-time safegcd modular inverse (590 divsteps). *)

(** The fixed-schedule (10x59 = 590 divsteps) constant-time counterpart of
    secp256k1_modinv64_var.  Mirrors the _var driver port but with the const
    divsteps_59 / update_fg_62 and a fixed [for(i=0;i<10;++i)] loop (no
    convergence break), relying on the 590-divstep convergence (example590).
    Uses the zeta machine (zstep / zstep_n / ztrans_n, eta = -delta encoding). *)
Lemma body_secp256k1_modinv64:
  semax_body Vprog Gprog
    f_secp256k1_modinv64 spec_secp256k1_modinv64.
Proof.
  start_function.

  (* ===== Leading inits: d = {{0,0,0,0,0}}, e = {{1,0,0,0,0}}, zeta = -1 ===== *)

  (* secp256k1_modinv64_signed62 d = {{0, 0, 0, 0, 0}} *)
  forward. (* d.v[0] = 0 *)
  forward. (* d.v[1] = 0 *)
  forward. (* d.v[2] = 0 *)
  forward. (* d.v[3] = 0 *)
  forward. (* d.v[4] = 0 *)
  change (upd_Znth 4 _ _) with (map Vlong (Signed62.reprn 5 0)).

  (* secp256k1_modinv64_signed62 e = {{1, 0, 0, 0, 0}} *)
  forward. (* e.v[0] = 1 *)
  forward. (* e.v[1] = 0 *)
  forward. (* e.v[2] = 0 *)
  forward. (* e.v[3] = 0 *)
  forward. (* e.v[4] = 0 *)
  change (upd_Znth 4 _ _) with (map Vlong (Signed62.reprn 5 1)).

  (* int64_t zeta = -1 *)
  forward.

  (* ===== f = modulus, g = x -- the two signed62_assign calls ===== *)

  (* secp256k1_modinv64_signed62_assign(&f, &modinfo->modulus) -- split the
     modinfo struct so the &modulus field address is available as an argument *)
  unfold make_modinfo.
  unfold_data_at (data_at _ _ _ modinfo).
  assert_PROP (field_compatible t_secp256k1_modinv64_modinfo (DOT _modulus) modinfo) by entailer.

  forward_call (m, v_f, field_address t_secp256k1_modinv64_modinfo (DOT _modulus) modinfo,
                Tsh, sh_modinfo).
  { rewrite field_address_offset by assumption.
    entailer!!. }

  (* refold the &modulus field-at back into the modinfo struct data-at *)
  change (data_at sh_modinfo t_secp256k1_modinv64_signed62) with
    (data_at sh_modinfo (nested_field_type t_secp256k1_modinv64_modinfo (DOT _modulus))).
  rewrite <- field_at_data_at.

  assert (Hmodinfo :
    ((field_at sh_modinfo t_secp256k1_modinv64_modinfo (DOT _modulus) (map Vlong (Signed62.reprn 5 m)) modinfo) *
     (field_at sh_modinfo t_secp256k1_modinv64_modinfo (DOT _modulus_inv62) (Vlong (Int64.repr (mod_inv m (2 ^ 62)))) modinfo) |--
     data_at sh_modinfo t_secp256k1_modinv64_modinfo (map Vlong (Signed62.reprn 5 m), Vlong (Int64.repr (mod_inv m (2 ^ 62)))) modinfo))
    by (unfold_data_at (data_at _ _ _ modinfo); entailer!!).

  sep_apply Hmodinfo.
  fold (make_modinfo m).
  clear Hmodinfo.

  (* secp256k1_modinv64_signed62_assign(&g, x) *)
  forward_call.

  (* ===== Set up the zeta divstep model state and the f/g bounds ===== *)

  change (Int64.repr (Int.signed (Int.neg (Int.repr 1)))) with (Int64.repr (-1)).
  rewrite <- Zodd_equiv in H.
  set (init := divstep_zeta.zinit m x H).

  (* f stays in [-m, m]; g stays strictly inside (-m, m), for all step counts *)
  assert (HfBound : forall i, -m <= divstep_zeta.zf (fst (divstep_zeta.zstep_n i init)) <= m).
  { clear -H0 H1.
    intro i.
    destruct (divstep_zeta.zfg_bounds init i) as [Hf _].
    change (divstep_zeta.zf init) with m in *.
    change (divstep_zeta.zg init) with x in *.
    rewrite (Z.abs_eq m), (Z.abs_eq x) in Hf by lia.
    rewrite Z.max_l in Hf by lia.
    lia. }

  assert (HgBound : forall i, -m < divstep_zeta.zg (fst (divstep_zeta.zstep_n i init)) < m).
  { clear -H0 H1.
    intro i.
    case (divstep_zeta.zfg_bounds_strict init i).
    { change (divstep_zeta.zf init) with m.
      change (divstep_zeta.zg init) with x.
      rewrite (Z.abs_eq m), (Z.abs_eq x) by lia.
      lia. }
    intros _ Hg.
    change (divstep_zeta.zf init) with m in Hg.
    change (divstep_zeta.zg init) with x in Hg.
    rewrite (Z.abs_eq m), (Z.abs_eq x) in Hg by lia.
    rewrite Z.max_l in Hg by lia.
    lia. }

  (* ===== Main for(i=0;i<10;++i) loop: 10 * 59 = 590 divsteps ===== *)

  forward_for_simple_bound 10 (EX i:Z, EX d:Z, EX e:Z,
    PROP ( -2 * m < d < m
         ; -2 * m < e < m
         ; eqm m (x * d) (divstep_zeta.zf (fst (divstep_zeta.zstep_n (59 * Z.to_nat i) init)))
         ; eqm m (x * e) (divstep_zeta.zg (fst (divstep_zeta.zstep_n (59 * Z.to_nat i) init)))
         ; x = 0 -> d = 0
         )
    LOCAL (temp _zeta (Vlong (Int64.repr (divstep_zeta.zeta (fst (divstep_zeta.zstep_n (59 * Z.to_nat i) init)))));
      lvar _t t_secp256k1_modinv64_trans2x2 v_t;
      lvar _g t_secp256k1_modinv64_signed62 v_g;
      lvar _f t_secp256k1_modinv64_signed62 v_f;
      lvar _e t_secp256k1_modinv64_signed62 v_e;
      lvar _d t_secp256k1_modinv64_signed62 v_d;
      temp _x ptrx; temp _modinfo modinfo)
    SEP (
      data_at (cs := CompSpecs) Tsh t_secp256k1_modinv64_signed62 (map Vlong (Signed62.reprn 5 (divstep_zeta.zg (fst (divstep_zeta.zstep_n (59 * Z.to_nat i) init))))) v_g;
      data_at (cs := CompSpecs) shx t_secp256k1_modinv64_signed62 (map Vlong (Signed62.reprn 5 x)) ptrx;
      data_at (cs := CompSpecs) sh_modinfo t_secp256k1_modinv64_modinfo (make_modinfo m) modinfo;
      data_at (cs := CompSpecs) Tsh t_secp256k1_modinv64_signed62 (map Vlong (Signed62.reprn 5 (divstep_zeta.zf (fst (divstep_zeta.zstep_n (59 * Z.to_nat i) init))))) v_f;
      data_at_ (cs := CompSpecs) Tsh t_secp256k1_modinv64_trans2x2 v_t;
      data_at (cs := CompSpecs) Tsh t_secp256k1_modinv64_signed62 (map Vlong (Signed62.reprn 5 e)) v_e;
      data_at (cs := CompSpecs) Tsh t_secp256k1_modinv64_signed62 (map Vlong (Signed62.reprn 5 d)) v_d)
    )%assert.

  - (* ===== Loop entry: i = 0, d = 0, e = 1 ===== *)

    Exists 0 1.
    change (Z.to_nat 0) with 0%nat.
    change (59 * 0)%nat with 0%nat.
    simpl (divstep_zeta.zstep_n 0 init).
    change (divstep_zeta.zf (fst (init, _))) with m.
    change (divstep_zeta.zg (fst (init, @nil divstep.Step))) with x.
    change (divstep_zeta.zeta (fst (init, @nil divstep.Step))) with (-1).
    entailer!!.

    split.
    + (* conjunct: eqm m (x * 0) m -- both sides are 0 mod m *)
      unfold eqm.
      rewrite Z.mul_0_r, Z.mod_0_l, Z.mod_same by lia.
      lia.

    + (* conjunct: eqm m (x * 1) x -- reflexivity *)
      apply eqm_refl.

  - (* ===== Loop body: read f[0]/g[0], divsteps_59, update_de_62, update_fg_62 ===== *)

    Intros.
    rename H5 into Hdbnd.
    rename H6 into Hebnd.
    rename H7 into Hxd_i.
    rename H8 into Hxe_i.
    rename H9 into Hd0_i.

    set (sti := fst (divstep_zeta.zstep_n (59 * Z.to_nat i) init)) in *.
    set (fi := divstep_zeta.zf sti) in *.
    set (gi := divstep_zeta.zg sti) in *.

    assert (Hlf : Zlength (Signed62.reprn 5 fi) = 5) by (rewrite Signed62.reprn_Zlength; reflexivity).
    assert (Hlg : Zlength (Signed62.reprn 5 gi) = 5) by (rewrite Signed62.reprn_Zlength; reflexivity).

    (* read f[0] and g[0] -- the bottom limbs fed to divsteps_59 *)
    forward. (* _t'3 = f.v[0] *)
    forward. (* _t'4 = g.v[0] *)

    rewrite !Signed62.reprn_Znth by lia.
    change (62 * 0) with 0.
    rewrite !Z.shiftr_0_r.

    (* build the call state stCall from the bottom limbs (mod 2^62), with the zeta bound *)
    assert (Hfi0Odd : Zodd (fi mod 2^62)).
    { apply Zodd_bool_iff.
      rewrite <- Zbits.Ztestbit_base, <-Z.land_ones, Z.land_spec, Zbits.Ztestbit_base, andb_true_r by lia.
      apply Zodd_bool_iff.
      unfold fi.
      apply divstep_zeta.zodd_f. }

    set (stCall := {| divstep_zeta.zeta := divstep_zeta.zeta sti; divstep_zeta.zf := fi mod 2^62; divstep_zeta.zg := gi mod 2^62; divstep_zeta.zodd_f := Hfi0Odd |}).

    assert (HzetaCall : -1063 <= divstep_zeta.zeta stCall <= 1063).
    { change (divstep_zeta.zeta stCall) with (divstep_zeta.zeta sti).
      unfold sti.
      assert (Hzb := divstep_zeta.zeta_bounds (59 * Z.to_nat i) init).
      change (divstep_zeta.zeta init) with (-1) in Hzb.
      change (Z.abs (-1)) with 1 in Hzb.
      assert (Z.to_nat i <= 9)%nat by lia.
      assert (Z.of_nat (59 * Z.to_nat i) <= 531) by lia.
      lia. }

    (* _t'1 = secp256k1_modinv64_divsteps_59(zeta, _t'3, _t'4, &t) *)
    forward_call (stCall, v_t, Tsh).

    (* zeta = _t'1 *)
    forward.

    (* the mod-2^62 truncation of the bottom limbs does not change the 59-step result *)
    assert (HmodEq : forall z, eqm (2^Z.of_nat 59) (z mod 2^62) z).
    { intros z.
      unfold eqm.
      change (Z.of_nat 59) with 59.
      rewrite <- !Z.land_ones by lia.
      rewrite <- Z.land_assoc.
      change (Z.land (Z.ones 62) (Z.ones 59)) with (Z.ones 59).
      reflexivity. }

    assert (HbridgeZeta : divstep_zeta.zeta (fst (divstep_zeta.zstep_n 59 stCall)) = divstep_zeta.zeta (fst (divstep_zeta.zstep_n 59 sti))
                       /\ snd (divstep_zeta.zstep_n 59 stCall) = snd (divstep_zeta.zstep_n 59 sti)).
    { apply divstep_zeta.zstep_n_mod.
      - (* the f argument agrees mod 2^59 *)
        change (divstep_zeta.zf stCall) with (fi mod 2^62).
        apply HmodEq.
      - (* the g argument agrees mod 2^59 *)
        change (divstep_zeta.zg stCall) with (gi mod 2^62).
        apply HmodEq.
      - (* the zeta arguments are literally equal *)
        reflexivity. }

    destruct HbridgeZeta as [HbridgeZeta HbridgeSnd].

    assert (HbridgeMtx : divstep_zeta.ztrans_n 59 stCall = divstep_zeta.ztrans_n 59 sti).
    { unfold divstep_zeta.ztrans_n.
      rewrite HbridgeSnd.
      reflexivity. }

    rewrite HbridgeMtx, HbridgeZeta.

    (* the call matrix scale_m 8 (ztrans_n 59 sti) is bounded by 2^62 = 8 * 2^59 *)
    assert (Hbounded62 : divstep_trans.Trans.bounded (2 ^ 62) (divstep_zeta.scale_m 8 (divstep_zeta.ztrans_n 59 sti))).
    { assert (H62 : (2:Z) ^ 62 = 8 * 2 ^ 59) by (vm_compute; reflexivity).
      rewrite H62.
      clear H62.
      apply divstep_zeta.bounded_scale_m.
      { lia. }
      change (2 ^ 59) with (2 ^ Z.of_nat 59).
      apply divstep_zeta.bounded_ztrans_n. }

    (* secp256k1_modinv64_update_de_62(&d, &e, &t, modinfo) *)
    forward_call (d, e, divstep_zeta.scale_m 8 (divstep_zeta.ztrans_n 59 sti), m, v_d, v_e, v_t, modinfo, Tsh, Tsh, Tsh, sh_modinfo).
    { apply Zodd_equiv.
      assumption. }

    (* secp256k1_modinv64_update_fg_62(&f, &g, &t) -- the proved generic spec
       gives (u*fi + v*gi)/2^62 and (q*fi + r*gi)/2^62 *)
    forward_call (fi, gi, divstep_zeta.scale_m 8 (divstep_zeta.ztrans_n 59 sti), v_f, v_g, v_t, Tsh, Tsh, Tsh).
    { assert (Hm311 : m < 2 ^ (62 * 5 + 1)).
      { eapply Z.lt_trans.
        { apply (proj2 H1). }
        apply Z.pow_lt_mono_r; lia. }
      assert (HfiB : - m <= fi <= m) by apply (HfBound (59 * Z.to_nat i)%nat).
      assert (HgiB : - m < gi < m) by apply (HgBound (59 * Z.to_nat i)%nat).
      split; lia. }

    (* ===== Re-establish the loop invariant for iteration i+1 ===== *)

    (* the next state is one 59-block on from sti *)
    assert (Hsti' : fst (divstep_zeta.zstep_n (59 * Z.to_nat (i + 1)) init) = fst (divstep_zeta.zstep_n 59 sti)).
    { unfold sti.
      rewrite <- divstep_zeta.zstep_n_app_fst.
      replace (59 * Z.to_nat (i + 1))%nat with (59 + 59 * Z.to_nat i)%nat by (rewrite Z2Nat.inj_add by lia; change (Z.to_nat 1) with 1%nat; lia).
      reflexivity. }

    (* the matrix-vector relation: ap (scale_m 8 (ztrans_n 59 sti)) (zfg sti) = scale (2^62) (zfg sti') *)
    assert (Hrel : divstep_trans.Trans.ap (divstep_zeta.scale_m 8 (divstep_zeta.ztrans_n 59 sti)) (divstep_zeta.zfg sti)
                 = divstep_trans.Trans.scale (2 ^ 62) (divstep_zeta.zfg (fst (divstep_zeta.zstep_n 59 sti)))).
    { assert (H62 : 8 * 2 ^ Z.of_nat 59 = 2 ^ 62) by (vm_compute; reflexivity).
      rewrite divstep_zeta.ap_scale_m.
      rewrite <- divstep_zeta.ztrans_n_step.
      rewrite <- divstep_trans.Trans.scale_mul.
      rewrite H62.
      reflexivity. }

    (* the f/g floor-divisions equal the model zf/zg of the next state *)
    assert (Hfdiv : (divstep_trans.Trans.u (divstep_zeta.scale_m 8 (divstep_zeta.ztrans_n 59 sti)) * fi +
                     divstep_trans.Trans.v (divstep_zeta.scale_m 8 (divstep_zeta.ztrans_n 59 sti)) * gi) / 2 ^ 62
                  = divstep_zeta.zf (fst (divstep_zeta.zstep_n 59 sti))).
    { assert (Hx := f_equal divstep_trans.Trans.x Hrel).
      unfold divstep_trans.Trans.ap, divstep_trans.Trans.scale, divstep_zeta.zfg in Hx.
      cbn [divstep_trans.Trans.x divstep_trans.Trans.y] in Hx.
      change (divstep_zeta.zf sti) with fi in Hx.
      change (divstep_zeta.zg sti) with gi in Hx.
      rewrite Hx.
      assert (Hp62 : 2 ^ 62 <> 0) by (apply Z.pow_nonzero; lia).
      rewrite Z.mul_comm, Z_div_mult by lia.
      reflexivity. }

    assert (Hgdiv : (divstep_trans.Trans.q (divstep_zeta.scale_m 8 (divstep_zeta.ztrans_n 59 sti)) * fi +
                     divstep_trans.Trans.r (divstep_zeta.scale_m 8 (divstep_zeta.ztrans_n 59 sti)) * gi) / 2 ^ 62
                  = divstep_zeta.zg (fst (divstep_zeta.zstep_n 59 sti))).
    { assert (Hy := f_equal divstep_trans.Trans.y Hrel).
      unfold divstep_trans.Trans.ap, divstep_trans.Trans.scale, divstep_zeta.zfg in Hy.
      cbn [divstep_trans.Trans.x divstep_trans.Trans.y] in Hy.
      change (divstep_zeta.zf sti) with fi in Hy.
      change (divstep_zeta.zg sti) with gi in Hy.
      rewrite Hy.
      assert (Hp62 : 2 ^ 62 <> 0) by (apply Z.pow_nonzero; lia).
      rewrite Z.mul_comm, Z_div_mult by lia.
      reflexivity. }

    (* d', e' bounds and eqm tracking, from the fully applied model lemmas *)
    destruct Hbounded62 as [[Huv _] [Hqr _]].

    destruct (divstep_zeta.update_de_bound m d e
                (divstep_zeta.scale_m 8 (divstep_zeta.ztrans_n 59 sti)) H Huv Hqr Hdbnd Hebnd)
      as [Hdb Heb].

    destruct (divstep_zeta.zupdate_de_eqm_gen m x d e
                (divstep_zeta.scale_m 8 (divstep_zeta.ztrans_n 59 sti)) sti
                (fst (divstep_zeta.zstep_n 59 sti)) H Hrel Hxd_i Hxe_i)
      as [Hxd Hxe].

    (* the x = 0 -> d' = 0 invariant: g is fixed at 0, so the matrix is the
       identity-like H-case matrix and update_de leaves d' = 0 *)
    assert (Hx0d0 : x = 0 -> fst (divstep_zeta.update_de m d e (divstep_zeta.scale_m 8 (divstep_zeta.ztrans_n 59 sti))) = 0).
    { intros Hx0.
      specialize (Hd0_i Hx0).
      assert (Hzg0 : divstep_zeta.zg sti = 0).
      { unfold sti, init.
        apply divstep_zeta.zfixed_g.
        change (divstep_zeta.zg (divstep_zeta.zinit m x H)) with x.
        assumption. }
      assert (HtransHs : divstep_zeta.ztrans_n 59 sti = {| divstep_trans.Trans.u := 2 ^ (Z.of_nat 59); divstep_trans.Trans.v := 0; divstep_trans.Trans.q := 0; divstep_trans.Trans.r := 1 |}).
      { apply divstep_zeta.ztrans_hs.
        rewrite Hzg0.
        apply Z.divide_0_r. }

      rewrite HtransHs.
      unfold divstep_zeta.scale_m, divstep_zeta.update_de, divstep_trans.Trans.ap.
      cbn [divstep_trans.Trans.u divstep_trans.Trans.v divstep_trans.Trans.q divstep_trans.Trans.r divstep_trans.Trans.x divstep_trans.Trans.y].
      rewrite Hd0_i.
      cbn [fst].
      change (0 <? 0) with false.
      change (if false then m else 0) with 0.

      assert (HE : 8 * 2 ^ Z.of_nat 59 * (0 + 0) + 8 * 0 * (e + (if e <? 0 then m else 0)) = 0) by ring.
      rewrite HE.
      unfold divstep_zeta.pre_div62Modulo.
      rewrite Z.mul_0_r, Zmod_0_l, Z.mul_0_l, Z.sub_0_r.
      apply Zdiv_0_l. }

    (* commit the next-iteration invariant: d' / e' as the update_de results *)
    Exists (fst (divstep_zeta.update_de m d e (divstep_zeta.scale_m 8 (divstep_zeta.ztrans_n 59 sti))))
           (snd (divstep_zeta.update_de m d e (divstep_zeta.scale_m 8 (divstep_zeta.ztrans_n 59 sti)))).
    rewrite Hfdiv, Hgdiv.
    rewrite Hsti'.
    entailer!!.

  - (* ===== After the loop (i = 10, 590 divsteps): g = 0, |f| = 1, normalize d into x ===== *)

    Intros d e.
    rename H4 into Hdbnd.
    rename H5 into Hebnd.
    rename H6 into Hxd.
    rename H7 into Hxe.
    rename H8 into Hx0d0.

    change (Z.to_nat 10) with 10%nat in *.
    change (59 * 10)%nat with 590%nat in *.

    set (sti := (fst (divstep_zeta.zstep_n 590 init))) in *.
    set (fi := divstep_zeta.zf sti) in *.
    set (gi := divstep_zeta.zg sti) in *.

    (* g = 0 after 590 divsteps (the constant-time convergence certificate) *)
    assert (Hg0 : gi = 0).
    { unfold gi, sti, init.
      apply example590; lia. }

    (* |f| == 1, or (x == 0 and f == modulus): f is +/- gcd(m, x) (= +/- 1, or m when x=0) *)
    assert (Hverify : (Z.abs fi = 1) \/ (x = 0 /\ fi = m)).
    { destruct (Z.eq_dec x 0) as [Hx0 | Hx0].
      - (* branch: x = 0 -- g stays 0, so f is the preserved initial f = modulus *)
        right.
        split.
        { assumption. }
        unfold fi, sti, init.
        rewrite divstep_zeta.zfixed_f.
        + (* the preserved f is the initial f = m *)
          change (divstep_zeta.zf (divstep_zeta.zinit m x H)) with m.
          reflexivity.
        + (* side condition of zfixed_f: the initial g is 0 *)
          change (divstep_zeta.zg (divstep_zeta.zinit m x H)) with x.
          assumption.

      - (* branch: x <> 0 -- |f| = gcd(m, x) = 1 by coprimality *)
        left.
        rewrite <- Z.gcd_0_r.
        apply Zis_gcd_gcd.
        { lia. }
        rewrite <- Hg0.
        unfold fi, gi, sti, init.
        apply divstep_zeta.zgcd.
        change (divstep_zeta.zf (divstep_zeta.zinit m x H)) with m.
        change (divstep_zeta.zg (divstep_zeta.zinit m x H)) with x.
        apply Zis_gcd_sym.
        destruct H2 as [Hx0' | Hrp].
        + (* x = 0 contradicts this branch *)
          lia.
        + (* the funspec's coprimality hypothesis *)
          apply Hrp. }

    (* ===== read f[4] (sign arg), normalize_62(&d, f[4], modinfo), assign x = d ===== *)

    assert (Hlf : Zlength (Signed62.reprn 5 fi) = 5) by (rewrite Signed62.reprn_Zlength; reflexivity).

    (* _t'2 = f.v[4] -- the top limb = Z.shiftr fi (62*4) *)
    forward.

    replace 4 with (Zlength (Signed62.reprn 5 fi) - 1) by (rewrite Signed62.reprn_Zlength; reflexivity).
    rewrite Znth_last, Signed62.reprn_last by lia.
    change (62 * (Z.of_nat 5 - 1)) with (62 * 4).

    assert (HfiBound590 : - m <= fi <= m) by apply (HfBound 590%nat).

    (* the sign limb fits int64: |fi / 2^248| <= 2^9 *)
    assert (Hshf_bnd : -512 <= Z.shiftr fi (62 * 4) <= 512).
    { assert (Hp : 0 < 2 ^ (62 * 4)) by (apply Z.pow_pos_nonneg; lia).
      assert (Hpe : 2 ^ 9 * 2 ^ (62 * 4) = 2 ^ 257) by (vm_compute; reflexivity).
      assert (Hm257 : m <= 2 ^ 257).
      { apply Z.le_trans with (2 ^ 256).
        - lia.
        - apply Z.pow_le_mono_r; lia. }

      rewrite Z.shiftr_div_pow2 by lia.
      change (-512) with (- 2 ^ 9).
      change 512 with (2 ^ 9).
      split.
      - (* lower bound: -m / 2^248 <= fi / 2^248 *)
        apply Z.le_trans with (- m / 2 ^ (62 * 4)).
        + apply Z.div_le_lower_bound; lia.
        + apply Z.div_le_mono; lia.
      - (* upper bound: fi / 2^248 <= m / 2^248 *)
        apply Z.le_trans with (m / 2 ^ (62 * 4)).
        + apply Z.div_le_mono; lia.
        + apply Z.div_le_upper_bound; lia. }

    (* secp256k1_modinv64_normalize_62(&d, _t'2, modinfo) -- the PRE sign range
       is Hshf_bnd, the remaining PRE bounds discharge automatically *)
    forward_call (d, Z.shiftr fi (62 * 4), m, v_d, modinfo, Tsh, sh_modinfo).

    (* the top limb is negative exactly when fi is *)
    assert (Hsgn : (fi <? 0) = (Z.shiftr fi (62 * 4) <? 0)).
    { apply Bool.eq_true_iff_eq.
      rewrite !Z.ltb_lt.
      rewrite Z.shiftr_neg.
      reflexivity. }

    rewrite <- Hsgn.

    (* the normalized result (if fi < 0 then -d else d) mod m equals mod_inv x m *)
    assert (Hnorm : (if fi <? 0 then - d else d) mod m = mod_inv x m).
    { destruct Hverify as [Habsfi | [Hx0 Hfim]].
      - (* branch: |f| = 1 -- d * sgn f is the inverse of x *)
        apply mod_inv_mul_unique_r.
        replace (if fi <? 0 then - d else d) with (d * Z.sgn fi) by (elim (Z.ltb_spec); lia).
        rewrite Z.mul_assoc.
        rewrite <- Zmult_mod_idemp_l.
        rewrite Hxd.
        rewrite Zmult_mod_idemp_l.
        rewrite Z.sgn_abs.
        rewrite Habsfi.
        apply Z.mod_1_l.
        lia.

      - (* branch: x = 0 -- d = 0 and mod_inv 0 m = 0 *)
        rewrite Hx0.
        rewrite mod_inv_zero.
        specialize (Hx0d0 Hx0).
        rewrite Hx0d0.
        destruct (fi <? 0).
        + reflexivity.
        + reflexivity. }

    rewrite Hnorm.

    (* secp256k1_modinv64_signed62_assign(x, &d) -- write the result back into x *)
    sep_apply (data_at_data_at_ shx t_secp256k1_modinv64_signed62 (map Vlong (Signed62.reprn 5 x)) ptrx).
    forward_call.

    (* property POST: the result limbs hold [mod_inv x m], which satisfies the
       model spec [is_modular_inverse x m].  Prove its three conjuncts (reduced
       range, 0 -> 0, and the coprime-case identity) from [mod_inv]'s number-
       theoretic lemmas -- the bridge content, inline in the verif layer. *)
    Exists (mod_inv x m).
    entailer!!.

    unfold modinv.is_modular_inverse.

    split3.
    + (* conjunct 0: 0 <= mod_inv x m < m *)
      unfold mod_inv.
      apply Z.mod_pos_bound.
      lia.

    + (* conjunct 1: x = 0 -> mod_inv x m = 0 *)
      intros ->.
      apply mod_inv_zero.

    + (* conjunct 2: rel_prime x m -> (x * mod_inv x m) mod m = 1 *)
      intros Hr.
      rewrite mod_inv_mul_r.
      rewrite (proj2 (Zgcd_1_rel_prime x m) Hr).
      apply Z.mod_1_l.
      lia.
Qed.
