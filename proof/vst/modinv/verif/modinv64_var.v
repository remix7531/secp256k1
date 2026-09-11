(** * vst.modinv.verif.modinv64_var: body proof for secp256k1_modinv64_var. *)
(** Copyright (C) 2026 remix7531
    Ported from BlockstreamResearch/simplicity Coq/C/secp256k1/verif_modinv64_impl.v
    (commit c1dddedd), Copyright (c) 2018 Blockstream, originally MIT.
    Upstream notice reproduced in proof/README.md.
    SPDX-License-Identifier: MIT *)

(** Split out from the upstream-ported verif_modinv64_impl.v (one semax_body
    per file, per the project convention). *)

Require Import secp256k1.vst.base.
Require Import secp256k1.vst.helper.structs_modinv.
Require Import secp256k1.vst.modinv.impl.
Require Import secp256k1.vst.gprog.
Require Import secp256k1.theory.integers.extra_math.
Require Import secp256k1.theory.modinv.divsteps.theory.
Require Import secp256k1.theory.modinv.divsteps.bound724.
Require Import secp256k1.theory.modinv.construction.inverse.
Require secp256k1.theory.modinv.construction.divstep.
Require secp256k1.theory.modinv.construction.divstep_trans.
Require secp256k1.theory.modinv.construction.divstep_zeta.
Require Import secp256k1.vst.tactics.core.
Require Import secp256k1.vst.tactics.hygiene.

(* ================================================================= *)
(** ** secp256k1_modinv64_var -- variable-time safegcd modular inverse. *)

(** [secp256k1_modinv64_var(x, modinfo)] computes the modular inverse of [x]
    modulo [modinfo->modulus] in variable time and writes it back into [x].
    Runs the safegcd divstep loop (62 divsteps per iteration, eta=-delta) until
    g=0, shrinking [len] as the top limbs vanish; the postcondition replaces the
    [x] limbs with [mod_inv x m]. *)
Lemma body_secp256k1_modinv64_var: semax_body Vprog Gprog f_secp256k1_modinv64_var spec_secp256k1_modinv64_var.
Proof.
  start_function.

  (* ===== Leading inits: d[0..4]=0, e[0]=1/e[1..4]=0, len=5, eta=-1 =====
     (local C orders the len/eta inits BEFORE the two signed62_assign calls,
     unlike upstream, which does them after; sequence to match the local AST.) *)

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

  (* int len = 5 *)
  forward.

  (* int64_t eta = -1 *)
  forward.
  change (Int.neg (Int.repr 1)) with (Int.repr (-1)).

  (* ===== f = modulus, g = x -- the two signed62_assign calls ===== *)

  (* split the modinfo struct so the &modulus field address is available as an argument *)
  unfold make_modinfo.
  unfold_data_at (data_at _ _ _ modinfo).
  assert_PROP (field_compatible t_secp256k1_modinv64_modinfo (DOT _modulus) modinfo) by entailer.

  (* secp256k1_modinv64_signed62_assign(&f, &modinfo->modulus) *)
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

  (* ===== Set up the divstep model state and the f/g bounds ===== *)

  rewrite <- Zodd_equiv in H.
  set (init := divstep.init m x H).

  (* f stays in (-m, m]; g stays strictly inside (-m, m), for all step counts *)
  assert (HfBound : forall i, -m < divstep.f (fst (divstep.step_n i init)) <= m).
  { clear -H0 H1.
    intro i.
    injection (divstep_trans.Trans.trans_n_step i init).
    intros _.
    destruct (divstep_trans.Trans.bounded_trans_n i init) as [[Huv Huv'] _].
    nia. }

  assert (HgBound : forall i, -m < divstep.g (fst (divstep.step_n i init)) < m).
  { clear -H0 H1.
    intro i.
    case (divstep.fg_bounds_strict init i).
    { cbn.
      lia. }
    intros _.
    change (divstep.f init) with m.
    change (divstep.g init) with x.
    lia. }

  (* ===== Main while(1) loop, with break when g = 0 ===== *)

  (* The invariant is parametrized by the extra postcondition [P] on g (trivial
     going round the loop, [g = 0] on the break edge) and by the step count [f]
     reached at the head of iteration [i]. *)
  set (invariant := fun P f => (EX i:nat, EX len:nat, EX d:Z, EX e:Z,
    PROP ( 0 <= Z.of_nat i < 12
         ; (1 <= len <= 5)%nat
         ; -2^(62 * Z.of_nat len + 1) <= divstep.f (fst (divstep.step_n (f i) init)) <= 2^(62 * Z.of_nat len + 1) - 1
         ; -2^(62 * Z.of_nat len + 1) <= divstep.g (fst (divstep.step_n (f i) init)) <= 2^(62 * Z.of_nat len + 1) - 1
         ; -2 * m < d < m
         ; -2 * m < e < m
         ; eqm m (x * d) (divstep.f (fst (divstep.step_n (f i) init)))
         ; eqm m (x * e) (divstep.g (fst (divstep.step_n (f i) init)))
         ; x = 0 -> d = 0
         ; P (divstep.g (fst (divstep.step_n (f i) init)))
         )
    LOCAL (temp _eta (Vlong (Int64.repr (divstep.eta (fst (divstep.step_n (f i) init)))));
      temp _len (Vint (Int.repr (Z.of_nat len)));
      lvar _t t_secp256k1_modinv64_trans2x2 v_t;
      lvar _g t_secp256k1_modinv64_signed62 v_g;
      lvar _f t_secp256k1_modinv64_signed62 v_f;
      lvar _e t_secp256k1_modinv64_signed62 v_e;
      lvar _d t_secp256k1_modinv64_signed62 v_d;
      gvars gv; temp _x ptrx; temp _modinfo modinfo)
    SEP (
      data_at (cs := CompSpecs) Tsh t_secp256k1_modinv64_signed62 (Signed62.pad (Signed62.reprn len (divstep.g (fst (divstep.step_n (f i) init))))) v_g;
      data_at (cs := CompSpecs) shx t_secp256k1_modinv64_signed62 (map Vlong (Signed62.reprn 5 x)) ptrx;
      data_at (cs := CompSpecs) Tsh t_secp256k1_modinv64_signed62 (Signed62.pad (Signed62.reprn len (divstep.f (fst (divstep.step_n (f i) init))))) v_f;
      data_at_ (cs := CompSpecs) Tsh t_secp256k1_modinv64_trans2x2 v_t;
      data_at (cs := CompSpecs) Tsh t_secp256k1_modinv64_signed62 (map Vlong (Signed62.reprn 5 e)) v_e;
      data_at (cs := CompSpecs) Tsh t_secp256k1_modinv64_signed62 (map Vlong (Signed62.reprn 5 d)) v_d;
      data_at (cs := CompSpecs) sh_modinfo t_secp256k1_modinv64_modinfo (make_modinfo m) modinfo;
      debruijn64_array sh_debruijn gv)
  )%assert).

  (* while (1) { ... if (g == 0) break; ... } *)
  forward_loop (invariant (fun g => True) (fun i => 62 * i)%nat)
    break: (invariant (fun g => g = 0) (fun i => 62 * (i + 1))%nat).

  - (* ===== Loop entry: instantiate the invariant at i=0, len=5, d=0, e=1 ===== *)

    unfold invariant in *.
    clear invariant.
    Exists 0%nat 5%nat 0 1.
    rewrite !Signed62.pad5 by (rewrite Signed62.reprn_length; reflexivity).
    simpl (divstep.step_n (62 * 0) init).
    simpl (divstep.g _).
    simpl (divstep.f _).
    entailer!!.

    split.
    + (* conjunct: eqm m (x * 0) m -- both sides are 0 mod m *)
      unfold eqm.
      rewrite Z.mod_same, Z.mul_0_r, Z.mod_0_l; lia.

    + (* conjunct: eqm m (x * 1) x -- reflexivity *)
      apply eqm_refl.

  - (* ===== Loop body: 62 divsteps, then update_de / update_fg, then shrink len ===== *)

    unfold invariant in *.
    clear invariant.
    Intros i len d e.
    set (sti := (fst (divstep.step_n (62 * i) init))) in *.
    set (fi := divstep.f sti) in *.
    set (gi := divstep.g sti) in *.

    (* _t'7 = f.v[0] -- the bottom limb fed to divsteps_62_var *)
    forward.
    { rewrite Signed62.pad_nth by (rewrite Signed62.reprn_Zlength; lia).
      entailer!!. }
    rewrite Signed62.pad_nth by (rewrite Signed62.reprn_Zlength; lia).

    (* _t'8 = g.v[0] *)
    forward.
    { rewrite Signed62.pad_nth by (rewrite Signed62.reprn_Zlength; lia).
      entailer!!. }
    rewrite Signed62.pad_nth by (rewrite Signed62.reprn_Zlength; lia).

    (* the bottom limb is z (when len=1) or z mod 2^62 (otherwise) *)
    assert (Hi0 : forall z, Znth 0 (Signed62.reprn len z) = Int64.repr (if (len =? 1)%nat then z else z mod 2^62)).
    { intros z.
      destruct len.
      { (* len = 0 is excluded by the PRE bound 1 <= len *)
        lia. }
      destruct len.
      - (* branch: len = 1 -- the single limb is z itself *)
        rewrite Nat.eqb_refl.
        change (Znth 0 (Signed62.reprn 1 z)) with (last (Signed62.reprn 1 z) default).
        rewrite Signed62.reprn_last by lia.
        reflexivity.

      - (* branch: len >= 2 -- the bottom limb is z mod 2^62 *)
        replace (_ =? _)%nat with false by (symmetry; apply Nat.eqb_neq; lia).
        rewrite Signed62.reprn_Znth by lia.
        reflexivity. }

    rewrite !Hi0.

    (* build the divstep state stCall from the bottom limbs fi0, gi0 and its eta bound *)
    set (fi0 := if (len =? 1)%nat then fi else fi mod 2^62).
    set (gi0 := if (len =? 1)%nat then gi else gi mod 2^62).

    assert (Hfi0Odd : Zodd fi0).
    { unfold fi0.
      destruct (len =? 1)%nat.
      - (* branch: len = 1 -- fi0 is fi, odd by [divstep.odd_f] *)
        apply divstep.odd_f.

      - (* branch: len >= 2 -- the low 62 bits keep the parity of fi *)
        apply Zodd_bool_iff.
        rewrite <- Zbits.Ztestbit_base, <-Z.land_ones, Z.land_spec, Zbits.Ztestbit_base, andb_true_r by lia.
        apply Zodd_bool_iff.
        apply divstep.odd_f. }

    set (stCall := {| divstep.delta := divstep.delta sti; divstep.f := _; divstep.g := gi0; divstep.odd_f := Hfi0Odd |}).

    assert (etaStCall : -683 <= divstep.eta stCall < 683).
    { assert (etaInit : -(1) <= divstep.eta init < 1) by (cbn; lia).
      assert (eta_bounds := divstep.eta_bounds 1 (62*i) init etaInit).
      fold sti in eta_bounds.
      change (divstep.eta stCall) with (divstep.eta sti).
      lia. }

    (* _t'1 = secp256k1_modinv64_divsteps_62_var(eta, _t'7, _t'8, &t) *)
    forward_call (stCall, v_t, Tsh, sh_debruijn, gv).

    (* the mod-2^62 truncation of fi/gi does not change the divstep result *)
    assert (Hi0mod : forall z, eqm (2^62) (if (len =? 1)%nat then z else z mod 2^62) z).
    { intros z.
      destruct (_ =? _)%nat.
      - (* branch: len = 1 -- the limb is z itself *)
        reflexivity.

      - (* branch: len >= 2 -- z mod 2^62 agrees with z mod 2^62 *)
        unfold eqm.
        rewrite Z.mod_mod by lia.
        reflexivity. }

    unfold divstep.eta, divstep_trans.Trans.trans_n.
    destruct (divstep.step_n_mod 62 stCall sti (Hi0mod fi) (Hi0mod gi) (eq_refl _)) as [-> ->].
    fold (divstep_trans.Trans.trans_n 62 sti).
    fold (divstep.eta (fst (divstep.step_n 62 sti))).
    clear Hi0mod etaStCall stCall.

    (* eta = _t'1 -- store the returned eta *)
    forward.
    assert (HmOdd : Z.Odd m) by (apply Zodd_equiv; assumption).
    assert (HstiBounded := divstep_trans.Trans.bounded_trans_n 62 sti).

    (* secp256k1_modinv64_update_de_62(&d, &e, &t, modinfo) *)
    forward_call (d, e, divstep_trans.Trans.trans_n 62 sti, m, v_d, v_e, v_t, modinfo, Tsh, Tsh, Tsh, sh_modinfo).
    destruct HstiBounded as [[Huv Huv'] [Hqr Hqr']].
    destruct (divstep_zeta.update_de_bound m d e (divstep_trans.Trans.trans_n 62 sti) H Huv Hqr H9 H10)
      as [Hdm Hem].

    (* name the updated d', e' and carry the x=0 -> d'=0 invariant *)
    set (d' := fst (divstep_zeta.update_de m d e (divstep_trans.Trans.trans_n 62 sti))).
    set (e' := snd (divstep_zeta.update_de m d e (divstep_trans.Trans.trans_n 62 sti))).

    assert (Hx0d'0 : x = 0 -> d' = 0).
    { intros Hx0.
      specialize (H13 Hx0).
      unfold d', sti, init.
      rewrite divstep_trans.Trans.trans_hs.
      - (* the H-case matrix leaves d' = 0 *)
        rewrite H13.
        simpl.
        replace (_ + _) with (0) by ring.
        unfold divstep_zeta.pre_div62Modulo.
        rewrite Z.mul_0_r.
        reflexivity.

      - (* side condition of trans_hs: g is fixed at 0 when x = 0 *)
        rewrite divstep.fixed_g by assumption.
        apply Z.divide_0_r. }

    clear H13.
    assert (HfiBound : -m < fi <= m) by apply HfBound.
    assert (HgiBound : -m < gi < m) by apply HgBound.

    (* ===== update_fg_62_var(len, &f, &g, &t), then derive the new f/g bounds ===== *)

    (* the two arithmetic obligations of the update_fg_62_var funspec: the
       62-step matrix maps (fi,gi) to 2^62*(f,g) of the state 62 steps on, and
       it is bounded by 2^62 -- both straight from the transition lemmas *)
    assert (Hfg62 : divstep_trans.Trans.ap (divstep_trans.Trans.trans_n 62 sti)
                      {| divstep_trans.Trans.x := fi; divstep_trans.Trans.y := gi |}
                    = divstep_trans.Trans.scale (2 ^ 62)
                        {| divstep_trans.Trans.x := divstep.f (fst (divstep.step_n 62 sti));
                           divstep_trans.Trans.y := divstep.g (fst (divstep.step_n 62 sti)) |})
      by exact (eq_sym (divstep_trans.Trans.trans_n_step 62 sti)).
    assert (Hbnd62 : divstep_trans.Trans.bounded (2 ^ 62) (divstep_trans.Trans.trans_n 62 sti))
      by exact (divstep_trans.Trans.bounded_trans_n 62 sti).

    (* secp256k1_modinv64_update_fg_62_var(len, &f, &g, &t) *)
    forward_call (len, fi, gi,
                  divstep.f (fst (divstep.step_n 62 sti)),
                  divstep.g (fst (divstep.step_n 62 sti)),
                  divstep_trans.Trans.trans_n 62 sti,
                  v_f, v_g, v_t, Tsh, Tsh, Tsh).
    sep_apply (data_at_data_at_ Tsh t_secp256k1_modinv64_trans2x2).

    set (fi' := divstep.f (fst (divstep.step_n 62 sti))).
    set (gi' := divstep.g (fst (divstep.step_n 62 sti))).

    assert (Hfgi'Bound :
      -2 ^ (62 * Z.of_nat len + 1) <= fi' <= 2 ^ (62 * Z.of_nat len + 1) - 1 /\
      -2 ^ (62 * Z.of_nat len + 1) <= gi' <= 2 ^ (62 * Z.of_nat len + 1) - 1).
    { unfold fi'.
      remember 62%nat as n62.
      injection (divstep_trans.Trans.trans_n_step n62 sti).
      subst n62.
      destruct (divstep_trans.Trans.bounded_trans_n 62 sti) as [[Hb1 Hb2] [Hb3 Hb4]].
      (* nia is exponential in the number of hypotheses: keep only the four
         matrix bounds and the two f/g bounds it actually multiplies *)
      clear -Hb1 Hb2 Hb3 Hb4 H7 H8.
      nia. }
    destruct Hfgi'Bound as [Hfi'Bound Hgi'Bound].
    destruct (divstep_zeta.update_de_eqm m x d e sti) as [Hxd' Hxe']; try assumption.
    fold d' in Hxd'.
    fold e' in Hxe'.

    (* one 62-block on from sti is the state at step 62*(i+1) *)
    pose (sti' := fst (divstep.step_n (62 * (i + 1)) init)).
    unfold fi', gi' in *.
    clear fi' gi'.
    replace (fst (divstep.step_n 62 sti)) with sti' in *
      by (unfold sti';
          replace (62 * (i + 1))%nat with (62 + 62 * i)%nat by lia;
          apply divstep.step_n_app_fst).
    set (fi' := divstep.f sti') in *.
    set (gi' := divstep.g sti') in *.

    (* ===== if(g[0] == 0) { for j: cond |= g[j]; if(cond == 0) break } -- detect g = 0 ===== *)

    (* _t'5 = g.v[0] *)
    forward.
    { rewrite Signed62.pad_nth by (rewrite Signed62.reprn_Zlength; lia).
      entailer!!. }
    rewrite Signed62.pad_nth by (rewrite Signed62.reprn_Zlength; lia).

    (* drop the dead divsteps temps (eta return _t'1 and the f[0]/g[0] reads
       _t'7/_t'8) so the forward_if join LOCALs are consistent *)
    drop_LOCALs [_t'1; _t'7; _t'8].

    (* if (g.v[0] == 0) *)
    forward_if (gi' <> 0).
    { (* branch: g.v[0] == 0 -- OR all the limbs of g and check for zero *)
      (* cond = 0 *)
      forward.

      (* for (j = 1; j < len; ++j) cond |= g.v[j] *)
      forward_for_simple_bound (Z.of_nat len) (EX j:Z,
        PROP ( )
        LOCAL (temp _cond (Vlong (fold_left (fun x y => Int64.or x y) (firstn (Z.to_nat j) (Signed62.reprn len gi')) Int64.zero));
          temp _t'5 (Vlong (Znth 0 (Signed62.reprn len gi')));
          temp _eta (Vlong (Int64.repr (divstep.eta sti')));
          temp _len (Vint (Int.repr (Z.of_nat len)));
          lvar _t t_secp256k1_modinv64_trans2x2 v_t;
          lvar _g t_secp256k1_modinv64_signed62 v_g;
          lvar _f t_secp256k1_modinv64_signed62 v_f;
          lvar _e t_secp256k1_modinv64_signed62 v_e;
          lvar _d t_secp256k1_modinv64_signed62 v_d;
          gvars gv; temp _x ptrx; temp _modinfo modinfo)
        SEP (data_at_ Tsh t_secp256k1_modinv64_trans2x2 v_t;
          data_at Tsh t_secp256k1_modinv64_signed62 (Signed62.pad (Signed62.reprn len fi')) v_f;
          data_at Tsh t_secp256k1_modinv64_signed62 (Signed62.pad (Signed62.reprn len gi')) v_g;
          data_at Tsh t_secp256k1_modinv64_signed62 (map Vlong (Signed62.reprn 5 d')) v_d;
          data_at Tsh t_secp256k1_modinv64_signed62 (map Vlong (Signed62.reprn 5 e')) v_e;
          data_at sh_modinfo t_secp256k1_modinv64_modinfo (make_modinfo m) modinfo;
          debruijn64_array sh_debruijn gv;
          data_at shx t_secp256k1_modinv64_signed62 (map Vlong (Signed62.reprn 5 x)) ptrx))%assert.

      - (* loop entry: cond still holds only the (zero) bottom limb *)
        entailer!!.
        rewrite <- sublist_firstn, sublist_one, H13.
        { reflexivity. }
        { lia. }
        { rewrite Signed62.reprn_Zlength.
          lia. }
        lia.

      - (* _t'6 = g.v[j] *)
        forward.
        { rewrite Signed62.pad_nth by (rewrite Signed62.reprn_Zlength; lia).
          entailer!!. }
        rewrite Signed62.pad_nth by (rewrite Signed62.reprn_Zlength; lia).

        (* cond = cond | _t'6 *)
        forward.
        entailer!!.
        rewrite <- Zfirstn_app by lia.
        rewrite <- (app_nil_r (firstn (Z.to_nat 1) _)), <- (Znth_cons Int64.zero) by (rewrite Signed62.reprn_Zlength; lia).
        rewrite fold_left_app.
        cbn.
        reflexivity.

      - (* after the loop: cond is the fold of every limb of g *)
        rewrite Nat2Z.id, firstn_all2 by (rewrite Signed62.reprn_length; lia).
        assert (Hor_assoc : forall a b c, Int64.or a (Int64.or b c) = Int64.or (Int64.or a b) c)
          by (intros; rewrite Int64.or_assoc; reflexivity).
        assert (Hor_zero : forall a, Int64.or Int64.zero a = Int64.or a Int64.zero)
          by (intros; apply Int64.or_commut).
        rewrite (fold_symmetric (fun x y => Int64.or x y) Hor_assoc Int64.zero Hor_zero).

        (* if (cond == 0) break *)
        forward_if (gi' <> 0).
        { (* branch: cond == 0 -- every limb was zero, so g = 0; break *)
          forward.
          Exists i len d' e'.
          entailer!!.
          change (gi' = 0).

          (* a zero OR-fold forces every limb to be zero *)
          assert (Hgi'0 : Forall (fun x => x = Int64.zero) (Signed62.reprn len gi')).
          { revert H14.
            clear H13.
            induction (Signed62.reprn len gi').
            { (* base case: no limbs *)
              constructor. }
            cbn.
            intros H14.

            assert (Horzero : forall a b, Int64.or a b = Int64.zero -> a = Int64.zero).
            { clear -l.
              intros a b Hab.
              destruct (Int64.bits_size_1 a).
              { (* a is already zero *)
                assumption. }
              assert (Hsize : 0 < Int64.size a).
              { destruct (Z_le_lt_dec 0 (Z.pred (Int64.size a))) as [Hle|Hlt].
                { lia. }
                assert (Hcontra := Int64.bits_below a _ Hlt).
                congruence. }

              apply (f_equal (fun x => Int64.testbit x (Z.pred (Int64.size a)))) in Hab.
              rewrite Int64.bits_zero, Int64.bits_or in Hab by (assert (Hrange := Int64.size_range a); lia).
              apply orb_false_elim in Hab.
              destruct Hab; congruence. }

            constructor.
            { eapply Horzero.
              apply H14. }
            apply IHl.
            eapply Horzero.
            rewrite Int64.or_commut.
            apply H14. }

          (* all-zero limbs reconstruct the value 0 *)
          rewrite <- (Signed62.signed_reprn gi' len).
          { clear -Hgi'0.
            induction (Signed62.reprn len gi').
            { reflexivity. }
            cbn.
            inversion_clear Hgi'0 as [|Ha Hl].
            rewrite H0, IHl.
            { reflexivity. }
            assumption. }
          { lia. }
          assumption. }
        { (* branch: cond <> 0 -- some limb was nonzero, so g <> 0 *)
          (* fall through *)
          forward.
          entailer!!.
          apply H14.
          rewrite H15.
          clear -len.
          induction len.
          { reflexivity. }
          destruct len.
          { reflexivity. }
          cbn in *.
          rewrite !Z.shiftr_0_l, !Zmod_0_l in *.
          rewrite IHlen.
          reflexivity. }
        entailer!!. }
    { (* branch: g.v[0] <> 0 -- g <> 0 holds directly *)
      (* fall through (skip the g==0 zero-check loop) *)
      forward.
      entailer!!.
      apply H13.
      rewrite H14.
      clear -len.
      destruct len as [|[|len]]; reflexivity. }

    (* ===== Length shrink: read f[len-1]/g[len-1], build cond, maybe drop a limb ===== *)

    drop_LOCALs [_t'5].

    (* fn = f.v[len-1] *)
    forward.
    { rewrite Signed62.pad_nth by (rewrite Signed62.reprn_Zlength; lia).
      entailer!!. }
    rewrite Signed62.pad_nth by (rewrite Signed62.reprn_Zlength; lia).
    replace (Z.of_nat len - 1) with (Zlength (Signed62.reprn len fi') - 1)
      by (rewrite Signed62.reprn_Zlength; reflexivity).
    rewrite Znth_last, Signed62.reprn_last by lia.

    (* gn = g.v[len-1] *)
    forward.
    { rewrite Signed62.pad_nth by (rewrite Signed62.reprn_Zlength; lia).
      entailer!!. }
    rewrite Signed62.pad_nth by (rewrite Signed62.reprn_Zlength; lia).
    replace (Z.of_nat len - 1) with (Zlength (Signed62.reprn len gi') - 1) at 1
      by (rewrite Signed62.reprn_Zlength; reflexivity).
    rewrite Znth_last, Signed62.reprn_last by lia.

    (* cond = ((int64_t)len - 2) >> 63 -- the len>1 guard term *)
    forward.
    autorewrite with int_to_z.
    change (Int.signed (Int.repr 2)) with 2.
    change (Int64.unsigned (Int64.repr (Int.unsigned (Int.repr 63)))) with 63.
    rewrite (Int.signed_repr (Z.of_nat len)) by rep_lia.
    rewrite Int64.signed_repr by rep_lia.

    (* the guard term is 0 exactly when len >= 2, and -1 otherwise *)
    assert (Hlenshift : Z.shiftr (Z.of_nat len - 2) 63 = if 2 <=? Z.of_nat len then 0 else -1).
    { rewrite Z.shiftr_div_pow2 by lia.
      elim Z.leb_spec.
      - (* branch: len >= 2 -- the quotient is 0 *)
        intros Hlen.

        cut (0 <= (Z.of_nat len - 2) / 2 ^ 63 < 1).
        { lia. }
        apply div_bounds; lia.

      - (* branch: len < 2 -- the quotient is -1 *)
        intros Hlen.

        cut (-1 <= (Z.of_nat len - 2) / 2 ^ 63 < 0).
        { lia. }
        apply div_bounds; lia. }

    rewrite Hlenshift.
    clear Hlenshift.

    (* cond = cond | (fn ^ (fn >> 63)) *)
    forward.

    (* cond = cond | (gn ^ (gn >> 63)) *)
    forward.

    (* if (cond == 0) shrink len: fold the top limb of f and g back into limb len-2 *)
    forward_if (EX len:nat,
      PROP (
        (1 <= len <= 5)%nat
      ; -2^(62 * Z.of_nat len + 1) <= divstep.f (fst (divstep.step_n (62 * (i + 1)) init)) <= 2^(62 * Z.of_nat len + 1) - 1
      ; -2^(62 * Z.of_nat len + 1) <= divstep.g (fst (divstep.step_n (62 * (i + 1)) init)) <= 2^(62 * Z.of_nat len + 1) - 1
      )
      LOCAL (
        temp _eta (Vlong (Int64.repr (divstep.eta sti')));
        temp _len (Vint (Int.repr (Z.of_nat len)));
        lvar _t t_secp256k1_modinv64_trans2x2 v_t;
        lvar _g t_secp256k1_modinv64_signed62 v_g;
        lvar _f t_secp256k1_modinv64_signed62 v_f;
        lvar _e t_secp256k1_modinv64_signed62 v_e;
        lvar _d t_secp256k1_modinv64_signed62 v_d;
        gvars gv; temp _x ptrx; temp _modinfo modinfo)
      SEP (data_at_ Tsh t_secp256k1_modinv64_trans2x2 v_t;
        data_at Tsh t_secp256k1_modinv64_signed62 (Signed62.pad (Signed62.reprn len fi')) v_f;
        data_at Tsh t_secp256k1_modinv64_signed62 (Signed62.pad (Signed62.reprn len gi')) v_g;
        data_at Tsh t_secp256k1_modinv64_signed62 (map Vlong (Signed62.reprn 5 d')) v_d;
        data_at Tsh t_secp256k1_modinv64_signed62 (map Vlong (Signed62.reprn 5 e')) v_e;
        data_at sh_modinfo t_secp256k1_modinv64_modinfo (make_modinfo m) modinfo;
        debruijn64_array sh_debruijn gv;
        data_at shx t_secp256k1_modinv64_signed62 (map Vlong (Signed62.reprn 5 x)) ptrx))%assert.

    { (* branch: cond == 0 -- len > 1 and both top limbs are pure sign *)
      (* a zero OR forces its left argument to be zero; peel the three terms *)
      assert (Hor0_l : forall x y, Int64.or x y = Int64.zero -> x = Int64.zero).
      { clear.
        intros x y Hxy.
        apply Int64.same_bits_eq.
        intros i Hi.
        apply (f_equal (fun x => Int64.testbit x i)) in Hxy.
        rewrite Int64.bits_or, Int64.bits_zero, orb_false_iff in Hxy by assumption.
        rewrite Int64.bits_zero.
        tauto. }

      assert (H14ab := Hor0_l _ _ H14).
      rewrite Int64.or_commut in H14.
      generalize (Hor0_l _ _ H14).
      clear H14.
      assert (H14a := Hor0_l _ _ H14ab).
      rewrite Int64.or_commut in H14ab.
      generalize (Hor0_l _ _ H14ab).
      clear H14ab.
      autorewrite with int_to_z.
      change (Int64.unsigned (Int64.repr (Int.unsigned (Int.repr 63)))) with 63.

      (* x ^ (x >> 63) = 0 pins x to the two sign values -1 and 0 *)
      assert (Hxor : forall x, -2^63 <= x < 2^63 -> Int64.repr (Z.lxor x (Z.shiftr (Int64.signed (Int64.repr x)) 63)) = Int64.zero -> -1 <= x <= 0).
      { clear.
        intros x Hx Hlxor.

        assert (Hxrange : Int64.min_signed <= x <= Int64.max_signed).
        { change Int64.min_signed with (-2^63).
          change Int64.max_signed with (2^63 - 1).
          lia. }

        assert (Hshrange : -1 <= Z.shiftr x 63 < 1).
        { apply shiftr_bounds.
          lia. }

        rewrite <- xor64_repr in Hlxor.
        apply Int64.xor_zero_equal in Hlxor.
        rewrite Int64.signed_repr in Hlxor by rep_lia.

        assert (Heq : x = Z.shiftr x 63).
        { rewrite <- (Int64.signed_repr (Z.shiftr x 63)) by rep_lia.
          rewrite <- (Int64.signed_repr x) at 1 by rep_lia.
          congruence. }

        rewrite Heq.
        lia. }

      intros Hfi'last Hgi'last.

      (* both top limbs fit in an int64 (they are the top window of a 62*len-bit value) *)
      assert (Hfn_range : -2^63 <= Z.shiftr fi' (62 * (Z.of_nat len - 1)) < 2^63).
      { rewrite Z.mul_sub_distr_l, Z.shiftr_div_pow2 by lia.
        apply div_bounds.
        { lia. }
        clear -Hfi'Bound H5 H6.
        rewrite Z.mul_opp_r, <- Z.pow_add_r by lia.
        replace (62 * Z.of_nat len - 62 * 1 + 63) with (62 * Z.of_nat len + 1) by ring.
        lia. }

      assert (Hgn_range : -2^63 <= Z.shiftr gi' (62 * (Z.of_nat len - 1)) < 2^63).
      { rewrite Z.mul_sub_distr_l, Z.shiftr_div_pow2 by lia.
        apply div_bounds.
        { lia. }
        clear -Hgi'Bound H5 H6.
        rewrite Z.mul_opp_r, <- Z.pow_add_r by lia.
        replace (62 * Z.of_nat len - 62 * 1 + 63) with (62 * Z.of_nat len + 1) by ring.
        lia. }

      apply (Hxor _ Hfn_range) in Hfi'last.
      apply (Hxor _ Hgn_range) in Hgi'last.

      (* the guard term being zero is exactly len >= 2 *)
      assert (Hlen2 : 2 <= Z.of_nat len).
      { revert H14a.
        elim Z.leb_spec.
        - (* branch: len >= 2 -- the guard term is 0 *)
          intros Hlen2 _.
          exact Hlen2.

        - (* branch: len < 2 -- the guard term is -1, contradicting cond = 0 *)
          discriminate. }

      clear H14a.
      set (fisign := Z.shiftr fi' (62 * (Z.of_nat len - 1))) in *.
      set (gisign := Z.shiftr gi' (62 * (Z.of_nat len - 1))) in *.

      (* _t'4 = f.v[len-2] *)
      forward.
      { rewrite Signed62.pad_nth by (rewrite Signed62.reprn_Zlength; lia).
        entailer!!. }
      rewrite Signed62.pad_nth by (rewrite Signed62.reprn_Zlength; lia).

      (* f.v[len-2] = _t'4 | ((uint64_t)fn << 62) *)
      forward.

      (* _t'3 = g.v[len-2] *)
      forward.
      { rewrite Signed62.pad_nth by (rewrite Signed62.reprn_Zlength; lia).
        entailer!!. }
      rewrite Signed62.pad_nth by (rewrite Signed62.reprn_Zlength; lia).

      (* g.v[len-2] = _t'3 | ((uint64_t)gn << 62) *)
      forward.

      (* [Int64.shl _ 62] as a plain [Z.shiftl] on the stored limb value *)
      rewrite !Int64.shl_mul_two_p.
      change (Int64.unsigned (Int64.repr (Int.unsigned (Int.repr 62)))) with 62.
      rewrite !two_p_equiv.
      rewrite !mul64_repr.
      rewrite <- !Z.shiftl_mul_pow2 by lia.
      rewrite !Signed62.pad_upd_Znth by (rewrite Signed62.reprn_Zlength; lia).

      (* --len *)
      forward.
      rewrite sub_repr.
      Exists (len - 1)%nat.
      rewrite Nat2Z.inj_sub by lia.
      change (Z.of_nat 1) with 1.

      (* dropping a pure-sign top limb keeps f and g inside 62*(len-1) bits *)
      assert (Hfi'Bound' : -2 ^ (Z.of_nat (len - 1) * 62) <= fi' <
              2 ^ (Z.of_nat (len - 1) * 62)).
      { replace (Z.of_nat (len - 1) * 62) with (62 * (Z.of_nat len - 1)) by lia.
        destruct (Z.eq_dec fisign 0) as [Hfisign0|Hfisign0].
        { apply shiftr_small_iff in Hfisign0; lia. }
        destruct (Z.eq_dec fisign (-1)) as [Hfisign1|Hfisign1].
        { apply shiftr_small_neg_iff in Hfisign1; lia. }
        lia. }

      assert (Hgi'Bound' : -2 ^ (Z.of_nat (len - 1) * 62) <= gi' <
              2 ^ (Z.of_nat (len - 1) * 62)).
      { replace (Z.of_nat (len - 1) * 62) with (62 * (Z.of_nat len - 1)) by lia.
        destruct (Z.eq_dec gisign 0) as [Hgisign0|Hgisign0].
        { apply shiftr_small_iff in Hgisign0; lia. }
        destruct (Z.eq_dec gisign (-1)) as [Hgisign1|Hgisign1].
        { apply shiftr_small_neg_iff in Hgisign1; lia. }
        lia. }

      entailer!!.
      { (* PROP: the shrunk-length f/g interval *)
        replace (62 * (Z.of_nat len - 1) + 1) with (Z.of_nat (len - 1) * 62 + 1) by lia.
        rewrite Z.pow_add_r by lia.
        fold sti' fi' gi'.
        lia. }

      (* a top limb confined to {-1, 0} is exactly the sign of the value *)
      assert (Hsign : forall x n, -1 <= Z.shiftr x n <= 0 -> Z.shiftr x n = if 0 <=? x then 0 else -1).
      { clear.
        intros x n Hx.
        elim Z.leb_spec.
        - (* branch: 0 <= x -- the shifted value is nonnegative, hence 0 *)
          intros Hx0.
          apply (Z.shiftr_nonneg _ n) in Hx0; lia.

        - (* branch: x < 0 -- the shifted value is negative, hence -1 *)
          intros Hx0.
          apply (Z.shiftr_neg _ n) in Hx0; lia. }

      unfold fisign, gisign.
      rewrite !Hsign by assumption.

      (* SEP: one generic limb-fold entailment, used for both f and g *)
      cut (forall v x, -2 ^ (Z.of_nat (len - 1) * 62) <= x <= 2 ^ (Z.of_nat (len - 1) * 62) - 1 -> data_at Tsh t_secp256k1_modinv64_signed62
        (Signed62.pad
           (upd_Znth (Z.of_nat len - 2) (Signed62.reprn len x)
              (Int64.or (Znth (Z.of_nat len - 2) (Signed62.reprn len x))
                 (Int64.repr (Z.shiftl (if 0 <=? x then 0 else -1) 62))))) v
      |-- data_at Tsh t_secp256k1_modinv64_signed62
            (Signed62.pad (Signed62.reprn (len - 1) x)) v).
      { intro K.
        apply sepcon_derives.
        - (* the f resource *)
          apply K; lia.

        - (* the g resource *)
          apply K; lia. }

      intros v h Hh.

      (* split the 5-limb array into the [len-1] live limbs and the padding *)
      unfold Signed62.pad at 2.
      do 2 unfold_data_at (data_at _ _ _ v).
      rewrite !field_at_data_at.
      simpl (nested_field_type t_secp256k1_modinv64_signed62 (DOT _v)).
      assert (Hzl_v : Zlength (map Vlong (Signed62.reprn (len - 1) h)) = Z.of_nat len - 1)
        by (rewrite Zlength_map, Signed62.reprn_Zlength; lia).
      assert (Hzl_pad : Zlength (repeat Vundef (5 - Datatypes.length (Signed62.reprn (len - 1) h))) =
                        5 - (Z.of_nat len - 1))
        by (rewrite Signed62.reprn_length, Zlength_repeat'; lia).
      rewrite (split2_data_at_Tarray_app (Z.of_nat len - 1)) by assumption.
      rewrite ?Signed62.reprn_length.
      rewrite <-(data_at__tarray' _ tlong _ (repeat Vundef (5 - (len - 1)))) by
        (replace (5 - (len - 1))%nat with (Z.to_nat (5 - (Z.of_nat len - 1))) by lia; apply repeat_Zrepeat).
      sep_apply (split2_data_at_Tarray_unfold Tsh tlong 5 (Z.of_nat len - 1)).
      { lia. }
      entailer!!.

      (* the live prefix: the top limb of [reprn len h] folds into limb len-2 *)
      unfold Signed62.pad.
      rewrite sublist0_app1, sublist_map, sublist_firstn by (rewrite Zlength_map, Zlength_upd_Znth, Signed62.reprn_Zlength; lia).
      replace (Z.to_nat (Z.of_nat len - 1)) with (len - 1)%nat by lia.
      replace (Z.of_nat len - 2) with ((Z.of_nat (len - 1)) - 1) by lia.
      rewrite Signed62.reprn_shrink.
      { entailer!!. }
      { (* the folded limb stays inside the signed 62-bit window *)
        unfold Signed62.min_signed, Signed62.max_signed.
        lia. }
      lia. }

    { (* branch: cond <> 0 -- len is unchanged *)
      (* fall through *)
      forward.
      Exists len.
      entailer!!. }

    Intros len0.
    clear Hgi'Bound Hfi'Bound Hfi0Odd gi0 fi0 Hi0 H8 H7 H6 H5 len.
    rename len0 into len.

    (* ===== Next iteration: bound i < 11 via the 724-divstep convergence certificate ===== *)

    (* the loop cannot reach iteration 11 without g already being 0 (the 724-divstep
       correctness certificate from divsteps724); needed so the re-established
       invariant's [Z.of_nat (i+1) < 12] holds *)
    assert(Hi0 : (i <> 11)%nat).
    { intros ->.
      apply H13.
      unfold gi', sti', init.
      rewrite (divstep.step_n_app_fst 20 724).
      apply divstep.fixed_g.
      rewrite divstep.Translate_divsteps_g.
      apply (process_divstep_correct _ 0x1030596cf6d817d1357f908ef70cdb00b38d047fbba852139babb6c8646fb15b2); try lia.
      { assumption. }
      apply example724. }

    assert (Hi12 : (i + 1 < 12)%nat) by lia.

    (* re-establish the loop invariant for the next iteration: i+1, len, d', e' *)
    Exists (i + 1)%nat len d' e'.
    entailer!!.

  - (* ===== After break (g = 0): |f| is the gcd, then normalize d into the result ===== *)

    unfold invariant in *.
    clear invariant.
    Intros i len d e.
    rename H13 into Hx0d0.
    rename H14 into H13.
    set (sti := (fst (divstep.step_n (62 * (i + 1)) init))) in *.
    set (fi := divstep.f sti) in *.
    set (gi := divstep.g sti) in *.

    (* |f| == 1, or (x == 0 and f == modulus): f is +/- gcd(x, m) = +/- 1 (or m when x=0) *)
    assert (Hverify : (Z.abs fi = 1) \/ (x = 0 /\ fi = m)).
    { destruct (Z.eq_dec x 0) as [Hx0|Hx0].
      - (* branch: x = 0 -- g stays 0, so |f| is the preserved modulus *)
        right.
        split.
        { assumption. }
        specialize (HfBound (62 * (i + 1))%nat).
        fold sti fi in HfBound.

        cut (m = Z.abs fi).
        { lia. }
        transitivity (Z.gcd fi 0).
        { symmetry.
          apply Zis_gcd_gcd.
          { lia. }
          rewrite <- H13.
          apply divstep.gcd.
          subst x.
          apply Zis_gcd_0. }
        apply Z.gcd_0_r.

      - (* branch: x <> 0 -- |f| = gcd(x, m) = 1 by the coprimality hypothesis *)
        left.
        rewrite <- Z.gcd_0_r.
        apply Zis_gcd_gcd.
        { lia. }
        rewrite <- H13.
        apply divstep.gcd.
        apply Zis_gcd_sym.
        destruct H2 as [H2|H2].
        { lia. }
        apply H2. }

    (* ===== normalize_62(&d, f[len-1], modinfo), then assign d into x ===== *)

    (* _t'2 = f.v[len-1] -- the sign argument *)
    forward.
    { rewrite Signed62.pad_nth by (rewrite Signed62.reprn_Zlength; lia).
      entailer!!. }
    rewrite Signed62.pad_nth by (rewrite Signed62.reprn_Zlength; lia).
    rewrite <- (Signed62.reprn_Zlength len fi), Znth_last, Signed62.reprn_last at 1 by lia.

    (* the sign limb fits an int64: fi is a 62*len-bit value *)
    assert (Hfibound : 2 ^ (62 * (Z.of_nat len - 1)) * -2 ^ 63 <= fi <=
      2 ^ (62 * (Z.of_nat len - 1)) * (2 ^ 63 - 1 + 1) - 1).
    { rewrite Z.sub_add, Z.mul_opp_r, <-Z.pow_add_r, Z.mul_sub_distr_l by lia.
      replace (62 * Z.of_nat len - 62 * 1 + 63) with (62 * Z.of_nat len + 1); lia. }

    assert (Hfn_range : Int64.min_signed <= Z.shiftr fi (62 * (Z.of_nat len - 1)) <= Int64.max_signed).
    { assert (Hsh : -2 ^ 63 <= Z.shiftr fi (62 * (Z.of_nat len - 1)) < 2 ^ 63).
      { apply shiftr_bounds.
        lia. }
      change Int64.min_signed with (-2^63).
      change Int64.max_signed with (2^63 - 1).
      lia. }

    (* secp256k1_modinv64_normalize_62(&d, _t'2, modinfo) -- the PRE sign range
       is Hfn_range *)
    forward_call.

    (* the top limb is negative exactly when fi is *)
    assert (Hsgn : (Z.shiftr fi (62 * (Z.of_nat len - 1)) <? 0) = (fi <? 0)).
    { apply Bool.eq_true_iff_eq.
      rewrite !Z.ltb_lt.
      rewrite Z.shiftr_neg.
      reflexivity. }

    rewrite Hsgn.

    (* the normalized result (if fi<0 then -d else d) mod m equals mod_inv x m *)
    assert (Hnorm : (if fi <? 0 then - d else d) mod m = mod_inv x m).
    { destruct Hverify as [Habsfi|[Hx0 _]].
      - (* branch: |f| = 1 -- d * sgn f is the inverse of x *)
        apply mod_inv_mul_unique_r.
        replace ((if fi <? 0 then -d else d)) with (d * Z.sgn fi) by (elim (Z.ltb_spec); lia).
        rewrite Z.mul_assoc, <-Zmult_mod_idemp_l, H11, Zmult_mod_idemp_l, Z.sgn_abs, Habsfi, Z.mod_1_l; lia.

      - (* branch: x = 0 -- d = 0 and mod_inv 0 m = 0 *)
        rewrite Hx0d0, Hx0, mod_inv_zero by assumption.
        destruct (fi <? 0); reflexivity. }

    rewrite Hnorm.

    (* release the old x limbs so the in-place write has an uninitialised target *)
    sep_apply (data_at_data_at_ shx t_secp256k1_modinv64_signed62 (map Vlong (Signed62.reprn 5 x)) ptrx).
    (* secp256k1_modinv64_signed62_assign(x, &d) -- write the result back into x *)
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
      rewrite mod_inv_mul_r, (proj2 (Zgcd_1_rel_prime x m) Hr).
      apply Z.mod_1_l.
      lia.
Qed.
