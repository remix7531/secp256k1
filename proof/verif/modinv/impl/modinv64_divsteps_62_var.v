(** * verif.modinv.impl.modinv64_divsteps_62_var: body proof for secp256k1_modinv64_divsteps_62_var. *)
(** Copyright (C) 2026 remix7531
    Ported from BlockstreamResearch/simplicity Coq/C/secp256k1/verif_modinv64_impl.v
    (commit c1dddedd), Copyright (c) 2018 Blockstream, originally MIT.
    Upstream notice reproduced in proof/README.md.
    SPDX-License-Identifier: MIT *)

(** Split out from the upstream-ported verif_modinv64_impl.v (one semax_body
    per file, per the project convention). *)

Require Import secp256k1.vst.base.
Require Import secp256k1.contract.helper.structs_modinv.
Require Import secp256k1.contract.impl.modinv.
Require Import secp256k1.contract.gprog.modinv.
Require Import secp256k1.theory.extra_math.
Require Import secp256k1.theory.modinv.divsteps.theory.
Require Import secp256k1.theory.modinv.divsteps.bound724.
Require Import secp256k1.theory.modinv.construction.inverse.
Require secp256k1.theory.modinv.construction.divstep.
Require secp256k1.theory.modinv.construction.divstep_trans.
Require Import secp256k1.tactics.core.
Require Import secp256k1.tactics.hygiene.

(* ================================================================= *)
(** ** secp256k1_modinv64_divsteps_62_var -- 62 variable-time divsteps. *)

(** [secp256k1_modinv64_divsteps_62_var(eta, f0, g0, t)] runs 62 variable-time
    divsteps on [(f, g)] starting from [eta].  It returns the final eta and fills
    [t] with the aggregate transition matrix, i.e. [Trans.trans_n 62 st] with eta
    advanced to [divstep.eta (fst (divstep.step_n 62 st))].

    Proof shape: one [forward_loop] whose invariant carries a step count [i] and
    a "pending" count [j] of trailing zero divsteps already folded into [u]/[v]
    but not yet into the loop counter.  Each round (a) calls [ctz64_var] on
    [g | (UINT64_MAX << i)] and cancels the [k] trailing zeros, advancing the
    model index from [n] to [n1 = k + n]; (b) breaks when [i] hits 0; (c) branches
    on the sign of eta, computing a mask [m] of [min(limit, 6)] resp.
    [min(limit, 4)] bits and the multiplier [w] that clears exactly those bits of
    [g]; (d) applies [g += f*w], [q += u*w], [r += v*w] and re-establishes the
    invariant with [n2] more divsteps done. *)
Lemma body_secp256k1_modinv64_divsteps_62_var: semax_body Vprog Gprog f_secp256k1_modinv64_divsteps_62_var spec_secp256k1_modinv64_divsteps_62_var.
Proof.
  start_function.

  (* ===== Init: u=1, v=0, q=0, r=1, f=f0, g=g0, i=62 ===== *)

  (* uint64_t u = 1 *)
  forward.

  (* uint64_t v = 0 *)
  forward.

  (* uint64_t q = 0 *)
  forward.

  (* uint64_t r = 1 *)
  forward.

  (* uint64_t f = f0 *)
  forward.

  (* uint64_t g = g0 *)
  forward.

  (* int i = 62 *)
  forward.

  (* for (;;) -- [i] counts the completed divsteps, [j] the trailing zero
     divsteps already folded into u/v but not yet into the loop counter *)
  forward_loop (EX i : nat, EX j : nat, EX u : Z, EX v : Z, EX f : Z, EX g : Z,
    PROP (Z.of_nat j <= Z.of_nat i <= 62;
          divstep_trans.Trans.u (divstep_trans.Trans.trans_n i st) = (u * 2 ^ (Z.of_nat j))%Z;
          divstep_trans.Trans.v (divstep_trans.Trans.trans_n i st) = (v * 2 ^ (Z.of_nat j))%Z;
          eqm (2 ^ (64 - Z.of_nat i)) f (divstep.f (fst (divstep.step_n i st)));
          eqm (2 ^ (64 - Z.of_nat i)) g (divstep.g (fst (divstep.step_n i st))))
    LOCAL (temp _i (Vint (Int.repr (62 - Z.of_nat i + Z.of_nat j)));
      temp _g (Vlong (Int64.repr (g * 2 ^ (Z.of_nat j))));
      temp _f (Vlong (Int64.repr f));
      temp _r (Vlong (Int64.repr (divstep_trans.Trans.r (divstep_trans.Trans.trans_n i st))));
      temp _q (Vlong (Int64.repr (divstep_trans.Trans.q (divstep_trans.Trans.trans_n i st))));
      temp _v (Vlong (Int64.repr v));
      temp _u (Vlong (Int64.repr u));
      gvars gv;
      temp _eta (Vlong (Int64.repr (divstep.eta (fst (divstep.step_n i st)) + Z.of_nat j)));
      temp _f0 (Vlong (Int64.repr (divstep.f st)));
      temp _g0 (Vlong (Int64.repr (divstep.g st)));
      temp _t t)
    SEP (data_at_ sh t_secp256k1_modinv64_trans2x2 t;
      debruijn64_array sh_debruijn gv))%assert
  break:(
    PROP ( )
    LOCAL (temp _r (Vlong (Int64.repr (divstep_trans.Trans.r (divstep_trans.Trans.trans_n 62 st))));
      temp _q (Vlong (Int64.repr (divstep_trans.Trans.q (divstep_trans.Trans.trans_n 62 st))));
      temp _v (Vlong (Int64.repr (divstep_trans.Trans.v (divstep_trans.Trans.trans_n 62 st))));
      temp _u (Vlong (Int64.repr (divstep_trans.Trans.u (divstep_trans.Trans.trans_n 62 st))));
      gvars gv;
      temp _eta (Vlong (Int64.repr (divstep.eta (fst (divstep.step_n 62 st)))));
      temp _t t)
    SEP (data_at_ sh t_secp256k1_modinv64_trans2x2 t;
      debruijn64_array sh_debruijn gv))%assert.

  - (* ===== Loop entry: the i = 0, j = 0 instance of the invariant ===== *)
    Exists 0%nat.
    Exists 0%nat.
    Exists (divstep_trans.Trans.u (divstep_trans.Trans.trans_n 0 st)).
    Exists (divstep_trans.Trans.v (divstep_trans.Trans.trans_n 0 st)).
    Exists (divstep.f (fst (divstep.step_n 0 st))).
    Exists (divstep.g (fst (divstep.step_n 0 st))).
    entailer!!.

  - (* ===== Loop body: cancel the trailing zeros of g, then one divstep round ===== *)
    Intros n j u v f g.
    rename H0 into Hn.
    rename H1 into Hu.
    rename H2 into Hv.
    rename H3 into Hf.
    rename H4 into Hg.

    (* ===== Setup: parity / gcd / eta facts feeding the rest of the round ===== *)

    (* Hmask: the sentinel bit -1 << i is still set, so the ctz64 argument is nonzero *)
    assert (Hmask : 0 <> (-1 * 2 ^ (62 - Z.of_nat n + Z.of_nat j)) mod (2 ^ 64)).
    { intros Hzero.
      symmetry in Hzero.
      apply (Zmod_divide _ (2 ^ 64) ltac:(lia)) in Hzero.
      replace 64 with ((2 + Z.of_nat n - Z.of_nat j) + (62 - Z.of_nat n + Z.of_nat j)) in Hzero by ring.
      rewrite !Z.pow_add_r, Z.mul_divide_cancel_r, (Z.divide_opp_r _ 1) in Hzero by lia.

      assert (Hpow_pos : 0 <= 2 ^ (2 + Z.of_nat n - Z.of_nat j)) by lia.
      apply (Z.divide_1_r_nonneg _ Hpow_pos) in Hzero.
      replace (2 + Z.of_nat n - Z.of_nat j) with (2 + (Z.of_nat n - Z.of_nat j)) in Hzero by ring.
      rewrite Z.pow_add_r in Hzero by lia.
      lia. }
    assert (Hbound := Z.mod_pos_bound (-1 * 2 ^ (62 - Z.of_nat n + Z.of_nat j)) (2 ^ 64)).
    assert (Heta := divstep.eta_bounds 683 n st H).

    (* Hfodd: f is odd, because it agrees with the model f mod 2^(64-n) *)
    assert (Hfodd : Zodd f).
    { apply Zodd_bool_iff.

      assert (Hf0 := Zmod_odd f).
      revert Hf0.
      destruct (Z.odd f).

      - (* branch: f odd -- nothing left to prove *)
        reflexivity.

      - (* branch: f even -- contradicts oddness of the model f *)
        assert (H2 : (2 | 2 ^ (64 - Z.of_nat n))) by (apply Zpow_facts.Zpower_divide; lia).
        rewrite (Zmod_div_mod 2 (2 ^ (64 - Z.of_nat n))), Hf, <- (Zmod_div_mod 2 (2 ^ (64 - Z.of_nat n)))
          by (try lia; assumption).
        assert (Hfodd := divstep.odd_f (fst (divstep.step_n n st))).
        apply Zodd_bool_iff in Hfodd.

        assert (Hmod := Zmod_odd (divstep.f (fst (divstep.step_n n st)))).
        rewrite Hfodd in Hmod.
        rewrite Hmod.
        discriminate. }

    (* Hgcd: an odd number is coprime to every power of two ([theory/bits.v]) *)
    pose proof gcd_odd_pow2_1 as Hgcd.

    (* zeros = secp256k1_ctz64_var(g | (UINT64_MAX << i)) *)
    forward_call.
    { (* tc: the shift count i stays below the word size *)
      change (Int.unsigned Int64.iwordsize') with 64.
      lia. }

    { split.

      - (* lower: the sentinel bit -1 << i keeps the argument nonzero *)
        apply Z_lor_pos.
        + rep_lia.
        + rewrite Int64.shl_mul_two_p.
          rewrite two_p_equiv.
          rewrite Int64.unsigned_repr by rep_lia.
          rewrite mul64_repr.
          rewrite Int64.unsigned_repr_eq.
          change Int64.modulus with (2 ^ 64).
          lia.

      - (* upper: the OR of two 64-bit words is below 2^64 *)
        change Int64.modulus with (2 ^ 64).
        rewrite Z_log2_lt_pow2, Z.log2_lor, Z.max_lub_lt_iff, <- !Z_log2_lt_pow2; rep_lia. }

    rewrite (Int.unsigned_repr (62 - Z.of_nat n + Z.of_nat j)) by rep_lia.
    rewrite Int64.shl_mul_two_p.
    rewrite two_p_equiv.
    rewrite (Int64.unsigned_repr (62 - Z.of_nat n + Z.of_nat j)) by rep_lia.
    rewrite mul64_repr.
    rewrite !Int64.unsigned_repr_eq.
    change Int64.modulus with (2 ^ 64).

    set (g' := g * 2 ^ Z.of_nat j).
    assert (Hgbound := Z.mod_pos_bound g' (2 ^ 64)).
    set (zeros := Z_ctz (Z.lor (g' mod 2 ^ 64) ((-1 * 2 ^ (62 - Z.of_nat n + Z.of_nat j)) mod 2 ^ 64))).
    assert (Hzeros_pos : 0 <= zeros) by apply Z_ctz_non_neg.

    assert (Hzeros62 : zeros <= 62 - Z.of_nat n + Z.of_nat j).
    { unfold zeros.
      rewrite Z.lor_comm.
      etransitivity.
      - apply Z_ctz_lor_l.
        lia.
      - apply Z.nlt_ge.
        intros Hctz.
        apply Z_ctz_testbit_false in Hctz.
        rewrite Z.mod_pow2_bits_low, <- two_p_equiv, Z.mul_comm, <- Z.opp_eq_mul_m1,
                Zbits.Ztestbit_neg_two_p in Hctz by lia.
        destruct zlt in Hctz; lia. }

    (* Hg'zeros: every bit of g' below [zeros] is clear, i.e. 2^zeros divides g' *)
    assert (Hg'zeros : (2 ^ zeros | g')).
    { apply Zmod_divide.

      - (* side: the divisor 2 ^ zeros is nonzero *)
        apply Z.pow_nonzero; lia.
      - apply Z.bits_inj_0.
        intros k.
        destruct (Z_le_lt_dec 0 k) as [Hk0|Hk0].
        + rewrite <- two_p_equiv, Zbits.Ztestbit_mod_two_p by lia.
          destruct zlt as [Hk|Hk].
          * rewrite <- (Z.mod_pow2_bits_low _ 64) by lia.
            destruct (Z.eq_dec (g' mod 2 ^ 64) 0) as [Hz|Hne].
            { (* branch: the low word is zero -- every bit is clear *)
              rewrite Hz.
              apply Z.bits_0. }

            apply Z_ctz_testbit_false.
            eapply Z.lt_le_trans.
            { apply Hk. }
            apply Z_ctz_lor_l; assumption.

          * (* branch: zeros <= k -- above the truncation window *)
            reflexivity.

        + (* branch: k < 0 -- a negative bit index *)
          apply Z.testbit_neg_r.
          assumption. }

    (* Hzeros_opt: [zeros] is maximal -- no larger power of two below the
       sentinel divides g' *)
    assert (Hzeros_opt : forall i, (2 ^ i | g') -> i <= 62 - Z.of_nat n + Z.of_nat j -> i <= zeros).
    { intros i Hig Hi62.
      apply Z.lt_pred_le.
      apply Z_testbit_false_ctz.

      - (* side: the ctz argument is nonzero *)
        apply Z_lt_neq.
        apply Z_lor_pos; lia.
      - intros k Hk.
        destruct Hig as [m ->].
        rewrite Z.lor_spec, orb_false_iff, !Z.mod_pow2_bits_low, Z.mul_pow2_bits_low by lia.
        rewrite <- two_p_equiv, Z.mul_comm, <- Z.opp_eq_mul_m1, Zbits.Ztestbit_neg_two_p by lia.
        elim zlt; lia. }

    (* Posed in the exact shape [forward]'s shift-count obligation takes, so the
       three shift statements below need no explicit side-goal block. *)
    assert (Htc_shift : zeros < Int.unsigned Int64.iwordsize')
      by (change (Int.unsigned Int64.iwordsize') with 64; lia).

    (* g >>= zeros *)
    forward.

    (* u <<= zeros *)
    forward.

    (* v <<= zeros *)
    forward.

    (* eta -= zeros *)
    forward.

    (* i -= zeros *)
    forward.

    rewrite (Int.unsigned_repr zeros) by rep_lia.
    rewrite (Int.signed_repr zeros) by rep_lia.
    rewrite sub_repr.
    rewrite sub64_repr.
    rewrite Int64_shru_shiftr.
    rewrite !Int64.shl_mul_two_p.
    rewrite !two_p_equiv.
    rewrite !(Int64.unsigned_repr zeros) by rep_lia.
    rewrite !mul64_repr.
    rewrite Int64.unsigned_repr_eq.
    change Int64.modulus with (2 ^ 64).

    (* ===== Fold the cancelled zeros into the model: g/2^zeros, u and v scaled ===== *)

    unfold g'.
    replace 64 with (zeros + (64 - zeros)) by ring.
    rewrite Z.pow_add_r by lia.
    rewrite (Z.shiftr_div_pow2 _ zeros) by lia.
    rewrite Zaux.Zdiv_mod_mult by lia.
    replace zeros with (Z.of_nat j + (zeros - Z.of_nat j)) by ring.

    set (k := zeros - Z.of_nat j).

    assert (Hk : 0 <= k).
    { apply Z.nlt_ge.
      intros Hkneg.
      enough (Hcontra : zeros + 1 <= zeros) by lia.
      apply Hzeros_opt.

      - (* 2^(zeros+1) divides g' = g * 2^j, via 2^j *)
        apply (Z.divide_trans _ (2 ^ Z.of_nat j)).
        + apply Zmod_divide.

          * (* side: 2 ^ (zeros + 1) is nonzero *)
            apply Z.pow_nonzero; lia.
          * replace (Z.of_nat j) with ((-1 - k) + (zeros + 1)) by (unfold k; ring).
            rewrite Z.pow_add_r by lia.
            apply Z_mod_mult.
        + apply Z.divide_factor_r.

      - (* side: zeros + 1 is still inside the sentinel window *)
        lia. }

    rewrite !Z.pow_add_r by lia.
    rewrite !Z.mul_assoc.
    rewrite <- Hu.
    rewrite <- Hv.
    clear u v Hu Hv.
    replace (62 - Z.of_nat n + Z.of_nat j - (Z.of_nat j + k))
      with (62 - Z.of_nat n - k) by ring.
    replace (divstep.eta (fst (divstep.step_n n st)) + Z.of_nat j - (Z.of_nat j + k))
      with (divstep.eta (fst (divstep.step_n n st)) - k) by ring.
    rewrite (Z.mul_comm g).
    rewrite Zdiv_mult_cancel_l by lia.

    assert (Hkn : (2 ^ k | 2 ^ (64 - Z.of_nat n))).
    { replace (64 - Z.of_nat n) with (k + (64 - Z.of_nat n - k)) by ring.
      rewrite Z.pow_add_r by lia.
      apply Z.divide_factor_l. }
    assert (Hgzeros : (2 ^ k | divstep.g (fst (divstep.step_n n st)))).
    { apply Zmod_divide.
      { (* side: 2 ^ k is nonzero *)
        apply Z.pow_nonzero; lia. }

      rewrite (Zmod_div_mod _ (2 ^ (64 - Z.of_nat n))), <- Hg, <- Zmod_div_mod by (try lia; assumption).
      apply Zdivide_mod.
      apply (Z.mul_divide_cancel_r (2 ^ k) g (2 ^ Z.of_nat j)).

      - (* side: 2 ^ j is nonzero *)
        apply Z.pow_nonzero; lia.
      - rewrite <- Z.pow_add_r by lia.
        replace (k + Z.of_nat j) with zeros by (unfold k; ring).
        exact Hg'zeros. }

    rewrite <- (Z2Nat.id _ Hk) in Hgzeros |- *.
    rewrite <- divstep.eta_hs by assumption.

    set (g1 := (g / 2 ^ Z.of_nat (Z.to_nat k)) mod 2 ^ (64 - (Z.of_nat j + Z.of_nat (Z.to_nat k)))).

    (* the truncation window after k more divsteps still divides the old one *)
    assert (Hdvd_k : (2 ^ (64 - Z.of_nat n - k) | 2 ^ (64 - (Z.of_nat j + k)))).
    { replace (64 - (Z.of_nat j + k))
        with ((64 - Z.of_nat n - k) + (0 - Z.of_nat j + Z.of_nat n)) by ring.
      rewrite Z.pow_add_r by lia.
      apply Z.divide_factor_l. }
    assert (Hg1 : eqm (2 ^ (64 - Z.of_nat n - k)) g1
                      (divstep.g (fst (divstep.step_n (Z.to_nat k) (fst (divstep.step_n n st)))))).
    { rewrite divstep.g_hs by assumption.
      unfold eqm, g1.
      rewrite (Z2Nat.id _ Hk).
      rewrite <- Zmod_div_mod by (try lia; assumption).
      rewrite <- !Zaux.Zdiv_mod_mult by lia.
      rewrite <- Z.pow_add_r by lia.
      replace (k + (64 - Z.of_nat n - k)) with (64 - Z.of_nat n) by ring.
      f_equal.
      assumption. }
    assert (Hf1 : eqm (2 ^ (64 - Z.of_nat n - k)) f
                      (divstep.f (fst (divstep.step_n (Z.to_nat k) (fst (divstep.step_n n st)))))).
    { rewrite divstep.f_hs by assumption.
      unfold eqm.
      rewrite (Zmod_div_mod _ (2 ^ (64 - Z.of_nat n - k + k)) (divstep.f _)),
              (Zmod_div_mod _ (2 ^ (64 - Z.of_nat n - k + k)))
        by (try lia; rewrite Z.pow_add_r by lia; apply Z.divide_factor_l).
      f_equal.
      replace (64 - Z.of_nat n - k + k) with (64 - Z.of_nat n) by ring.
      assumption. }

    (* ===== Fold the k zero-divsteps into the model index: n1 = k + n ===== *)

    rewrite <- divstep.step_n_app_fst in *.

    assert (Htrans_k := divstep_trans.Trans.trans_n_step_n (Z.to_nat k) n st).
    rewrite divstep_trans.Trans.trans_hs in Htrans_k by assumption.
    unfold divstep_trans.Trans.mul in Htrans_k.
    cbn in Htrans_k.
    rewrite !Z.mul_0_l, !Z.mul_1_l, !Z.add_0_r in Htrans_k.
    replace (divstep_trans.Trans.v (divstep_trans.Trans.trans_n n st) * 2 ^ Z.of_nat (Z.to_nat k))
      with (divstep_trans.Trans.v (divstep_trans.Trans.trans_n (Z.to_nat k + n) st))
      by (rewrite <- Htrans_k; cbn; ring).
    replace (divstep_trans.Trans.u (divstep_trans.Trans.trans_n n st) * 2 ^ Z.of_nat (Z.to_nat k))
      with (divstep_trans.Trans.u (divstep_trans.Trans.trans_n (Z.to_nat k + n) st))
      by (rewrite <- Htrans_k; cbn; ring).
    replace (divstep_trans.Trans.r (divstep_trans.Trans.trans_n n st))
      with (divstep_trans.Trans.r (divstep_trans.Trans.trans_n (Z.to_nat k + n) st))
      by (rewrite <- Htrans_k; reflexivity).
    replace (divstep_trans.Trans.q (divstep_trans.Trans.trans_n n st))
      with (divstep_trans.Trans.q (divstep_trans.Trans.trans_n (Z.to_nat k + n) st))
      by (rewrite <- Htrans_k; reflexivity).
    replace (62 - Z.of_nat n - Z.of_nat (Z.to_nat k))
      with (62 - Z.of_nat (Z.to_nat k + n)) by lia.
    replace (64 - Z.of_nat n - k)
      with (64 - Z.of_nat (Z.to_nat k + n)) in * by lia.
    set (n1 := (Z.to_nat k + n)%nat) in *.
    assert (Hn1 : 0 <= Z.of_nat n1 <= 62) by lia.

    (* Hg1odd: after cancelling all trailing zeros g is odd -- unless the 62
       divsteps are already exhausted *)
    assert (Hg1odd : Zodd g1 \/ n1 = 62%nat).
    { destruct (Zeven_odd_dec g1) as [Hg1even|Hg1odd].

      - (* branch: g1 even -- then zeros was maximal only because i ran out *)
        right.
        apply Zeven_div2 in Hg1even.
        rewrite (Z_div_mod_eq_full g1 2) in Hg1even at 1.
        rewrite Z.div2_div in Hg1even.

        assert (Hgeven : g1 mod 2 = 0) by lia.
        clear Hg1even.
        unfold g1 in Hgeven.
        rewrite <- Zmod_div_mod, (Z2Nat.id _ Hk) in Hgeven
          by (first [apply Zpow_facts.Zpower_divide; lia | lia]).
        enough (Hg'1 : (2 ^ (zeros + 1) | g')).
        { specialize (Hzeros_opt (zeros + 1) Hg'1).
          lia. }

        apply Zmod_divide.

        + (* side: 2 ^ (zeros + 1) is nonzero *)
          apply Z.pow_nonzero; lia.
        + apply Zdivide_mod in Hg'zeros.
          rewrite Z.pow_add_r, Z.rem_mul_r, Hg'zeros, Z.add_0_l by lia.
          replace 0 with (2 ^ zeros * 0) by ring.
          rewrite Z.mul_cancel_l by lia.
          unfold g'.
          replace zeros with (k + Z.of_nat j) by lia.
          rewrite Z.pow_add_r, Zdiv_mult_cancel_r by lia.
          assumption.

      - (* branch: g1 odd -- the left disjunct *)
        left.
        assumption. }

    (* [clearbody] is load-bearing, not an optimisation: the [clear] below drops
       [zeros] / [g'] / [g] / [n], which the bodies of [k] / [g1] / [n1] mention
       (without it the [clear] fails: "zeros is used in hypothesis k"). *)
    clearbody n1 k g1.
    clear Htc_shift Hdvd_k zeros Hzeros_pos Hzeros62 Hg'zeros Hzeros_opt Hk Hkn Hgzeros
          g' Hgbound Hf Hg g Hmask Hbound Hn n Heta Htrans_k.

    (* if (i == 0) break *)
    forward_if.
    { (* branch: i == 0 -- the 62 divsteps are complete, break out of the loop *)
      rename H0 into Hi0.
      rewrite Hi0.
      replace n1 with 62%nat by lia.

      (* break *)
      forward.
      entailer!!. }

    rename H0 into Hi_ne.

    assert (Hn162 : Z.of_nat n1 < 62) by lia.
    clear Hi_ne.

    (* past the break the second disjunct of Hg1odd is impossible *)
    assert (Hg1o : Zodd g1).
    { destruct Hg1odd as [Hodd|Hn62].
      - assumption.
      - lia. }

    clear Hg1odd.
    rename Hg1o into Hg1odd.

    (* eta bounds feed the no-overflow typecheck of the negation / limit below *)
    assert (Heta := divstep.eta_bounds 683 n1 st H).

    (* if (eta < 0) -- negate eta, swap (f,g) -> (g,-f), then pick the
       bit-cancelling mask m and multiplier w (6 bits here, 4 bits below) *)
    forward_if (EX n2 : nat, EX u : Z, EX v : Z, EX f2 : Z, EX g2 : Z, EX w : int,
      PROP (1 <= Z.of_nat n2 <= 62 - Z.of_nat n1;
            Z.of_nat n2 <= 32;
            divstep_trans.Trans.u (divstep_trans.Trans.trans_n (n1 + n2) st) = (u * 2 ^ (Z.of_nat n2))%Z;
            divstep_trans.Trans.v (divstep_trans.Trans.trans_n (n1 + n2) st) = (v * 2 ^ (Z.of_nat n2))%Z;
            eqm (2 ^ (64 - Z.of_nat (n1 + n2))) f2 (divstep.f (fst (divstep.step_n (n1 + n2) st)));
            eqm (2 ^ (64 - Z.of_nat (n1 + n2))) g2 (divstep.g (fst (divstep.step_n (n1 + n2) st))))
      LOCAL (temp _i (Vint (Int.repr (62 - Z.of_nat n1)));
        temp _g (Vlong (Int64.repr (g2 * 2 ^ (Z.of_nat n2) - f2 * Int.unsigned w)));
        temp _f (Vlong (Int64.repr f2));
        temp _r (Vlong (Int64.repr (divstep_trans.Trans.r (divstep_trans.Trans.trans_n (n1 + n2) st) - v * Int.unsigned w)));
        temp _q (Vlong (Int64.repr (divstep_trans.Trans.q (divstep_trans.Trans.trans_n (n1 + n2) st) - u * Int.unsigned w)));
        temp _v (Vlong (Int64.repr v));
        temp _u (Vlong (Int64.repr u));
        temp _m (Vlong (Int64.repr (Z.ones (Z.of_nat n2))));
        temp _w (Vint w);
        gvars gv;
        temp _eta (Vlong (Int64.repr (divstep.eta (fst (divstep.step_n (n1 + n2) st)) + Z.of_nat n2)));
        temp _f0 (Vlong (Int64.repr (divstep.f st)));
        temp _g0 (Vlong (Int64.repr (divstep.g st)));
        temp _t t)
      SEP (data_at_ sh t_secp256k1_modinv64_trans2x2 t;
        debruijn64_array sh_debruijn gv))%assert.
    { (* branch: eta < 0 -- negate eta and swap the (f,g) / (u,q) / (v,r) pairs *)
      rename H0 into Heta_neg.

      (* eta = -eta *)
      forward.
      { (* tc: negating eta stays inside int64 *)
        entailer!!.
        rewrite Int64.signed_zero.
        rep_lia. }

      rewrite Int64.neg_repr.

      (* tmp = f *)
      forward.

      (* f = g *)
      forward.

      (* g = -tmp *)
      forward.
      rewrite Int64.neg_repr.

      (* tmp = u *)
      forward.

      (* u = q *)
      forward.

      (* q = -tmp *)
      forward.
      rewrite Int64.neg_repr.

      (* tmp = v *)
      forward.

      (* v = r *)
      forward.

      (* r = -tmp *)
      forward.
      rewrite Int64.neg_repr.

      (* limit = ((int)eta + 1) > i ? i : ((int)eta + 1) *)
      forward_if (temp _t'2 (Vint (Int.repr (Z.min (62 - Z.of_nat n1)
                                                   ((- divstep.eta (fst (divstep.step_n n1 st))) + 1))))).
      { (* tc: the int cast of (eta + 1) stays inside int32 *)
        entailer!!.
        rewrite Int_repr_Int64_Z_mod_modulus.
        rewrite Int.signed_repr by rep_lia.
        rewrite Int.signed_repr by rep_lia.
        rep_lia. }

      { (* branch: (int)eta + 1 > i -- limit = i *)
        rewrite Int64.Z_mod_modulus_eq in H0.
        rewrite Z.mod_small in H0 by rep_lia.
        rewrite Int.signed_repr in H0 by rep_lia.

        (* _t'2 = (tint) i *)
        forward.
        entailer!!.
        rewrite Z.min_l by lia.
        reflexivity. }

      { (* branch: (int)eta + 1 <= i -- limit = eta + 1 *)
        rewrite Int64.Z_mod_modulus_eq in H0.
        rewrite Z.mod_small in H0 by rep_lia.
        rewrite Int.signed_repr in H0 by rep_lia.

        (* _t'2 = (tint)((tint) eta + 1) *)
        forward.
        { (* tc: eta + 1 stays inside int32 *)
          entailer!!.
          rewrite Int_repr_Int64_Z_mod_modulus.
          rewrite Int.signed_repr by rep_lia.
          rewrite Int.signed_repr by rep_lia.
          rep_lia. }

        entailer!!.
        rewrite Z.min_r by lia.
        reflexivity. }

      (* limit = _t'2 *)
      forward.
      replace (Z.of_nat j + Z.of_nat (Z.to_nat k) + (64 - (Z.of_nat j + Z.of_nat (Z.to_nat k))))
        with 64 by ring.

      (* m = (UINT64_MAX >> (64 - limit)) & 63 -- the bottom min(limit, 6) bits *)
      forward.
      { (* tc: the shift count 64 - limit stays below the word size *)
        entailer!!.
        change (Int.unsigned Int64.iwordsize') with 64.
        lia. }

      rewrite sub_repr.
      rewrite !Int.unsigned_repr by rep_lia.
      rewrite Int64_shru_shiftr.
      rewrite !Int64.unsigned_repr_eq.
      change Int64.modulus with (2 ^ 64).
      rewrite (Z.mod_small (64 - _)) by lia.
      rewrite and64_repr.
      change 63 with (Z.ones 6).
      rewrite <- Z.land_ones by lia.
      rewrite Z.land_m1_l.
      rewrite Z_shiftr_ones by lia.
      rewrite subsub1.
      rewrite Z_land_ones_min by lia.

      set (n2 := Z.min (Z.min (62 - Z.of_nat n1)
                              (- divstep.eta (fst (divstep.step_n n1 st)) + 1)) 6).
      pose (w := (mod_inv (- g1) (2 ^ n2) * (- f)) mod (2 ^ n2)).

      (* w = (f * g * (f * f - 2)) & m *)
      forward.
      Exists (Z.to_nat n2)
             (divstep_trans.Trans.q (divstep_trans.Trans.trans_n n1 st))
             (divstep_trans.Trans.r (divstep_trans.Trans.trans_n n1 st))
             g1
             ((- f + g1 * w) / 2 ^ n2)
             (Int.repr w).
      entailer!!.
      rewrite Nat.add_comm.
      rewrite <- divstep_trans.Trans.trans_n_step_n.

      (* the model g is odd at step n1, transported from Hg1odd through Hg1 *)
      assert (Hgn1 : Zodd (divstep.g (fst (divstep.step_n n1 st)))).
      { rewrite <- Zodd_bool_iff, <- Z.bit0_odd in * |- *.
        change (Z.testbit (divstep.g (fst (divstep.step_n n1 st))) 0)
          with (true && (Z.testbit (divstep.g (fst (divstep.step_n n1 st))) 0))%bool.
        rewrite <- (Z.ones_spec_low (64 - Z.of_nat n1) 0) at 1 by lia.
        rewrite <- Z.land_spec, Z.land_comm, Z.land_ones, <- Hg1,
                <- Z.land_ones, Z.land_comm, Z.land_spec, Z.ones_spec_low by lia.
        assumption. }

      (* the two delta side conditions of [trans_ds] (eta = -delta) *)
      assert (Hdelta : 0 < divstep.delta (fst (divstep.step_n n1 st)))
        by (unfold divstep.eta in Heta_neg; lia).
      assert (Hn2_delta : 0 < Z.of_nat (Z.to_nat n2)
                            <= 1 + divstep.delta (fst (divstep.step_n n1 st)))
        by (unfold divstep.eta in Heta_neg; unfold n2, divstep.eta; lia).
      rewrite divstep_trans.Trans.trans_ds by assumption.

      split.
      { (* conjunct: the u entry scales by 2^n2 *)
        cbn.
        ring. }

      split.
      { (* conjunct: the v entry scales by 2^n2 *)
        cbn.
        ring. }

      rewrite Nat2Z.inj_add, Z2Nat.id, divstep.step_n_app_fst by lia.
      injection (divstep_trans.Trans.trans_n_step (Z.to_nat n2) (fst (divstep.step_n n1 st))).
      intros Hg2 Hf2.
      rewrite divstep_trans.Trans.trans_ds in Hf2, Hg2 by assumption.
      cbn in Hf2, Hg2.
      ring_simplify in Hf2.
      ring_simplify in Hg2.

      assert (Hn2pow : 0 < 2 ^ n2 <= 2 ^ 6) by (split; [|apply Z.pow_le_mono_r]; lia).
      assert (Hwmod := Z.mod_pos_bound (mod_inv (- g1) (2 ^ n2) * (- f)) (2 ^ n2)).
      assert (Hw : 0 <= w < 2 ^ 6) by (unfold w; lia).
      rewrite !(Int.unsigned_repr w) by rep_lia.

      (* w is exactly the multiple of f that clears the bottom n2 bits of g *)
      assert (Hg1fw : (2 ^ n2 | (- f) + g1 * w)).
      { apply Zmod_divide.
        { (* side: 2 ^ n2 is nonzero *)
          lia. }

        unfold w.
        rewrite <- Zplus_mod_idemp_r, Zmult_mod_idemp_r, Zplus_mod_idemp_r, Z.mul_assoc,
                <- Z.sub_opp_r, !Zopp_mult_distr_l, <- Zminus_mod_idemp_r, <- Zmult_mod_idemp_l,
                mod_inv_mul_r, Z.gcd_opp_l.
        rewrite Hgcd by (first [assumption | lia]).
        rewrite Zmult_mod_idemp_l, Zminus_mod_idemp_r, Z.mul_1_l, Z.sub_diag, Zmod_0_l; lia. }

      (* the same w, written against the model f / g at step n1 *)
      assert (Hw0 : w = (mod_inv (- divstep.g (fst (divstep.step_n n1 st))) (2 ^ n2)
                         * (- divstep.f (fst (divstep.step_n n1 st)))) mod 2 ^ n2).
      { assert (Hn2 : (2 ^ n2 | 2 ^ (64 - Z.of_nat n1)))
          by (exists (2 ^ ((64 - Z.of_nat n1) - n2)); rewrite <- Z.pow_add_r by lia; f_equal; ring).
        apply Zmult_eqm.
        - unfold eqm.
          f_equal.
          apply mod_inv_eqm.
          apply Zopp_eqm.
          apply (eqm_2_pow_le _ (64 - Z.of_nat n1)).
          + lia.
          + apply Hg1.
        - apply (eqm_2_pow_le _ (64 - Z.of_nat n1)).
          + lia.
          + apply Zopp_eqm.
            apply Hf1. }

      rewrite Z.mul_cancel_l in Hf2 by lia.

      repeat split.

      - (* conjunct: the new f is the old g mod 2^(64 - (n1+n2)) *)
        rewrite Hf2.
        apply (eqm_2_pow_le _ (64 - Z.of_nat n1)).
        + lia.
        + assumption.

      - (* conjunct: the new g is (-f + g1*w) / 2^n2 mod 2^(64 - (n1+n2)) *)
        rewrite Z2Nat.id in Hg2 by lia.
        unfold eqm.
        rewrite <- Zaux.Zdiv_mod_mult by lia.
        symmetry.
        apply Z.div_unique_exact.

        + (* side: 2 ^ n2 is nonzero *)
          lia.
        + rewrite <- Zmult_mod_distr_l, <- Z.pow_add_r, Hg2 by lia.
          replace (n2 + (64 - (n2 + Z.of_nat n1))) with (64 - Z.of_nat n1) by ring.
          apply Zplus_eqm.
          * apply Zopp_eqm.
            assumption.
          * rewrite (Z.mul_comm _ (divstep.g (fst (divstep.step_n n1 st)))).
            apply Zmult_eqm; try assumption.
            unfold eqm.
            f_equal.
            assumption.

      - (* conjunct: the C word for g after g += f*w *)
        repeat f_equal.
        rewrite Z.mul_comm, <- Z_div_exact_full_2 by (try lia; apply Zdivide_mod; assumption).
        ring.

      - (* conjunct: the C word for r after r += v*w *)
        repeat f_equal.
        apply Z.sub_move_r.
        rewrite <- Hw0.
        cbn.
        ring.

      - (* conjunct: the C word for q after q += u*w *)
        repeat f_equal.
        apply Z.sub_move_r.
        rewrite <- Hw0.
        cbn.
        ring.

      - (* conjunct: w = (f*g*(f*f-2)) & m -- Hacker's Delight inverse mod 2^n2 *)
        repeat f_equal.
        rewrite Int64.unsigned_repr_eq.
        change Int64.modulus with (2 ^ 64).
        rewrite Z.land_ones by lia.

        assert (Hn264 : 2 ^ n2 < 2 ^ 64) by (apply Z.pow_lt_mono_r; lia).
        assert (Hmod := Z.mod_pos_bound (g1 * - f * (g1 * g1 - 2)) (2 ^ n2)).
        rewrite Z.mod_small by lia.
        unfold w.
        replace (g1 * - f * (g1 * g1 - 2)) with (g1 * (g1 * g1 - 2) * - f) by ring.
        do 2 (rewrite <- Zmult_mod_idemp_l; symmetry).
        do 2 f_equal.
        symmetry.
        rewrite <- Z.land_ones by lia.
        replace n2 with (Z.min 6 n2) at 1 by lia.
        rewrite <- Z_land_ones_min, Z.land_assoc by lia.
        rewrite hackers_delight_b by (apply Zodd_equiv; assumption).
        rewrite Z.land_ones by lia.
        rewrite <- (Z.mul_1_l (mod_inv _ _)), <- Zmult_mod_idemp_l.
        rewrite <- (Hgcd g1 n2) at 1 by (first [assumption | lia]).
        rewrite <- Z.gcd_opp_l, <- Zmult_mod_idemp_r, <- mod_inv_mul_l, Zmult_mod_idemp_r,
                Zmult_mod_idemp_l, <- Z.mul_assoc.
        rewrite <- Z.land_ones by lia.
        replace n2 with (Z.min 6 n2) at 2 by lia.
        rewrite <- Z_land_ones_min, Z.land_assoc by lia.
        rewrite !Z.land_ones by lia.
        rewrite <- Zmult_mod_idemp_r, mod_inv_mul_r, Z.gcd_opp_l, Hgcd, Zmult_mod_idemp_r,
                Z.mul_1_r by (first [assumption | lia]).
        rewrite <- Zmod_div_mod.
        + reflexivity.

        + (* side: 0 < 2 ^ n2 *)
          lia.

        + (* side: 0 < 2 ^ 6 *)
          lia.

        + (* side: 2 ^ n2 divides 2 ^ 6 *)
          exists (2 ^ (6 - n2)).
          rewrite <- Z.pow_add_r by lia.
          f_equal.
          ring.

      - (* conjunct: eta after the n2 divsteps *)
        repeat f_equal.

        assert (Hn2_eta : 0 < Z.of_nat (Z.to_nat n2)
                            <= 1 - divstep.eta (fst (divstep.step_n n1 st)))
          by (unfold n2; lia).
        rewrite divstep.eta_ds by assumption.
        lia. }

    { (* branch: eta >= 0 -- keep (f,g) and use the 4-bit cancellation formula *)
      rename H0 into Heta_pos.

      (* limit = ((int)eta + 1) > i ? i : ((int)eta + 1) *)
      forward_if (temp _t'3 (Vint (Int.repr (Z.min (62 - Z.of_nat n1)
                                                   (divstep.eta (fst (divstep.step_n n1 st)) + 1))))).
      { (* tc: the int cast of (eta + 1) stays inside int32 *)
        entailer!!.
        rewrite Int_repr_Int64_Z_mod_modulus.
        rewrite Int.signed_repr by rep_lia.
        rewrite Int.signed_repr by rep_lia.
        rep_lia. }

      { (* branch: (int)eta + 1 > i -- limit = i *)
        rewrite Int64.Z_mod_modulus_eq in H0.
        rewrite Z.mod_small in H0 by rep_lia.
        rewrite Int.signed_repr in H0 by rep_lia.

        (* _t'3 = (tint) i *)
        forward.
        entailer!!.
        rewrite Z.min_l by lia.
        reflexivity. }

      { (* branch: (int)eta + 1 <= i -- limit = eta + 1 *)
        rewrite Int64.Z_mod_modulus_eq in H0.
        rewrite Z.mod_small in H0 by rep_lia.
        rewrite Int.signed_repr in H0 by rep_lia.

        (* _t'3 = (tint)((tint) eta + 1) *)
        forward.
        { (* tc: eta + 1 stays inside int32 *)
          entailer!!.
          rewrite Int_repr_Int64_Z_mod_modulus.
          rewrite Int.signed_repr by rep_lia.
          rewrite Int.signed_repr by rep_lia.
          rep_lia. }

        entailer!!.
        rewrite Z.min_r by lia.
        reflexivity. }

      (* limit = _t'3 *)
      forward.
      replace (Z.of_nat j + Z.of_nat (Z.to_nat k) + (64 - (Z.of_nat j + Z.of_nat (Z.to_nat k))))
        with 64 by ring.

      (* m = (UINT64_MAX >> (64 - limit)) & 15 -- the bottom min(limit, 4) bits *)
      forward.
      { (* tc: the shift count 64 - limit stays below the word size *)
        entailer!!.
        change (Int.unsigned Int64.iwordsize') with 64.
        lia. }

      rewrite sub_repr.
      rewrite !Int.unsigned_repr by rep_lia.
      rewrite Int64_shru_shiftr.
      rewrite !Int64.unsigned_repr_eq.
      change Int64.modulus with (2 ^ 64).
      rewrite (Z.mod_small (64 - _)) by lia.
      rewrite and64_repr.
      change 15 with (Z.ones 4).
      rewrite <- Z.land_ones by lia.
      rewrite Z.land_m1_l.
      rewrite Z_shiftr_ones by lia.
      rewrite subsub1.
      rewrite Z_land_ones_min by lia.

      set (n2 := Z.min (Z.min (62 - Z.of_nat n1)
                              (divstep.eta (fst (divstep.step_n n1 st)) + 1)) 4).
      pose (w := (mod_inv (- f) (2 ^ n2) * g1) mod (2 ^ n2)).

      (* w = f + (((f + 1) & 4) << 1) *)
      forward.

      (* w = (-w * g) & m *)
      forward.
      Exists (Z.to_nat n2)
             (divstep_trans.Trans.u (divstep_trans.Trans.trans_n n1 st))
             (divstep_trans.Trans.v (divstep_trans.Trans.trans_n n1 st))
             f
             ((g1 + f * w) / 2 ^ n2)
             (Int.repr w).
      entailer!!.
      rewrite Nat.add_comm.
      rewrite <- divstep_trans.Trans.trans_n_step_n.

      (* the two delta side conditions of [trans_ss] (eta = -delta) *)
      assert (Hdelta : divstep.delta (fst (divstep.step_n n1 st)) <= 0)
        by (unfold divstep.eta in Heta_pos; lia).
      assert (Hn2_delta : Z.of_nat (Z.to_nat n2)
                          <= 1 - divstep.delta (fst (divstep.step_n n1 st)))
        by (unfold divstep.eta in Heta_pos; unfold n2, divstep.eta; lia).
      rewrite divstep_trans.Trans.trans_ss by assumption.

      split.
      { (* conjunct: the u entry scales by 2^n2 *)
        cbn.
        ring. }

      split.
      { (* conjunct: the v entry scales by 2^n2 *)
        cbn.
        ring. }

      rewrite Nat2Z.inj_add, Z2Nat.id, divstep.step_n_app_fst by lia.
      injection (divstep_trans.Trans.trans_n_step (Z.to_nat n2) (fst (divstep.step_n n1 st))).
      intros Hg2 Hf2.
      rewrite divstep_trans.Trans.trans_ss in Hf2, Hg2 by assumption.
      cbn in Hf2, Hg2.
      ring_simplify in Hf2.
      ring_simplify in Hg2.

      assert (Hn2pow : 0 < 2 ^ n2 <= 2 ^ 4) by (split; [|apply Z.pow_le_mono_r]; lia).
      assert (Hwmod := Z.mod_pos_bound (mod_inv (- f) (2 ^ n2) * g1) (2 ^ n2)).
      assert (Hw : 0 <= w < 2 ^ 4) by (unfold w; lia).
      rewrite !(Int.unsigned_repr w) by rep_lia.

      (* w is exactly the multiple of f that clears the bottom n2 bits of g *)
      assert (Hg1fw : (2 ^ n2 | g1 + f * w)).
      { apply Zmod_divide.
        { (* side: 2 ^ n2 is nonzero *)
          lia. }

        unfold w.
        rewrite <- Zplus_mod_idemp_r, Zmult_mod_idemp_r, Zplus_mod_idemp_r, Z.mul_assoc,
                <- Z.sub_opp_r, !Zopp_mult_distr_l, <- Zminus_mod_idemp_r, <- Zmult_mod_idemp_l,
                mod_inv_mul_r, Z.gcd_opp_l.
        rewrite Hgcd by (first [assumption | lia]).
        rewrite Zmult_mod_idemp_l, Zminus_mod_idemp_r, Z.mul_1_l, Z.sub_diag, Zmod_0_l; lia. }

      (* the same w, written against the model f / g at step n1 *)
      assert (Hw0 : w = (mod_inv (- divstep.f (fst (divstep.step_n n1 st))) (2 ^ n2)
                         * divstep.g (fst (divstep.step_n n1 st))) mod 2 ^ n2).
      { assert (Hn2 : (2 ^ n2 | 2 ^ (64 - Z.of_nat n1)))
          by (exists (2 ^ ((64 - Z.of_nat n1) - n2)); rewrite <- Z.pow_add_r by lia; f_equal; ring).
        apply Zmult_eqm.
        - unfold eqm.
          f_equal.
          apply mod_inv_eqm.
          apply Zopp_eqm.
          apply (eqm_2_pow_le _ (64 - Z.of_nat n1)).
          + lia.
          + apply Hf1.
        - apply (eqm_2_pow_le _ (64 - Z.of_nat n1)).
          + lia.
          + apply Hg1. }

      rewrite Z.mul_cancel_l in Hf2 by lia.

      repeat split.

      - (* conjunct: f is unchanged by the n2 divsteps *)
        rewrite Hf2.
        apply (eqm_2_pow_le _ (64 - Z.of_nat n1)).
        + lia.
        + assumption.

      - (* conjunct: the new g is (g1 + f*w) / 2^n2 mod 2^(64 - (n1+n2)) *)
        rewrite Z2Nat.id in Hg2 by lia.
        unfold eqm.
        rewrite <- Zaux.Zdiv_mod_mult by lia.
        symmetry.
        apply Z.div_unique_exact.

        + (* side: 2 ^ n2 is nonzero *)
          lia.
        + rewrite <- Zmult_mod_distr_l, <- Z.pow_add_r, Hg2 by lia.
          replace (n2 + (64 - (n2 + Z.of_nat n1))) with (64 - Z.of_nat n1) by ring.
          rewrite (Z.add_comm _ (divstep.g (fst (divstep.step_n n1 st)))).
          apply Zplus_eqm; try assumption.
          rewrite (Z.mul_comm _ (divstep.f (fst (divstep.step_n n1 st)))).
          apply Zmult_eqm; try assumption.
          unfold eqm.
          f_equal.
          assumption.

      - (* conjunct: the C word for g after g += f*w *)
        repeat f_equal.
        rewrite Z.mul_comm, <- Z_div_exact_full_2 by (try lia; apply Zdivide_mod; assumption).
        ring.

      - (* conjunct: the C word for r after r += v*w *)
        repeat f_equal.
        apply Z.sub_move_r.
        rewrite <- Hw0.
        cbn.
        ring.

      - (* conjunct: the C word for q after q += u*w *)
        repeat f_equal.
        apply Z.sub_move_r.
        rewrite <- Hw0.
        cbn.
        ring.

      - (* conjunct: w = (-(f + ((f+1)&4)<<1) * g) & m -- the 4-bit inverse *)
        repeat f_equal.
        rewrite (Int.unsigned_repr 1) by rep_lia.
        rewrite Int64.shl_mul_two_p.
        rewrite two_p_equiv.
        rewrite (Int64.unsigned_repr 1) by rep_lia.
        rewrite mul64_repr.
        rewrite add64_repr.
        rewrite !Int64.unsigned_repr_eq.
        rewrite Int.unsigned_repr_eq.
        change Int64.modulus with (2 ^ 64).
        change Int.modulus with (2 ^ 32).
        rewrite Z.land_ones by lia.

        assert (Hn264 : 2 ^ n2 < 2 ^ 64) by (apply Z.pow_lt_mono_r; lia).
        assert (Hmod := Z.mod_pos_bound
                          (- ((f + Z.land (f + 1) 4 * 2 ^ 1) mod 2 ^ 64) mod 2 ^ 32 * g1) (2 ^ n2)).
        rewrite Z.mod_small by lia.
        unfold w.
        do 2 (rewrite <- Zmult_mod_idemp_l; symmetry).
        do 2 f_equal.
        rewrite <- Zmod_div_mod
          by (first [lia | (exists (2 ^ (32 - n2)); rewrite <- Z.pow_add_r by lia; f_equal; ring)]).
        rewrite <- (Z.mul_1_l (_ mod (2 ^ 64))), <- Z.mul_opp_l, <- Zmult_mod_idemp_r.
        rewrite <- Zmod_div_mod, Zmult_mod_idemp_r
          by (first [lia | (exists (2 ^ (64 - n2)); rewrite <- Z.pow_add_r by lia; f_equal; ring)]).
        rewrite (Zmod_div_mod (2 ^ n2) (2 ^ 4))
          by (first [lia | (exists (2 ^ (4 - n2)); rewrite <- Z.pow_add_r by lia; f_equal; ring)]).
        rewrite <- (Z.mul_1_r (mod_inv (- f) (2 ^ n2))).
        rewrite <- (Hgcd f 4) at 1 by (first [assumption | lia]).
        rewrite <- Z.gcd_opp_l, <- Zmult_mod_idemp_r, <- mod_inv_mul_r, Zmult_mod_idemp_r,
                Z.mul_assoc.
        rewrite <- Zmod_div_mod
          by (first [lia | (exists (2 ^ (4 - n2)); rewrite <- Z.pow_add_r by lia; f_equal; ring)]).
        rewrite <- Zmult_mod_idemp_l, mod_inv_mul_l, Z.gcd_opp_l, Hgcd, Zmult_mod_idemp_l,
                Z.mul_1_l by (first [assumption | lia]).
        rewrite <- hackers_delight_a, Z.land_ones by (try lia; apply Zodd_equiv; assumption).
        rewrite <- Zmod_div_mod
          by (first [lia | (exists (2 ^ (4 - n2)); rewrite <- Z.pow_add_r by lia; f_equal; ring)]).
        rewrite Z.mul_opp_l, Z.mul_1_l.
        do 3 f_equal.
        rewrite Z.shiftl_mul_pow2; lia.

      - (* conjunct: eta after the n2 divsteps *)
        repeat f_equal.
        rewrite divstep.eta_ss; lia. }

    Intros n2 u v f2 g2 w.
    rename H0 into Hn2.
    rename H1 into Hn232.
    rename H2 into Hu.
    rename H3 into Hv.
    rename H4 into Hf2.
    rename H5 into Hg2.

    (* ===== Apply the cancellation multiplier: g += f*w; q += u*w; r += v*w ===== *)

    (* g += f * w *)
    forward.

    (* q += u * w *)
    forward.

    (* r += v * w *)
    forward.
    rewrite !mul64_repr.
    rewrite !add64_repr.
    ring_simplify (g2 * 2 ^ Z.of_nat n2 - f2 * Int.unsigned w + f2 * Int.unsigned w).
    ring_simplify (divstep_trans.Trans.q (divstep_trans.Trans.trans_n (n1 + n2) st)
                   - u * Int.unsigned w + u * Int.unsigned w).
    ring_simplify (divstep_trans.Trans.r (divstep_trans.Trans.trans_n (n1 + n2) st)
                   - v * Int.unsigned w + v * Int.unsigned w).

    (* ===== Loop back: bottom bits cancelled, re-establish the invariant ===== *)

    Exists (n1 + n2)%nat n2 u v f2 g2.
    rewrite Nat2Z.inj_add in * |- *.
    replace (62 - (Z.of_nat n1 + Z.of_nat n2) + Z.of_nat n2)
      with (62 - Z.of_nat n1) by ring.
    entailer!!.

  - (* ===== After the loop: store t->{u,v,q,r} and return eta ===== *)

    (* t->u = (int64_t)u *)
    forward.

    (* t->v = (int64_t)v *)
    forward.

    (* t->q = (int64_t)q *)
    forward.

    (* t->r = (int64_t)r *)
    forward.

    (* return eta *)
    forward.
Qed.
