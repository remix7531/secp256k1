(** * theory.modinv.construction.divstep_trans: the divstep transition-matrix algebra --
    [Module Trans]: 2x2 integer matrices ([V2] / [M2x2] / [mul] / [det] / [prod]
    / [bounded]) and the per-step transition matrices ([trans] / [trans_n]) with
    their H-shift / S-phase / D-phase closed forms ([trans_hs] / [trans_ss] /
    [trans_ds]). *)
(** Copyright (C) 2026 remix7531
    Ported from BlockstreamResearch/simplicity Coq/C/divstep.v
    (commit c1dddedd), Copyright (c) 2018 Blockstream, originally MIT.
    Upstream notice reproduced in proof/README.md.
    SPDX-License-Identifier: MIT *)

(** Builds on the variable-time state machine in [divstep].

    Adapted for Rocq 9.0 / VST 2.16. *)

Require Import ZArith.
Require Import ZArith.Znumtheory.
Require Import ZArith.Zpow_facts.
Require Import Lia.
Require Import List.

Require Import secp256k1.theory.modinv.divsteps.def.
Require Import secp256k1.theory.extra_math.
Require Import secp256k1.theory.modinv.construction.inverse.
Require Import secp256k1.theory.modinv.construction.divstep.

Open Scope list_scope.
Open Scope Z_scope.
Arguments Z.add !x !y.
Arguments Z.sub !m !n.
Arguments Z.mul !x !y.

(* ================================================================= *)
(** ** Transition-matrix algebra -- [Trans]: 2x2 matrices over [Z]. *)

Module Trans.

(** A 2-vector [(x, y)] over [Z]. *)
Record V2 :=
{ x : Z; y : Z }.

(** Scalar multiplication of a vector. *)
Definition scale (c : Z) (vec : V2) :=
{| x := c * (x vec);
   y := c * (y vec)
|}.

(** [scale] composes multiplicatively. *)
Lemma scale_mul c1 c2 vec : scale (c1 * c2) vec = scale c1 (scale c2 vec).
Proof.
  destruct vec.
  unfold scale; simpl; f_equal; ring.
Qed.

(** A 2x2 matrix [[u v; q r]] over [Z]. *)
Record M2x2 :=
{ u : Z; v : Z; q : Z; r : Z}.

(** The identity matrix. *)
Definition I : M2x2 :=
{| u := 1;
   v := 0;
   q := 0;
   r := 1
|}.

(** Matrix-vector application. *)
Definition ap (m : M2x2) (vec : V2) : V2 :=
{| x := (u m) * (x vec) + (v m) * (y vec);
   y := (q m) * (x vec) + (r m) * (y vec)
|}.

(** [ap] commutes with scaling. *)
Lemma ap_scale m c vec : ap m (scale c vec) = scale c (ap m vec).
Proof.
  destruct m, vec.
  unfold ap, scale; simpl; f_equal; ring.
Qed.

(** Matrix multiplication. *)
Definition mul (m1 m2: M2x2) : M2x2 :=
{| u := (u m1) * (u m2) + (v m1) * (q m2);
   v := (u m1) * (v m2) + (v m1) * (r m2);
   q := (q m1) * (u m2) + (r m1) * (q m2);
   r := (q m1) * (v m2) + (r m1) * (r m2)
|}.

(** Matrix multiplication is associative. *)
Lemma mul_assoc m1 m2 m3 : mul m1 (mul m2 m3) = mul (mul m1 m2) m3.
Proof.
  destruct m1, m2, m3.
  unfold mul; simpl; f_equal; ring.
Qed.

(** [ap] of a product is the composition of applications. *)
Lemma ap_mul m1 m2 vec : ap (mul m1 m2) vec = ap m1 (ap m2 vec).
Proof.
  destruct m1, m2, vec.
  unfold ap, mul; simpl; f_equal; ring.
Qed.

(** The determinant of a matrix. *)
Definition det (m: M2x2) : Z := (u m) * (r m) - (v m) * (q m).

(** The determinant is multiplicative. *)
Lemma det_mul m1 m2 : det (mul m1 m2) = det m1 * det m2.
Proof.
  destruct m1, m2.
  cbn.
  ring.
Qed.

(** Product of a list of matrices (right fold, starting from [I]). *)
Definition prod : list M2x2 -> M2x2 := fold_right mul I.

(** [prod] of an append factors as a product. *)
Lemma prod_app l1 l2 : prod (l1 ++ l2) = mul (prod l1) (prod l2).
Proof.
  induction l1.
  - (* base: l1 = nil *)
    cbn; destruct (prod l2); unfold mul; cbn; f_equal; ring.
  - (* step: l1 = a :: l1 *)
    cbn.
    rewrite IHl1.
    destruct (prod l1); destruct (prod l2); unfold mul; cbn; f_equal; ring.
Qed.

(** Determinant of a product is the product of determinants. *)
Lemma det_prod ms : det (prod ms) = fold_right Z.mul 1 (map det ms).
Proof.
  induction ms; try reflexivity.
  simpl.
  rewrite det_mul.
  congruence.
Qed.

(** Row-sum / row-magnitude bound on a matrix. *)
Definition bounded (b : Z) (m : M2x2) :=
  (Z.abs (u m) + Z.abs (v m) <= b /\ -b < u m + v m) /\
  (Z.abs (q m) + Z.abs (r m) <= b /\ -b < q m + r m).

(** The identity is bounded by [1]. *)
Lemma bounded_I : bounded 1 I.
Proof.
  unfold bounded.
  simpl.
  lia.
Qed.

(** The transition matrix of a single step. *)
Definition trans (s : Step) : M2x2 :=
match s with
| Step.H => {| u := 2; v := 0; q := 0; r := 1 |}
| Step.D => {| u := 0; v := 2; q := -1; r := 1 |}
| Step.S => {| u := 2; v := 0; q := 1; r := 1 |}
end.

(** The [(f, g)] vector of a state. *)
Definition fg st := {| x := f st; y := g st |}.

(** One step doubles the [(f, g)] vector, realized by [trans]. *)
Lemma trans_step st :
  scale 2 (fg (fst (step st))) = ap (trans (snd (step st))) (fg st).
Proof.
  destruct (spec st);
  unfold scale,ap, fg; cbn;
  f_equal; ring.
Qed.

(** Each transition matrix has determinant [2]. *)
Lemma det_trans s : det (trans s) = 2.
Proof.
  destruct s; reflexivity.
Qed.

(** Left-multiplying by a [trans] doubles the bound. *)
Lemma bounded_mul_trans b m s : bounded b m -> bounded (2*b) (mul (trans s) m).
Proof.
  destruct m as [u v q r].
  intros [Huv Hqr]; simpl in *.
  destruct s; unfold bounded; simpl; lia.
Qed.

(** The accumulated transition matrix over [n] steps. *)
Definition trans_n (n : nat) (st : State) : M2x2 :=
  prod (map trans (snd (step_n n st))).

(** [trans_n (S n)] factors as a [trans] times [trans_n n]. *)
Lemma trans_n_S n st : {x | trans_n (S n) st = mul (trans x) (trans_n n st)}.
Proof.
  unfold trans_n.
  simpl.
  destruct (step_n n st) as [st0 xs] eqn:Hxs.
  destruct (step st0) as [st1 x].
  exists x.
  reflexivity.
Qed.

(** [trans_n] scales the [(f, g)] vector by [2^n]. *)
Lemma trans_n_step n st :
  scale (2^(Z.of_nat n)) (fg (fst (step_n n st))) = ap (trans_n n st) (fg st).
Proof.
  induction n.
   rewrite Z.pow_0_r.
   destruct st; unfold scale, fg, ap; cbn.
   f_equal; ring.
  rewrite Nat2Z.inj_succ, Z.pow_succ_r by lia.
  unfold trans_n in *.
  simpl.
  destruct (step_n n st) as [st0 xs]; simpl in *.
  assert (Htrans := trans_step st0).
  destruct (step st0) as [st1 x]; simpl in *.
  rewrite ap_mul, <- IHn, ap_scale, Z.mul_comm, scale_mul by auto.
  f_equal.
  apply Htrans.
Qed.

(** [det (trans_n n st) = 2^n]. *)
Lemma det_trans_n n st : det (trans_n n st) = 2^(Z.of_nat n).
Proof.
  revert st.
  induction n; try reflexivity.
  intros st.
  destruct (trans_n_S n st) as [x ->].
  rewrite det_mul, det_trans, Nat2Z.inj_succ, Z.pow_succ_r by lia.
  congruence.
Qed.

(** [trans_n n st] is bounded by [2^n]. *)
Lemma bounded_trans_n n st : bounded (2^(Z.of_nat n)) (trans_n n st).
Proof.
  induction n; try apply bounded_I.
  destruct (trans_n_S n st) as [x ->].
  rewrite Nat2Z.inj_succ, Z.pow_succ_r by lia.
  auto using bounded_mul_trans.
Qed.

(** [trans_n] composes across a [step_n] split. *)
Lemma trans_n_step_n (n m : nat) (st : State) :
  mul (trans_n n (fst (step_n m st))) (trans_n m st) = trans_n (n + m) st.
Proof.
  unfold trans_n.
  rewrite step_n_app_snd, map_app, prod_app.
  reflexivity.
Qed.

(** When [g] is divisible by [2^n], the accumulated matrix is the H-shift form. *)
Lemma trans_hs n st : (2^(Z.of_nat n) | g st) ->
  trans_n n st = {| u := 2^(Z.of_nat n); v := 0; q := 0; r := 1 |}.
Proof.
  induction n;[intros; reflexivity|].
  rewrite Nat2Z.inj_succ, Z.pow_succ_r by lia.
  intros Hg.
  unfold trans_n in *.
  simpl (snd _).
  assert (Hg' : (2 ^ Z.of_nat n | g st)) by (etransitivity;[|apply Hg]; auto with *).
  divide_halving_massage Hg n.
  rewrite <- g_hs in Hg by assumption.
  destruct (step_n n st).
  transitivity (mul (trans Step.H) {| u := 2^(Z.of_nat n); v := 0; q := 0; r := 1 |}).
  - (* main goal: equal to the H-product *)
    rewrite <- IHn by assumption.
    destruct (spec s);
    simpl in Hg;
    try solve [rewrite Zmod_odd, Z.add_comm, Z.odd_add_mul_2 in Hg;
               discriminate].
    reflexivity.
  - (* side goal: the H-product reduces to the shift form *)
    unfold mul;cbn;f_equal; ring.
Qed.

(** In the S-phase, the accumulated matrix is the modular-inverse shift form. *)
Lemma trans_ss n st : delta st <= 0 -> Z.of_nat n <= 1 - delta st ->
  trans_n n st = {| u := 2^(Z.of_nat n); v := 0;
    q := (mod_inv (-f st) (2^(Z.of_nat n)) * g st) mod (2^(Z.of_nat n)); r := 1 |}.
Proof.
  intros Hdelta Hn.
  assert (Hrel_prime : rel_prime (f st) 2).
  { apply rel_prime_mod_rev; try lia.
    assert (Hfodd := odd_f st).
    apply <- Zodd_bool_iff in Hfodd.
    rewrite Zmod_odd, Hfodd.
    apply rel_prime_1. }
  assert (Hgcd : forall x, 0 <= x -> Z.gcd (f st) (2 ^ x) = 1).
  { intros x Hx.
    apply Zgcd_1_rel_prime.
    apply Zpow_facts.rel_prime_Zpower_r; try lia.
    assumption. }
  replace ((mod_inv (-f st) (2 ^ Z.of_nat n)
                       * g st) mod 2 ^ Z.of_nat n)
   with ((-mod_inv (f st) (2 ^ Z.of_nat n)
                       * g st) mod 2 ^ Z.of_nat n).
  (* main goal: prove the matrix form with the rewritten [q] entry *)
  { set (w := _ mod _).
    apply proj1 with ( (2^(Z.of_nat n) | f st * w + g st)
                    /\ (delta (fst (step_n n st)) = Z.of_nat n + delta st)).
    revert w Hn; induction n; intros w Hn;
    [repeat split;[unfold w;rewrite Z.mod_1_r;reflexivity|apply Z.divide_1_l]|].
    destruct IHn as [IHn1 [IHn2 IHn3]];[lia|].
    rewrite <- (trans_n_step_n 1 n), IHn1.
    change (step_n (S n) st) with (step_n (1 + n) st).
    rewrite step_n_app.
    unfold trans_n.
    simpl (fst (_,_)).
    simpl (step_n 1 _).
    set (st' := fst _).
    assert (Hst' := eq_refl st').
    revert Hst'.
    unfold st' at 2.
    assert (Hbound : forall a, 0 <= a mod 2 ^ Z.of_nat n < 2 ^ Z.of_nat n) by
     auto using Z.mod_pos_bound with *.

    assert (Hdivide: (2 ^ Z.of_nat (S n) | f st * w + g st)).
    { apply Z.mod_divide; try lia.
      unfold w.
      rewrite <- Zplus_mod_idemp_l, Zmult_mod_idemp_r, Z.mul_assoc,
              Z.mul_opp_r, Z.mul_opp_l, <-Z.mul_opp_r,
              <- Zmult_mod_idemp_l, mod_inv_mul_r.
      replace (Z.gcd _ _) with 1.
      (* main goal: continue with [gcd = 1] substituted *)
      { rewrite Zmult_mod_idemp_l, Zplus_mod_idemp_l.
        ring_simplify (1 * -g st + g st).
        reflexivity. }
      (* side goal: the gcd is indeed 1 *)
      { symmetry.
        apply Zgcd_1_rel_prime.
        apply Zpow_facts.rel_prime_Zpower_r; try lia.
        assumption. } }
    elim (spec);intros d f' g' Hst'.
    * repeat split.
      + replace (Z.of_nat (S n)) with (1 + Z.of_nat n) by lia.
        rewrite Z.pow_add_r by lia.
        unfold mul; cbn.
        f_equal; try ring.
        ring_simplify.
        unfold w.
        symmetry.
        apply Zdivide_mod_minus.
        - specialize (Hbound ((-mod_inv (f st) (2 ^ Z.of_nat n) * g st))).
          replace (Z.of_nat (S n)) with (1 + Z.of_nat n) by lia.
          rewrite Z.pow_add_r; lia.
        - set (w0 := (-mod_inv (f st) (2 ^ Z.of_nat n) * g st) mod 2 ^ Z.of_nat n) in *.
          apply Z.mod_divide; try lia.
          rewrite <- Zminus_mod_idemp_r.
          replace w0 with (1 * w0) by ring.
          rewrite <- Zmult_mod_idemp_l, <- (Hgcd (Z.of_nat (S n))) by lia.
          rewrite <- mod_inv_mul_l, Zmult_mod_idemp_l, Zminus_mod_idemp_r.
          replace (-mod_inv (f st) (2 ^ Z.of_nat (S n)) * g st
           - mod_inv (f st) (2 ^ Z.of_nat (S n))
           * f st
           * w0) with
           (-mod_inv (f st) (2 ^ Z.of_nat (S n)) *
            (w0 * f st + 1 * g st))
           by ring.
          assert (Htrans_n := trans_n_step n st).
          rewrite <- Hst', IHn1 in Htrans_n.
          unfold fg, scale, ap in Htrans_n.
          simpl in Htrans_n.
          injection Htrans_n; clear Htrans_n.
          intros Hg' Hf'.
          rewrite <- Hg'.
          replace (2 ^ Z.of_nat n * (2 * g')) with (g' * (2 ^ Z.of_nat n * 2^1)) by ring.
          rewrite <- Z.pow_add_r, Z.mul_assoc by lia.
          replace (Z.of_nat n + 1) with (Z.of_nat (S n)) by lia.
          apply Z_mod_mult.
      + assumption.
      + replace (Z.of_nat (S n) + delta st)
        with (1 + (Z.of_nat n + delta st)) by lia.
        rewrite <- IHn3.
        simpl.
        rewrite <- Hst'.
        reflexivity.
    * rewrite <- Hst' in IHn3.
      unfold delta at 1 in IHn3.
      lia.
    * repeat split.
      + replace (Z.of_nat (S n)) with (1 + Z.of_nat n) by lia.
        rewrite Z.pow_add_r by lia.
        unfold mul; cbn.
        f_equal; try ring.
        ring_simplify.
        unfold w.
        symmetry.
        apply Zdivide_mod_minus.
        - specialize (Hbound ((-mod_inv (f st) (2 ^ Z.of_nat n) * g st))).
          replace (Z.of_nat (S n)) with (1 + Z.of_nat n) by lia.
          rewrite Z.pow_add_r; lia.
        - set (w0 := (-mod_inv (f st) (2 ^ Z.of_nat n) * g st) mod 2 ^ Z.of_nat n) in *.
          apply Z.mod_divide; try lia.
          rewrite <- Zminus_mod_idemp_r.
          replace (2 ^ Z.of_nat n + w0) with (1 * (2 ^ Z.of_nat n + w0)) by ring.
          rewrite <- Zmult_mod_idemp_l, <- (Hgcd (Z.of_nat (S n))) by lia.
          rewrite <- mod_inv_mul_l, Zmult_mod_idemp_l, Zminus_mod_idemp_r.
          replace (-mod_inv (f st) (2 ^ Z.of_nat (S n)) * g st
       - mod_inv (f st) (2 ^ Z.of_nat (S n)) * f st
           * (2 ^ Z.of_nat n + w0)) with
           (-mod_inv (f st) (2 ^ Z.of_nat (S n)) *
            (2 ^ Z.of_nat n * f st + 0 * g st + (w0 * f st + 1 * g st)))
           by ring.
          assert (Htrans_n := trans_n_step n st).
          rewrite <- Hst'0, IHn1 in Htrans_n.
          unfold fg, scale, ap in Htrans_n;
          simpl in Htrans_n.
          injection Htrans_n; clear Htrans_n.
          intros Hg' Hf'.
          rewrite <- Hg', <- Hf'.
          replace (2 ^ Z.of_nat n * (2 * f' + 1) + 2 ^ Z.of_nat n * (2 * g' + 1))
             with ((f' + g' + 1) * (2 ^ Z.of_nat n * 2^1)) by ring.
          rewrite <- Z.pow_add_r, Z.mul_assoc by lia.
          replace (Z.of_nat n + 1) with (Z.of_nat (S n)) by lia.
          apply Z_mod_mult.
      + assumption.
      + replace (Z.of_nat (S n) + delta st)
        with (1 + (Z.of_nat n + delta st)) by lia.
        rewrite <- IHn3.
        simpl.
        rewrite <- Hst'0.
        reflexivity. }
  (* side goal: the two [q] entries are eqm modulo [2^n] *)
  { apply Zmult_eqm;[|reflexivity].
    unfold eqm.
    symmetry.
    rewrite <- (Z.mul_1_l (mod_inv _ _)).
    rewrite <- (Hgcd (Z.of_nat n)), <- Zmult_mod_idemp_l, <- mod_inv_mul_l, Zmult_mod_idemp_l, <- Z.mul_assoc by lia.
    rewrite <- (Z.opp_involutive (f st)) at 2.
    rewrite Z.mul_opp_l, Z.mul_opp_r, <- Z.mul_opp_l.
    rewrite <- Zmult_mod_idemp_r, mod_inv_mul_r, Z.gcd_opp_l, Hgcd, Zmult_mod_idemp_r by lia.
    rewrite Z.mul_1_r.
    reflexivity. }
Qed.

(** In the D-phase, the accumulated matrix is the modular-inverse anti-shift form. *)
Lemma trans_ds n st : Zodd (g st) -> 0 < delta st -> 0 < Z.of_nat n <= 1 + delta st ->
  trans_n n st = {| u := 0; v := 2^(Z.of_nat n);
    q := -1; r := (mod_inv (-g st) (2^(Z.of_nat n)) * (-f st)) mod (2^(Z.of_nat n)) |}.
Proof.
  intros Hodd Hdelta [Hn0 Hn].
  destruct n;[lia|].
  rewrite <- Nat.add_1_r, <- trans_n_step_n.
  unfold trans_n at 2; cbn.
  revert Hodd Hdelta Hn.
  elim (spec);cbn;intros d f' g' Hodd Hdelta Hn;
  [elim (Zeven_not_Zodd _ (Zeven_2p _) Hodd)| |lia].
  change (Z.of_nat (S n) <= 1 + Z.pos d) in Hn.
  change (Z.pos_sub 1 d) with (1 - Z.pos d).
  set (dZ := Z.pos d) in *; clearbody dZ; clear d.
  change (mul {| u := 0; v := 2; q := -1; r := 1 |} I)
   with (mul (trans Step.S) {| u := 0; v := 1; q := -1; r := 0 |}).
  rewrite !mul_assoc.
  clear st.
  pose (st0 := {| delta := - dZ;
                  f := 2 * g' + 1;
                  g := - 2 * f' - 1;
                  odd_f := Zodd_2p_plus_1 g' |}).
  set (st1 := Build_State _ _ _ _).
  assert (Hst01 : step st0 = (st1, Step.S)).
  { unfold step.
    assert (Hoddg : Zodd (g st0)) by
     (replace (g st0) with (2*(-f' - 1) + 1) by (cbn;ring); apply Zodd_2p_plus_1).
    destruct Zeven_odd_dec as [Heveng'|Hoddg'];
    [elim (Zodd_not_Zeven _ Hoddg Heveng')|].
    elim (Z.ltb_spec); intros Hd0; cbn in Hd0; try lia.
    simpl (g st0 + f st0).
    replace (-2 * f' - 1 + (2 * g' + 1)) with ((g' - f')*2) by ring.
    rewrite Z_div_mult by lia.
    reflexivity. }
  replace (trans Step.S) with (trans_n 1 st0)
   by (unfold trans_n;cbn;rewrite Hst01;reflexivity).
  replace st1 with (fst (step_n 1 st0)) by (unfold trans_n;cbn;rewrite Hst01;reflexivity).
  rewrite trans_n_step_n, trans_ss; cbn; try lia.
  unfold mul; cbn.
  f_equal; try ring.
  ring_simplify.
  do 1 f_equal.
  ring.
Qed.

End Trans.
