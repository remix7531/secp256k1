(** * theory.modinv.construction.divstep: the variable-time divstep state machine --
    [Step] / [State] / [step] / [step_n], its eta/f/g bounds, the fixed point
    and gcd invariant, and the bridge ([Translate_divsteps]) to the vendored
    safegcd-bounds library. *)
(** Copyright (C) 2026 remix7531
    Ported from BlockstreamResearch/simplicity Coq/C/divstep.v
    (commit c1dddedd), Copyright (c) 2018 Blockstream, originally MIT.
    Upstream notice reproduced in proof/README.md.
    SPDX-License-Identifier: MIT *)

(** The transition-matrix algebra lives in [divstep_trans]; the constant-time
    (zeta) machine in [divstep_zeta].

    Adapted for Rocq 9.0 / VST 2.16. *)

Require Import ZArith.
Require Import ZArith.Znumtheory.
Require Import ZArith.Zpow_facts.
Require Import Lia.
Require Import List.

Require Import secp256k1.theory.modinv.divsteps.def.
Require Import secp256k1.theory.integers.extra_math.
Require Import secp256k1.theory.modinv.construction.inverse.

Open Scope list_scope.
Open Scope Z_scope.
Arguments Z.add !x !y.
Arguments Z.sub !m !n.
Arguments Z.mul !x !y.

(* ================================================================= *)
(** ** Shared helpers -- [Zodd_irr] / [odd_divisor] / [divide_halving_massage]. *)

(** Proof irrelevance for [Zodd]: any two [Zodd z] proofs are equal. *)
Definition Zodd_irr z (Hz1 Hz2 : Zodd z) : Hz1 = Hz2.
Proof.
  revert Hz1 Hz2.
  destruct z as [|p|p]; try destruct p; try contradiction; intros [] []; reflexivity.
Defined.

(** Any divisor of an odd number is odd.  Used by the gcd-invariance proofs
    ([gcd] here, [zgcd] in [divstep_zeta]) to show the running gcd stays odd. *)
Lemma odd_divisor a d : (d | a) -> Zodd a -> Z.odd d = true.
Proof.
  intros [z ->] Ha.
  apply Zodd_bool_iff in Ha.
  rewrite Z.odd_mul, Bool.andb_true_iff in Ha.
  destruct Ha as [_ Hd].
  exact Hd.
Qed.

(** The recurring "[2^n] divides [g], so peel one power off the mod/div" massage
    on a hypothesis [H] carrying a [2^(Z.of_nat n)]-divisibility fact.  Shared by
    the H-shift lemmas [g_hs] / [f_hs] / [eta_hs] (and [trans_hs] / [ztrans_hs]). *)
Ltac divide_halving_massage H n :=
  apply Zdivide_mod in H;
  apply (f_equal (fun x => x / 2 ^ (Z.of_nat n))) in H;
  rewrite Z.mul_comm, Z.rem_mul_r, Z.mul_comm, Z_div_plus_full, Z.mod_div, Z.add_0_l in H by lia.

(* ================================================================= *)
(** ** Divstep state machine -- [Step] / [State] / [step] / [step_n]. *)

(** The three divstep transition kinds. *)
Module Step.

Inductive Step : Set :=
| D : Step
| S : Step
| H : Step.

End Step.
Definition Step := Step.Step.

(** The [delta] increment per step. *)
Definition INC : Z := 1.

(** Divstep state: [delta], the pair [(f, g)], and oddness of [f]. *)
Record State : Set :=
 { delta : Z;
   f : Z;
   g : Z;
   odd_f : Zodd f
 }.

(** [eta] is the negated [delta]. *)
Definition eta (st : State) := Z.opp (delta st).

(** Initial state: [delta = 1], inputs [f], [g], proof [odd_f]. *)
Definition init f g odd_f :=
{| delta := 1;
   f := f;
   g := g;
   odd_f := odd_f
 |}.

(** One divstep: branches on the parity of [g] and the sign of [delta]. *)
Definition step (st : State) : State * Step :=
match Zeven_odd_dec (g st) with
| left _ => ({| delta := INC + delta st;
                f := f st;
                g := g st / 2;
                odd_f := odd_f st
              |}
            , Step.H)
| right odd_g =>
    if (0 <? delta st)%Z
    then ({| delta := INC - delta st;
             f := g st;
             g := (g st - f st) / 2;
             odd_f := odd_g
           |}
         , Step.D)
    else ({| delta := INC + delta st;
             f := f st;
             g := (g st + f st) / 2;
             odd_f := odd_f st
           |}
         , Step.S)
end.

(** [n]-fold divstep; the last step is first in the list to facilitate
    matrix multiplication. *)
Fixpoint step_n (n : nat) : State -> State * list Step  :=
match n with
| O => fun st => (st, nil)
| (S n) => fun st =>
    let (st0, xs) := step_n n st in
    let (st1, x) := step st0 in
    (st1, x :: xs)
end.

(* ----------------------------------------------------------------- *)
(** *** Step specification. *)

(** Characterization of [step] by the three transition kinds. *)
Inductive Spec : State -> (State * Step) -> Set :=
| Spec_h : forall d f' g', Spec {| delta := d; f := 2*f'+1; g := 2*g'; odd_f := Zodd_2p_plus_1 f' |}
                               ({| delta := INC + d; f := 2*f'+1; g := g'; odd_f := Zodd_2p_plus_1 f' |}, Step.H)
| Spec_d : forall d f' g', Spec {| delta := Z.pos d; f := 2*f'+1; g := 2*g'+1; odd_f := Zodd_2p_plus_1 f' |}
                               ({| delta := INC - Z.pos d; f := 2*g'+1; g := g' - f'; odd_f := Zodd_2p_plus_1 g' |}, Step.D)
| Spec_s : forall d f' g', (d <= 0) ->
                          Spec {| delta := d; f := 2*f'+1; g := 2*g'+1; odd_f := Zodd_2p_plus_1 f' |}
                               ({| delta := INC + d; f := 2*f'+1; g := g' + f' + 1; odd_f := Zodd_2p_plus_1 f' |}, Step.S).

(** [step st] satisfies its [Spec]. *)
Lemma spec st : Spec st (step st).
Proof.
  destruct st as [d0 f0 g0 Hf0].
  unfold step; cbn -[Z.div].
  destruct (Zeven_odd_dec g0) as [Hg0|Hg0].
  generalize Hf0.
  apply Zodd_bool_iff in Hf0.
  rewrite (Zdiv2_odd_eqn f0), Hf0.
  rewrite (Zeven_div2 g0) by auto.
  replace (2 * Z.div2 g0 / 2) with (Z.div2 g0) by (rewrite Z.mul_comm, Z.div_mul by lia; reflexivity).
  intros Hf0'.
  replace Hf0' with (Zodd_2p_plus_1 (Z.div2 f0)) by apply Zodd_irr.
  apply Spec_h.
  generalize Hf0 Hg0.
  apply Zodd_bool_iff in Hf0.
  apply Zodd_bool_iff in Hg0.
  rewrite (Zdiv2_odd_eqn f0), Hf0.
  rewrite (Zdiv2_odd_eqn g0), Hg0.
  destruct (0 <? d0) eqn:Hd.
  destruct d0; try solve [cbn in Hd; congruence].
  replace (2 * Z.div2 g0 + 1 - (2 * Z.div2 f0 + 1)) with ((Z.div2 g0 - Z.div2 f0) * 2) by ring.
  rewrite Z.div_mul by lia.
  intros Hf0' Hg0'.
  replace Hf0' with (Zodd_2p_plus_1 (Z.div2 f0)) by apply Zodd_irr.
  replace Hg0' with (Zodd_2p_plus_1 (Z.div2 g0)) by apply Zodd_irr.
  apply Spec_d.
  replace (2 * Z.div2 g0 + 1 + (2 * Z.div2 f0 + 1)) with ((Z.div2 g0 + Z.div2 f0 + 1) * 2) by ring.
  rewrite Z.div_mul by lia.
  intros Hf0' _.
  replace Hf0' with (Zodd_2p_plus_1 (Z.div2 f0)) by apply Zodd_irr.
  apply Spec_s.
  lia.
Qed.

(* ================================================================= *)
(** ** eta / f / g evolution lemmas -- bounds across [step_n]. *)

(** [eta] drifts by at most [n] over [n] steps. *)
Lemma eta_bounds b n st : -b <= eta st < b ->
  -b - Z.of_nat n <= eta (fst (step_n n st)) < b + Z.of_nat n.
Proof.
  induction n; simpl; [lia|].
  destruct (step_n n st).
  rewrite Zpos_P_of_succ_nat.
  revert IHn.
  elim (spec s); intros d f' g'; try generalize (Z.pos d); unfold eta; cbn; try lia.
Qed.

(** When [g] is divisible by [2^n], [g] is right-shifted by [n] across [n] steps. *)
Lemma g_hs n st : (2^(Z.of_nat n) | g st) ->
  g (fst (step_n n st)) = g st / 2^(Z.of_nat n).
Proof.
  induction n;[intros;rewrite Z.div_1_r; reflexivity|].
  rewrite Nat2Z.inj_succ, Z.pow_succ_r by lia.
  simpl (fst _).
  destruct (step_n n st).
  intros Hg.
  assert (Hdivide : (2 ^ Z.of_nat n | g st)) by (etransitivity;[|apply Hg]; auto with *).
  divide_halving_massage Hg n.
  rewrite <- IHn in Hg by assumption.
  destruct (spec s);
  simpl in Hg;
  try solve [rewrite Zmod_odd, Z.add_comm, Z.odd_add_mul_2 in Hg;
             discriminate].
  simpl (g _).
  simpl (g _) in IHn.
  apply Z.mul_cancel_l with 2; try lia.
  rewrite !(Z.mul_comm 2), <- Zdiv_Zdiv by lia.
  rewrite <- IHn by assumption.
  rewrite !(Z.mul_comm 2), Z.div_mul; lia.
Qed.

(** When [g] is divisible by [2^n], [f] is unchanged across [n] steps. *)
Lemma f_hs n st : (2^(Z.of_nat n) | g st) ->
  f (fst (step_n n st)) = f st.
Proof.
  induction n;[intros; reflexivity|].
  rewrite Nat2Z.inj_succ, Z.pow_succ_r by lia.
  intros Hg.
  simpl (fst _).
  assert (Hg' : (2 ^ Z.of_nat n | g st)) by (etransitivity;[|apply Hg]; auto with *).
  divide_halving_massage Hg n.
  rewrite <- g_hs in Hg by assumption.
  destruct (step_n n st).
  rewrite <- IHn by assumption.
  destruct (spec s);
  simpl in Hg;
  try solve [rewrite Zmod_odd, Z.add_comm, Z.odd_add_mul_2 in Hg;
             discriminate].
  reflexivity.
Qed.

(** When [g] is divisible by [2^n], [eta] decreases by [n] across [n] steps. *)
Lemma eta_hs n st : (2^(Z.of_nat n) | g st) ->
  eta (fst (step_n n st)) = eta st - (Z.of_nat n).
Proof.
  induction n;[intros;cbn;ring|].
  rewrite Nat2Z.inj_succ, Z.pow_succ_r by lia.
  intros Hg.
  simpl (fst _).
  assert (Hg' : (2 ^ Z.of_nat n | g st)) by (etransitivity;[|apply Hg]; auto with *).
  divide_halving_massage Hg n.
  rewrite <- g_hs in Hg by assumption.
  destruct (step_n n st).
  replace (eta st - _) with (eta st - (Z.of_nat n) - 1) by lia.
  rewrite <- IHn by assumption.
  destruct (spec s);
  simpl in Hg;
  try solve [rewrite Zmod_odd, Z.add_comm, Z.odd_add_mul_2 in Hg;
             discriminate].
  unfold eta, INC.
  simpl.
  ring.
Qed.

(** In the S-phase ([eta >= 0]), [eta] decreases by [n] across [n] steps. *)
Lemma eta_ss n st : 0 <= eta st ->
       Z.of_nat n <= 1 + eta st ->
       eta (fst (step_n n st)) = eta st - Z.of_nat n.
Proof.
  induction n;[intros;cbn;ring|].
  rewrite Nat2Z.inj_succ, <- Z.add_1_l.
  intros Heta Hn.
  simpl (fst _).
  destruct (step_n n st) as [s l].
  transitivity (eta st - Z.of_nat n - 1);[|ring].
  assert (Hs : eta (fst (s, l)) = eta st - Z.of_nat n) by (apply IHn; lia).
  rewrite <- Hs.
  unfold eta in *.
  destruct (spec s); cbn; try ring.
  cbn in Hs.
  lia.
Qed.

(* ----------------------------------------------------------------- *)
(** *** [step_n] composition. *)

(** [step_n] splits as a concatenation: [step_n (n + m) = step_n n . step_n m]. *)
Lemma step_n_app (n m : nat) st : step_n (n + m) st = let st1 := step_n m st in
  (fst (step_n n (fst st1)), snd (step_n n (fst st1)) ++ snd st1).
Proof.
  induction n;[destruct (step_n _ _);reflexivity|].
  cbn.
  rewrite IHn.
  cbn.
  destruct (step_n n _).
  cbn.
  destruct (step s).
  reflexivity.
Qed.

(** State projection of the [step_n] split. *)
Lemma step_n_app_fst (n m : nat) st : fst (step_n (n + m) st) = fst (step_n n (fst (step_n m st))).
Proof.
  rewrite step_n_app.
  reflexivity.
Qed.

(** Step-list projection of the [step_n] split. *)
Lemma step_n_app_snd (n m : nat) st : snd (step_n (n + m) st) =
  snd (step_n n (fst (step_n m st))) ++ snd (step_n m st).
Proof.
  rewrite step_n_app.
  reflexivity.
Qed.

(** In the D-phase ([g] odd, [eta < 0]), [eta] flips and decreases over [n] steps. *)
Lemma eta_ds n st : Zodd (g st) -> eta st < 0 ->
       0 < Z.of_nat n <= 1 - eta st ->
       eta (fst (step_n n st)) = -eta st - Z.of_nat n.
Proof.
  intros Hodd Heta Hn.
  destruct n;[lia|].
  rewrite <- Nat.add_1_r.
  rewrite step_n_app_fst.
  simpl (step_n 1 st).
  destruct (spec st);[elim (Zodd_not_Zeven _ Hodd); apply Zeven_2p| |unfold eta in *;cbn in *;lia].
  rewrite eta_ss; unfold eta in *; cbn in *; change (Z.pos_sub 1 d) with (1 - Z.pos d); try lia.
  change (0 < Z.of_nat (S n) <= 1 - -(Z.pos d)) in Hn.
  lia.
Qed.

(** Two states congruent mod [2^n] in [f], [g] (and equal [delta]) take the
    same [n]-step sequence and end with equal [delta]. *)
Lemma step_n_mod n st1 st2 :
  eqm (2^Z.of_nat n) (f st1) (f st2) ->
  eqm (2^Z.of_nat n) (g st1) (g st2) ->
  delta st1 = delta st2 ->
  delta (fst (step_n n st1)) = delta (fst (step_n n st2)) /\
  snd (step_n n st1) = snd (step_n n st2).
Proof.
  revert st1 st2.
  induction n;[simpl;repeat split;congruence|].
  intros st1 st2 Hf Hg Hdelta.
  replace (S n) with (n + 1)%nat by lia.
  rewrite !step_n_app_fst, !step_n_app_snd.
  simpl (step_n 1 st1); simpl (step_n 1 st2).
  unfold step; rewrite Hdelta.
  assert (Hdiv2 : forall x y, eqm (2 ^ Z.of_nat (S n)) x y -> eqm (2 ^ Z.of_nat n) (x / 2) (y / 2)).
  { intros x y.
    unfold eqm.
    rewrite <-!Z.land_ones, <-!(Z.shiftr_div_pow2 _ 1) by lia.
    replace (Z.of_nat n) with (Z.of_nat (S n) - 1) by lia.
    rewrite <-!extra_math.Z_shiftr_ones, <-!Z.shiftr_land by lia.
    congruence. }
  destruct (Zeven_odd_dec (g st1)); destruct (Zeven_odd_dec (g st2));
  try solve
  [exfalso;
  rewrite <-?Zeven_bool_iff, <-?Zodd_bool_iff, ?Zeven_mod, ?Zodd_mod in *;
  apply Z.eqb_eq in z, z0;
  apply (extra_math.eqm_2_pow_le 1) in Hg; try lia;
  change (2^1) with 2 in *;
  rewrite Hg in z;
  congruence
  ];[|destruct (0 <? delta st2)];cbn;
    set (st1' := Build_State _ _ _ _);
    set (st2' := Build_State _ _ _ _);
    destruct (IHn st1' st2');
    try solve [cbn; lia|split; congruence].
  * eapply extra_math.eqm_2_pow_le;[|apply Hf]; lia.
  * apply Hdiv2; apply Hg.
  * eapply extra_math.eqm_2_pow_le;[|apply Hg]; lia.
  * apply Hdiv2; apply Zminus_eqm; assumption.
  * eapply extra_math.eqm_2_pow_le;[|apply Hf]; lia.
  * apply Hdiv2; apply Zplus_eqm; assumption.
Qed.

(* ================================================================= *)
(** ** Magnitude bounds -- [f_step_bounds] / [g_step_bounds] / [fg_bounds]. *)

(** [f] after one step is bounded by [max |f| |g|]. *)
Lemma f_step_bounds st : Z.abs (f (fst (step st))) <= Z.max (Z.abs (f st)) (Z.abs (g st)).
Proof.
  destruct (spec st); cbn;lia.
Qed.

(** Twice [g] after one step is bounded by [|f| + |g|]. *)
Lemma g_step_bounds st : 2 * Z.abs (g (fst (step st))) <= Z.abs (f st) + Z.abs (g st).
Proof.
  destruct (spec st); cbn;lia.
Qed.

(** Both [f] and [g] stay bounded by [max |f| |g|] across [n] steps. *)
Lemma fg_bounds st n :
 Z.abs (f (fst (step_n n st))) <= Z.max (Z.abs (f st)) (Z.abs (g st)) /\
 Z.abs (g (fst (step_n n st))) <= Z.max (Z.abs (f st)) (Z.abs (g st)).
Proof.
  induction n;[cbn; lia|].
  cbn.
  assert (Hf := f_step_bounds (fst (step_n n st))).
  assert (Hg := g_step_bounds (fst (step_n n st))).
  destruct (step_n n st) as [st' xs].
  cbn in *.
  destruct (step st') as [st'' xs'].
  cbn in *.
  lia.
Qed.

(** Strict variant: when [|g| < |f|], [g] stays strictly below [max |f| |g|]. *)
Lemma fg_bounds_strict st n :
 Z.abs (g st) < Z.abs (f st) ->
 Z.abs (f (fst (step_n n st))) <= Z.max (Z.abs (f st)) (Z.abs (g st)) /\
 Z.abs (g (fst (step_n n st))) < Z.max (Z.abs (f st)) (Z.abs (g st)).
Proof.
  induction n;[cbn; lia|].
  cbn.
  assert (Hf := f_step_bounds (fst (step_n n st))).
  assert (Hg := g_step_bounds (fst (step_n n st))).
  destruct (step_n n st) as [st' xs].
  cbn in *.
  destruct (step st') as [st'' xs'].
  cbn in *.
  lia.
Qed.

(* ================================================================= *)
(** ** Fixed point and gcd -- [fixed] / [fixed_f] / [fixed_g] / [gcd]. *)

(** Once [g = 0] the state is fixed: [f] is preserved and [g] stays [0]. *)
Lemma fixed st n : g st = 0 ->
 f (fst (step_n n st)) = f st /\ g (fst (step_n n st)) = 0.
Proof.
  intros Hg.
  induction n;[auto|].
  cbn.
  destruct (step_n n st) as [[eta f g Hf] l].
  unfold step.
  cbn in *.
  destruct IHn as [-> ->].
  cbn.
  auto.
Qed.

(** [f] projection of [fixed]. *)
Lemma fixed_f st n : g st = 0 ->
 f (fst (step_n n st)) = f st.
Proof.
  intros Hg.
  destruct (fixed st n Hg).
  assumption.
Qed.

(** [g] projection of [fixed]. *)
Lemma fixed_g st n : g st = 0 ->
 g (fst (step_n n st)) = 0.
Proof.
  intros Hg.
  destruct (fixed st n Hg).
  assumption.
Qed.

(** The gcd of [(f, g)] is invariant across [n] steps. *)
Lemma gcd st d n : Zis_gcd (f st) (g st) d ->
 Zis_gcd (f (fst (step_n n st))) (g (fst (step_n n st))) d.
Proof.
  intros Hgcd.
  induction n;[auto|].
  cbn.
  destruct (step_n n st) as [st0 l].
  cbn in IHn.
  destruct (spec st0);cbn in *;
    revert IHn;
    apply Zis_gcd_ind;
    intros Hd1 Hd2 Hdx;
    apply Zis_gcd_intro; try assumption.
  * assert (Hodd : Z.odd d = true) by (exact (odd_divisor _ _ Hd1 (Zodd_2p_plus_1 f'))).
    eapply Gauss;[apply Hd2|].
    apply rel_prime_mod_rev;[lia|].
    rewrite Zmod_odd, Hodd.
    apply rel_prime_1.
  * intros x Hxf Hxg.
    apply Hdx; try assumption.
    auto with *.
  * assert (Hodd : Z.odd d = true) by (exact (odd_divisor _ _ Hd1 (Zodd_2p_plus_1 f'))).
    apply Gauss with 2.
    + replace (2 * (g' - f')) with ((2 * g' + 1) - (2 * f' + 1)) by ring.
      apply Z.divide_sub_r; assumption.
    + apply rel_prime_mod_rev;[lia|].
      rewrite Zmod_odd, Hodd.
      apply rel_prime_1.
  * intros x Hxf Hxg.
    apply Hdx; try assumption.
    replace (2 * f' + 1) with ((2 * g' + 1) - (2*(g' - f'))) by ring.
    apply Z.divide_sub_r; try assumption.
    auto with *.
  * assert (Hodd : Z.odd d = true) by (exact (odd_divisor _ _ Hd1 (Zodd_2p_plus_1 f'))).
    apply Gauss with 2.
    + replace (2 * (g' + f' + 1)) with ((2 * g' + 1) + (2 * f' + 1)) by ring.
      apply Z.divide_add_r; assumption.
    + apply rel_prime_mod_rev;[lia|].
      rewrite Zmod_odd, Hodd.
      apply rel_prime_1.
  * intros x Hxf Hxg.
    apply Hdx; try assumption.
    replace (2 * g' + 1) with ((2*(g' + f' + 1)) - (2 * f' + 1)) by ring.
    apply Z.divide_sub_r; try assumption.
    auto with *.
Qed.

(* ================================================================= *)
(** ** Bridge to safegcd-bounds -- [Translate_divsteps]. *)

(** [delta], [f], [g] of this model agree with the vendored [divsteps] library
    after [n] / [N.of_nat n] steps. *)
Lemma Translate_divsteps n fi gi (Hf : Zodd fi) :
 delta (fst (step_n n (init fi gi Hf))) = divsteps.delta (N.iter (N.of_nat n) divsteps.step (divsteps.init fi gi)) /\
 f (fst (step_n n (init fi gi Hf))) = divsteps.f (N.iter (N.of_nat n) divsteps.step (divsteps.init fi gi)) /\
 g (fst (step_n n (init fi gi Hf))) = divsteps.g (N.iter (N.of_nat n) divsteps.step (divsteps.init fi gi)).
Proof.
  induction n;[cbn;auto|].
  destruct IHn as [IHdelta [IHf IHg]].
  rewrite Nnat.Nat2N.inj_succ, N.iter_succ.
  destruct (N.iter (N.of_nat n) divsteps.step (divsteps.init fi gi)).
  simpl.
  destruct (step_n n (init fi gi Hf)) as [st0 l].
  simpl in *.
  subst delta0 f0 g0.
  destruct (spec st0);
  unfold divsteps.step; cbn -[Z.div].
  * rewrite Z.even_mul; cbn -[Z.div].
    rewrite (Z.mul_comm 2 g'), Z.div_mul; lia.
  * rewrite Z.add_comm, Z.even_add_mul_2; cbn -[Z.div].
    repeat (split;try reflexivity).
    replace (1 + 2 * g' - (2 * f' + 1)) with ((g' - f') * 2) by ring.
    rewrite Z.div_mul; lia.
  * rewrite (Z.add_comm _ 1), Z.even_add_mul_2; cbn -[Z.div].
    elim Z.ltb_spec;[lia|intros _];cbn -[Z.div].
    repeat (split;try reflexivity).
    replace (1 + 2 * g' + (2 * f' + 1)) with ((g' + f' + 1) * 2) by ring.
    rewrite Z.div_mul; lia.
Qed.

(** [g]-only projection of [Translate_divsteps]. *)
Lemma Translate_divsteps_g n fi gi (Hf : Zodd fi) :
 g (fst (step_n n (init fi gi Hf))) = divsteps.g (N.iter (N.of_nat n) divsteps.step (divsteps.init fi gi)).
Proof.
  destruct (Translate_divsteps n fi gi Hf).
  tauto.
Qed.
