(** * theory.modinv.construction.posdivstep: the positive-divstep state machine
    with Jacobi tracking -- [State] / [pstep] / [pstep_n], the sign-flip bits
    ([hflip] / [sflip] / [pflip]), the eta / f / g / jac evolution lemmas, the
    positivity bounds and the gcd invariant. *)
(** Copyright (C) 2026 remix7531
    Adapted from BlockstreamResearch/simplicity Coq/C/divstep.v
    (commit c1dddedd), Copyright (c) 2018 Blockstream, originally MIT.
    Upstream notice reproduced in proof/README.md.
    SPDX-License-Identifier: MIT *)

(** This is the model of the C helper [secp256k1_modinv64_posdivsteps_62_var].
    It runs the same three-branch alphabet as [divstep] -- the alphabet
    [divstep.Step] is reused here, not redefined -- with two changes:

    - the D branch ADDS [f] to [g] instead of subtracting it, so [f] and [g]
      never leave [0 <= . <= M] (hence "positive" divsteps), and
    - every state carries the running Jacobi-symbol sign bit [jac], flipped
      per step by [pflip].

    The transition-matrix algebra lives in [posdivstep_trans].

    Written for Rocq 9.0 / VST 2.16. *)

Require Import ZArith.
Require Import ZArith.Znumtheory.
Require Import ZArith.Zpow_facts.
Require Import Lia.
Require Import List.

Require Import secp256k1.theory.integers.extra_math.
Require secp256k1.theory.modinv.construction.divstep.

Open Scope list_scope.
Open Scope Z_scope.
Arguments Z.add !x !y.
Arguments Z.sub !m !n.
Arguments Z.mul !x !y.

(* ================================================================= *)
(** ** Sign-flip bits -- [hflip] / [sflip] and their congruence transport. *)

(** The halving flip.  With [f] odd, halving [g] rescales the Jacobi symbol
    [(g | f)] by [(2 | f)], which is [-1] exactly when [f mod 8] is [3] or
    [5].  This is the bit the C extracts as [((f >> 1) ^ (f >> 2)) & 1]. *)
Definition hflip (x : Z) : bool := (x mod 8 =? 3) || (x mod 8 =? 5).

(** The swap flip.  With [a] and [b] both odd, exchanging them rescales
    [(b | a)] by the reciprocity sign, which is [-1] exactly when both are
    [3 mod 4].  This is the bit the C extracts as [((f & g) >> 1) & 1]. *)
Definition sflip (a b : Z) : bool := (a mod 4 =? 3) && (b mod 4 =? 3).

Arguments hflip : simpl never.
Arguments sflip : simpl never.

(** Congruent-mod-[8] arguments give the same halving flip. *)
Lemma hflip_eqm a b : eqm 8 a b -> hflip a = hflip b.
Proof.
  unfold eqm, hflip.
  intros Hab.
  rewrite Hab.
  reflexivity.
Qed.

(** Congruent-mod-[4] arguments give the same swap flip. *)
Lemma sflip_eqm a1 a2 b1 b2 : eqm 4 a1 a2 -> eqm 4 b1 b2 -> sflip a1 b1 = sflip a2 b2.
Proof.
  unfold eqm, sflip.
  intros Ha Hb.
  rewrite Ha, Hb.
  reflexivity.
Qed.

(** Parity is pinned mod [2].  Used to align the [g]-parity branch of two runs
    in [pstep_mod]. *)
Lemma odd_eqm a b : eqm 2 a b -> Z.odd a = Z.odd b.
Proof.
  unfold eqm.
  rewrite !Zmod_odd.
  intros Hab.
  destruct (Z.odd a), (Z.odd b); congruence.
Qed.

(* ================================================================= *)
(** ** Positive-divstep state machine -- [State] / [pstep] / [pstep_n]. *)

(** Positive-divstep state: [delta], the pair [(f, g)], the running Jacobi
    sign bit [jac], and oddness of [f]. *)
Record State : Set :=
 { delta : Z;
   f : Z;
   g : Z;
   jac : bool;
   odd_f : Zodd f
 }.

(** [eta] is the negated [delta]; the C tracks [eta], this model tracks
    [delta], so the C's [eta < 0] swap test is [0 < delta] here. *)
Definition eta (st : State) := Z.opp (delta st).

(** Initial state: [delta = 1], inputs [f], [g], sign bit [j], proof [odd_f]. *)
Definition init f g j odd_f :=
{| delta := 1;
   f := f;
   g := g;
   jac := j;
   odd_f := odd_f
 |}.

(** The bit XORed into [jac] by one [pstep].  Each branch performs exactly one
    halving, whose flip is read off the POST-branch [f] ([g st] on the D
    branch, where [f] and [g] are exchanged); the D branch additionally pays
    the reciprocity flip for the exchange itself. *)
Definition pflip (st : State) : bool :=
match Zeven_odd_dec (g st) with
| left _ => hflip (f st)
| right _ =>
    if (0 <? delta st)%Z
    then xorb (sflip (f st) (g st)) (hflip (g st))
    else hflip (f st)
end.

(** One positive divstep: branches on the parity of [g] and the sign of
    [delta].  Unlike [divstep.step], the D branch adds [f] to [g] rather than
    subtracting it. *)
Definition pstep (st : State) : State * divstep.Step :=
match Zeven_odd_dec (g st) with
| left _ => ({| delta := 1 + delta st;
                f := f st;
                g := g st / 2;
                jac := xorb (jac st) (hflip (f st));
                odd_f := odd_f st
              |}
            , divstep.Step.H)
| right odd_g =>
    if (0 <? delta st)%Z
    then ({| delta := 1 - delta st;
             f := g st;
             g := (g st + f st) / 2;
             jac := xorb (jac st) (xorb (sflip (f st) (g st)) (hflip (g st)));
             odd_f := odd_g
           |}
         , divstep.Step.D)
    else ({| delta := 1 + delta st;
             f := f st;
             g := (g st + f st) / 2;
             jac := xorb (jac st) (hflip (f st));
             odd_f := odd_f st
           |}
         , divstep.Step.S)
end.

(** [n]-fold positive divstep; the last step is first in the list to
    facilitate matrix multiplication. *)
Fixpoint pstep_n (n : nat) : State -> State * list divstep.Step :=
match n with
| O => fun st => (st, nil)
| Datatypes.S n => fun st =>
    let (st0, xs) := pstep_n n st in
    let (st1, x) := pstep st0 in
    (st1, x :: xs)
end.

(** One step of [pstep_n] peeled off the OUTSIDE (the newest step). *)
Lemma pstep_n_S n st : pstep_n (Datatypes.S n) st =
  (fst (pstep (fst (pstep_n n st))), snd (pstep (fst (pstep_n n st))) :: snd (pstep_n n st)).
Proof.
  cbn.
  destruct (pstep_n n st) as [st0 xs].
  cbn.
  destruct (pstep st0) as [st1 x].
  reflexivity.
Qed.

(** State projection of [pstep_n_S]. *)
Lemma pstep_n_S_fst n st : fst (pstep_n (Datatypes.S n) st) = fst (pstep (fst (pstep_n n st))).
Proof.
  rewrite pstep_n_S.
  reflexivity.
Qed.

(** [pstep_n 1] is [pstep]. *)
Lemma pstep_n_1 st : pstep_n 1 st = (fst (pstep st), snd (pstep st) :: nil).
Proof.
  cbn.
  destruct (pstep st) as [st1 x].
  reflexivity.
Qed.

(* ----------------------------------------------------------------- *)
(** *** Step specification. *)

(** Characterization of [pstep] by the three transition kinds.  Both the D and
    the S branch produce [g' = g' + f' + 1]; only [f'] and [delta'] tell them
    apart. *)
Inductive Spec : State -> (State * divstep.Step) -> Set :=
| Spec_h : forall d f' g' j,
    Spec {| delta := d; f := 2*f'+1; g := 2*g'; jac := j; odd_f := Zodd_2p_plus_1 f' |}
         ({| delta := 1 + d; f := 2*f'+1; g := g';
             jac := xorb j (hflip (2*f'+1)); odd_f := Zodd_2p_plus_1 f' |}, divstep.Step.H)
| Spec_d : forall d f' g' j,
    Spec {| delta := Z.pos d; f := 2*f'+1; g := 2*g'+1; jac := j; odd_f := Zodd_2p_plus_1 f' |}
         ({| delta := 1 - Z.pos d; f := 2*g'+1; g := g' + f' + 1;
             jac := xorb j (xorb (sflip (2*f'+1) (2*g'+1)) (hflip (2*g'+1)));
             odd_f := Zodd_2p_plus_1 g' |}, divstep.Step.D)
| Spec_s : forall d f' g' j, (d <= 0) ->
    Spec {| delta := d; f := 2*f'+1; g := 2*g'+1; jac := j; odd_f := Zodd_2p_plus_1 f' |}
         ({| delta := 1 + d; f := 2*f'+1; g := g' + f' + 1;
             jac := xorb j (hflip (2*f'+1)); odd_f := Zodd_2p_plus_1 f' |}, divstep.Step.S).

(** [pstep st] satisfies its [Spec]. *)
Lemma spec st : Spec st (pstep st).
Proof.
  destruct st as [d0 f0 g0 j0 Hf0].
  unfold pstep; cbn -[Z.div].
  destruct (Zeven_odd_dec g0) as [Hg0|Hg0].
  generalize Hf0.
  apply Zodd_bool_iff in Hf0.
  rewrite (Zdiv2_odd_eqn f0), Hf0.
  rewrite (Zeven_div2 g0) by auto.
  replace (2 * Z.div2 g0 / 2) with (Z.div2 g0) by (rewrite Z.mul_comm, Z.div_mul by lia; reflexivity).
  intros Hf0'.
  replace Hf0' with (Zodd_2p_plus_1 (Z.div2 f0)) by apply divstep.Zodd_irr.
  apply Spec_h.
  generalize Hf0 Hg0.
  apply Zodd_bool_iff in Hf0.
  apply Zodd_bool_iff in Hg0.
  rewrite (Zdiv2_odd_eqn f0), Hf0.
  rewrite (Zdiv2_odd_eqn g0), Hg0.
  destruct (0 <? d0) eqn:Hd.
  destruct d0; try solve [cbn in Hd; congruence].
  replace (2 * Z.div2 g0 + 1 + (2 * Z.div2 f0 + 1)) with ((Z.div2 g0 + Z.div2 f0 + 1) * 2) by ring.
  rewrite Z.div_mul by lia.
  intros Hf0' Hg0'.
  replace Hf0' with (Zodd_2p_plus_1 (Z.div2 f0)) by apply divstep.Zodd_irr.
  replace Hg0' with (Zodd_2p_plus_1 (Z.div2 g0)) by apply divstep.Zodd_irr.
  apply Spec_d.
  replace (2 * Z.div2 g0 + 1 + (2 * Z.div2 f0 + 1)) with ((Z.div2 g0 + Z.div2 f0 + 1) * 2) by ring.
  rewrite Z.div_mul by lia.
  intros Hf0' _.
  replace Hf0' with (Zodd_2p_plus_1 (Z.div2 f0)) by apply divstep.Zodd_irr.
  apply Spec_s.
  lia.
Qed.

(** The [jac] bit advances by XOR with [pflip], on every branch. *)
Lemma pstep_jac st : jac (fst (pstep st)) = xorb (jac st) (pflip st).
Proof.
  unfold pstep, pflip.
  destruct (Zeven_odd_dec (g st)) as [Hg|Hg];[reflexivity|].
  destruct (0 <? delta st);reflexivity.
Qed.

(** [f] is odd in every reachable state; the [odd_f] field, as a lemma. *)
Lemma pstep_odd_f st : Zodd (f (fst (pstep st))).
Proof.
  exact (odd_f (fst (pstep st))).
Qed.

(** On an even [g] the flip is the plain halving flip of [f]. *)
Lemma pflip_even st : Zeven (g st) -> pflip st = hflip (f st).
Proof.
  intros He.
  unfold pflip.
  destruct (Zeven_odd_dec (g st)) as [_|Ho];[reflexivity|].
  elim (Zodd_not_Zeven _ Ho He).
Qed.

(* ================================================================= *)
(** ** eta / f / g / jac evolution -- bounds across [pstep_n]. *)

(** [eta] drifts by at most [n] over [n] steps. *)
Lemma eta_bounds b n st : -b <= eta st < b ->
  -b - Z.of_nat n <= eta (fst (pstep_n n st)) < b + Z.of_nat n.
Proof.
  induction n; simpl; [lia|].
  destruct (pstep_n n st).
  rewrite Zpos_P_of_succ_nat.
  revert IHn.
  elim (spec s); intros d f' g' j; try generalize (Z.pos d); unfold eta; cbn; try lia.
Qed.

(** When [g] is divisible by [2^n], [g] is right-shifted by [n] across [n] steps. *)
Lemma g_hs n st : (2^(Z.of_nat n) | g st) ->
  g (fst (pstep_n n st)) = g st / 2^(Z.of_nat n).
Proof.
  induction n;[intros;rewrite Z.div_1_r; reflexivity|].
  rewrite Nat2Z.inj_succ, Z.pow_succ_r by lia.
  simpl (fst _).
  destruct (pstep_n n st).
  intros Hg.
  assert (Hdivide : (2 ^ Z.of_nat n | g st)) by (etransitivity;[|apply Hg]; auto with *).
  divstep.divide_halving_massage Hg n.
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
  f (fst (pstep_n n st)) = f st.
Proof.
  induction n;[intros; reflexivity|].
  rewrite Nat2Z.inj_succ, Z.pow_succ_r by lia.
  intros Hg.
  simpl (fst _).
  assert (Hg' : (2 ^ Z.of_nat n | g st)) by (etransitivity;[|apply Hg]; auto with *).
  divstep.divide_halving_massage Hg n.
  rewrite <- g_hs in Hg by assumption.
  destruct (pstep_n n st).
  rewrite <- IHn by assumption.
  destruct (spec s);
  simpl in Hg;
  try solve [rewrite Zmod_odd, Z.add_comm, Z.odd_add_mul_2 in Hg;
             discriminate].
  reflexivity.
Qed.

(** When [g] is divisible by [2^n], [eta] decreases by [n] across [n] steps. *)
Lemma eta_hs n st : (2^(Z.of_nat n) | g st) ->
  eta (fst (pstep_n n st)) = eta st - (Z.of_nat n).
Proof.
  induction n;[intros;cbn;ring|].
  rewrite Nat2Z.inj_succ, Z.pow_succ_r by lia.
  intros Hg.
  simpl (fst _).
  assert (Hg' : (2 ^ Z.of_nat n | g st)) by (etransitivity;[|apply Hg]; auto with *).
  divstep.divide_halving_massage Hg n.
  rewrite <- g_hs in Hg by assumption.
  destruct (pstep_n n st).
  replace (eta st - _) with (eta st - (Z.of_nat n) - 1) by lia.
  rewrite <- IHn by assumption.
  destruct (spec s);
  simpl in Hg;
  try solve [rewrite Zmod_odd, Z.add_comm, Z.odd_add_mul_2 in Hg;
             discriminate].
  unfold eta.
  simpl.
  ring.
Qed.

(** When [g] is divisible by [2^n], all [n] steps are H steps, so [jac] picks
    up the halving flip of the (unchanged) [f] once per step -- i.e. once iff
    [n] is odd. *)
Lemma jac_hs n st : (2^(Z.of_nat n) | g st) ->
  jac (fst (pstep_n n st)) = xorb (jac st) (Nat.odd n && hflip (f st)).
Proof.
  induction n.
  { intros _.
    cbn.
    destruct (jac st); reflexivity. }
  rewrite Nat2Z.inj_succ, Z.pow_succ_r by lia.
  intros Hg.
  assert (Hg' : (2 ^ Z.of_nat n | g st)) by (etransitivity;[|apply Hg]; auto with *).
  assert (Hf : f (fst (pstep_n n st)) = f st) by (apply f_hs; assumption).
  assert (Hgn : g (fst (pstep_n n st)) = g st / 2 ^ Z.of_nat n) by (apply g_hs; assumption).
  assert (Heven : Zeven (g (fst (pstep_n n st)))).
  { destruct Hg as [k Hk].
    rewrite Hgn, Hk.
    replace (k * (2 * 2 ^ Z.of_nat n)) with (2 * k * 2 ^ Z.of_nat n) by ring.
    rewrite Z.div_mul by (apply Z.pow_nonzero; lia).
    apply Zeven_2p. }
  rewrite pstep_n_S_fst, pstep_jac, pflip_even by assumption.
  rewrite Hf, IHn by assumption.
  rewrite Nat.odd_succ, <- Nat.negb_odd.
  destruct (Nat.odd n), (jac st), (hflip (f st)); reflexivity.
Qed.

(** In the S-phase ([eta >= 0]), [eta] decreases by [n] across [n] steps. *)
Lemma eta_ss n st : 0 <= eta st ->
       Z.of_nat n <= 1 + eta st ->
       eta (fst (pstep_n n st)) = eta st - Z.of_nat n.
Proof.
  induction n;[intros;cbn;ring|].
  rewrite Nat2Z.inj_succ, <- Z.add_1_l.
  intros Heta Hn.
  simpl (fst _).
  destruct (pstep_n n st) as [s l].
  transitivity (eta st - Z.of_nat n - 1);[|ring].
  assert (Hs : eta (fst (s, l)) = eta st - Z.of_nat n) by (apply IHn; lia).
  rewrite <- Hs.
  unfold eta in *.
  destruct (spec s); cbn; try ring.
  cbn in Hs.
  lia.
Qed.

(* ----------------------------------------------------------------- *)
(** *** [pstep_n] composition. *)

(** [pstep_n] splits as a concatenation: [pstep_n (n + m) = pstep_n n . pstep_n m]. *)
Lemma pstep_n_app (n m : nat) st : pstep_n (n + m) st = let st1 := pstep_n m st in
  (fst (pstep_n n (fst st1)), snd (pstep_n n (fst st1)) ++ snd st1).
Proof.
  induction n;[destruct (pstep_n _ _);reflexivity|].
  cbn.
  rewrite IHn.
  cbn.
  destruct (pstep_n n _).
  cbn.
  destruct (pstep s).
  reflexivity.
Qed.

(** State projection of the [pstep_n] split. *)
Lemma pstep_n_app_fst (n m : nat) st : fst (pstep_n (n + m) st) = fst (pstep_n n (fst (pstep_n m st))).
Proof.
  rewrite pstep_n_app.
  reflexivity.
Qed.

(** Step-list projection of the [pstep_n] split. *)
Lemma pstep_n_app_snd (n m : nat) st : snd (pstep_n (n + m) st) =
  snd (pstep_n n (fst (pstep_n m st))) ++ snd (pstep_n m st).
Proof.
  rewrite pstep_n_app.
  reflexivity.
Qed.

(** In the D-phase ([g] odd, [eta < 0]), [eta] flips and decreases over [n] steps. *)
Lemma eta_ds n st : Zodd (g st) -> eta st < 0 ->
       0 < Z.of_nat n <= 1 - eta st ->
       eta (fst (pstep_n n st)) = -eta st - Z.of_nat n.
Proof.
  intros Hodd Heta Hn.
  destruct n;[lia|].
  rewrite <- Nat.add_1_r.
  rewrite pstep_n_app_fst.
  simpl (pstep_n 1 st).
  destruct (spec st);[elim (Zodd_not_Zeven _ Hodd); apply Zeven_2p| |unfold eta in *;cbn in *;lia].
  rewrite eta_ss; unfold eta in *; cbn in *; change (Z.pos_sub 1 d) with (1 - Z.pos d); try lia.
  change (0 < Z.of_nat (Datatypes.S n) <= 1 - -(Z.pos d)) in Hn.
  lia.
Qed.

(** Two states congruent mod [2^n] in [f], [g] (and equal [delta]) take the
    same [n]-step sequence and end with equal [delta].  The [jac] bits need a
    wider congruence; see [pstep_n_mod_jac]. *)
Lemma pstep_n_mod n st1 st2 :
  eqm (2^Z.of_nat n) (f st1) (f st2) ->
  eqm (2^Z.of_nat n) (g st1) (g st2) ->
  delta st1 = delta st2 ->
  delta (fst (pstep_n n st1)) = delta (fst (pstep_n n st2)) /\
  snd (pstep_n n st1) = snd (pstep_n n st2).
Proof.
  revert st1 st2.
  induction n;[simpl;repeat split;congruence|].
  intros st1 st2 Hf Hg Hdelta.
  replace (Datatypes.S n) with (n + 1)%nat by lia.
  rewrite !pstep_n_app_fst, !pstep_n_app_snd.
  simpl (pstep_n 1 st1); simpl (pstep_n 1 st2).
  unfold pstep; rewrite Hdelta.
  assert (Hdiv2 : forall x y, eqm (2 ^ Z.of_nat (Datatypes.S n)) x y -> eqm (2 ^ Z.of_nat n) (x / 2) (y / 2)).
  { intros x y.
    unfold eqm.
    rewrite <-!Z.land_ones, <-!(Z.shiftr_div_pow2 _ 1) by lia.
    replace (Z.of_nat n) with (Z.of_nat (Datatypes.S n) - 1) by lia.
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
    set (st1' := Build_State _ _ _ _ _);
    set (st2' := Build_State _ _ _ _ _);
    destruct (IHn st1' st2');
    try solve [cbn; lia|split; congruence].
  * eapply extra_math.eqm_2_pow_le;[|apply Hf]; lia.
  * apply Hdiv2; apply Hg.
  * eapply extra_math.eqm_2_pow_le;[|apply Hg]; lia.
  * apply Hdiv2; apply Zplus_eqm; assumption.
  * eapply extra_math.eqm_2_pow_le;[|apply Hf]; lia.
  * apply Hdiv2; apply Zplus_eqm; assumption.
Qed.

(** One step of two runs whose [f] and [g] agree mod [2^k] with [k >= 3] -- wide
    enough to pin the [f mod 8] and [f mod 4] that the flips read -- and whose
    [delta] and [jac] agree: the same step is taken, [delta] and [jac] stay
    equal, and the [f] / [g] congruence survives the step's one halving. *)
Lemma pstep_mod k st1 st2 : 3 <= k ->
  eqm (2^k) (f st1) (f st2) ->
  eqm (2^k) (g st1) (g st2) ->
  delta st1 = delta st2 ->
  jac st1 = jac st2 ->
  eqm (2^(k-1)) (f (fst (pstep st1))) (f (fst (pstep st2))) /\
  eqm (2^(k-1)) (g (fst (pstep st1))) (g (fst (pstep st2))) /\
  delta (fst (pstep st1)) = delta (fst (pstep st2)) /\
  jac (fst (pstep st1)) = jac (fst (pstep st2)) /\
  snd (pstep st1) = snd (pstep st2).
Proof.
  intros Hk Hf Hg Hdelta Hjac.
  assert (Hpar : Z.odd (g st1) = Z.odd (g st2)).
  { apply odd_eqm.
    change 2 with (2^1).
    apply (extra_math.eqm_2_pow_le 1 k);[lia|assumption]. }
  assert (Hf8 : eqm 8 (f st1) (f st2)).
  { change 8 with (2^3).
    apply (extra_math.eqm_2_pow_le 3 k);[lia|assumption]. }
  assert (Hg8 : eqm 8 (g st1) (g st2)).
  { change 8 with (2^3).
    apply (extra_math.eqm_2_pow_le 3 k);[lia|assumption]. }
  assert (Hf4 : eqm 4 (f st1) (f st2)).
  { change 4 with (2^2).
    apply (extra_math.eqm_2_pow_le 2 k);[lia|assumption]. }
  assert (Hg4 : eqm 4 (g st1) (g st2)).
  { change 4 with (2^2).
    apply (extra_math.eqm_2_pow_le 2 k);[lia|assumption]. }
  assert (Hdiv2 : forall x y, eqm (2^k) x y -> eqm (2^(k-1)) (x / 2) (y / 2)).
  { intros x y.
    unfold eqm.
    rewrite <-!Z.land_ones, <-!(Z.shiftr_div_pow2 _ 1) by lia.
    rewrite <-!extra_math.Z_shiftr_ones, <-!Z.shiftr_land by lia.
    congruence. }
  unfold pstep.
  rewrite Hdelta.
  destruct (Zeven_odd_dec (g st1)) as [He1|Ho1];
  destruct (Zeven_odd_dec (g st2)) as [He2|Ho2].
  - (* branch: H on both sides *)
    cbn.
    repeat split.
    + eapply extra_math.eqm_2_pow_le;[|apply Hf]; lia.
    + apply Hdiv2.
      assumption.
    + rewrite Hjac, (hflip_eqm _ _ Hf8).
      reflexivity.
  - (* branch: parity mismatch -- impossible *)
    exfalso.
    apply Zodd_bool_iff in Ho2.
    rewrite <- Hpar in Ho2.
    apply Zodd_bool_iff in Ho2.
    exact (Zodd_not_Zeven _ Ho2 He1).
  - (* branch: parity mismatch -- impossible *)
    exfalso.
    apply Zodd_bool_iff in Ho1.
    rewrite Hpar in Ho1.
    apply Zodd_bool_iff in Ho1.
    exact (Zodd_not_Zeven _ Ho1 He2).
  - (* branch: g odd on both sides -- D or S together *)
    destruct (0 <? delta st2).
    + (* sub-branch: D *)
      cbn.
      repeat split.
      * eapply extra_math.eqm_2_pow_le;[|apply Hg]; lia.
      * apply Hdiv2.
        apply Zplus_eqm; assumption.
      * rewrite Hjac, (sflip_eqm _ _ _ _ Hf4 Hg4), (hflip_eqm _ _ Hg8).
        reflexivity.
    + (* sub-branch: S *)
      cbn.
      repeat split.
      * eapply extra_math.eqm_2_pow_le;[|apply Hf]; lia.
      * apply Hdiv2.
        apply Zplus_eqm; assumption.
      * rewrite Hjac, (hflip_eqm _ _ Hf8).
        reflexivity.
Qed.

(** The [jac]-carrying strengthening of [pstep_n_mod]: two runs whose [f], [g]
    agree mod [2^(n+2)] -- two bits of slack, so that the [mod 8] the flips
    read is still pinned at the last of the [n] steps -- and whose [delta] and
    [jac] agree run the same [n] steps and end with equal [delta] and [jac].
    This is what lets the C compute [jac] from [f], [g] truncated to a limb. *)
Lemma pstep_n_mod_jac n st1 st2 :
  eqm (2^(Z.of_nat n + 2)) (f st1) (f st2) ->
  eqm (2^(Z.of_nat n + 2)) (g st1) (g st2) ->
  delta st1 = delta st2 ->
  jac st1 = jac st2 ->
  delta (fst (pstep_n n st1)) = delta (fst (pstep_n n st2)) /\
  jac (fst (pstep_n n st1)) = jac (fst (pstep_n n st2)) /\
  snd (pstep_n n st1) = snd (pstep_n n st2).
Proof.
  revert st1 st2.
  induction n.
  { intros st1 st2 _ _ Hdelta Hjac.
    cbn.
    auto. }
  intros st1 st2 Hf Hg Hdelta Hjac.
  assert (HK : 3 <= Z.of_nat (Datatypes.S n) + 2) by lia.
  destruct (pstep_mod _ _ _ HK Hf Hg Hdelta Hjac) as [Hf1 [Hg1 [Hd1 [Hj1 Hs1]]]].
  assert (HfN : eqm (2 ^ (Z.of_nat n + 2)) (f (fst (pstep st1))) (f (fst (pstep st2)))).
  { replace (Z.of_nat n + 2) with (Z.of_nat (Datatypes.S n) + 2 - 1) by lia.
    assumption. }
  assert (HgN : eqm (2 ^ (Z.of_nat n + 2)) (g (fst (pstep st1))) (g (fst (pstep st2)))).
  { replace (Z.of_nat n + 2) with (Z.of_nat (Datatypes.S n) + 2 - 1) by lia.
    assumption. }
  destruct (IHn (fst (pstep st1)) (fst (pstep st2)) HfN HgN Hd1 Hj1) as [HD [HJ HS]].
  replace (Datatypes.S n) with (n + 1)%nat by lia.
  rewrite !pstep_n_app_fst, !pstep_n_app_snd, !pstep_n_1.
  cbn [fst snd].
  repeat split.
  - assumption.
  - assumption.
  - rewrite HS, Hs1.
    reflexivity.
Qed.

(* ================================================================= *)
(** ** Positivity bounds -- [pstep_bound_step] / [pstep_bounds]. *)

(** One positive divstep keeps [f] in [(0, M]] and [g] in [[0, M)].  This is
    the invariant that makes the C's [f] and [g] limbs nonnegative. *)
Lemma pstep_bound_step M st : 0 < f st <= M -> 0 <= g st < M ->
  0 < f (fst (pstep st)) <= M /\ 0 <= g (fst (pstep st)) < M.
Proof.
  destruct (spec st); cbn; lia.
Qed.

(** [f] stays in [(0, M]] and [g] in [[0, M)] across [n] steps. *)
Lemma pstep_bounds M st n : 0 < f st <= M -> 0 <= g st < M ->
  0 < f (fst (pstep_n n st)) <= M /\ 0 <= g (fst (pstep_n n st)) < M.
Proof.
  intros Hf Hg.
  induction n;[cbn; lia|].
  destruct IHn as [IHf IHg].
  rewrite pstep_n_S_fst.
  apply pstep_bound_step; assumption.
Qed.

(* ================================================================= *)
(** ** Fixed point and gcd -- [pfixed] / [pfixed_f] / [pfixed_g] / [pstep_gcd]. *)

(** Once [g = 0] the pair [(f, g)] is fixed: [f] is preserved and [g] stays
    [0].  ([jac] keeps flipping; see [jac_hs].) *)
Lemma pfixed st n : g st = 0 ->
 f (fst (pstep_n n st)) = f st /\ g (fst (pstep_n n st)) = 0.
Proof.
  intros Hg.
  induction n;[auto|].
  cbn.
  destruct (pstep_n n st) as [[d0 f0 g0 j0 Hf0] l].
  unfold pstep.
  cbn in *.
  destruct IHn as [-> ->].
  cbn.
  auto.
Qed.

(** [f] projection of [pfixed]. *)
Lemma pfixed_f st n : g st = 0 ->
 f (fst (pstep_n n st)) = f st.
Proof.
  intros Hg.
  destruct (pfixed st n Hg).
  assumption.
Qed.

(** [g] projection of [pfixed]. *)
Lemma pfixed_g st n : g st = 0 ->
 g (fst (pstep_n n st)) = 0.
Proof.
  intros Hg.
  destruct (pfixed st n Hg).
  assumption.
Qed.

(** The gcd of [(f, g)] is invariant across [n] steps. *)
Lemma pstep_gcd st d n : Zis_gcd (f st) (g st) d ->
 Zis_gcd (f (fst (pstep_n n st))) (g (fst (pstep_n n st))) d.
Proof.
  intros Hgcd.
  induction n;[auto|].
  cbn.
  destruct (pstep_n n st) as [st0 l].
  cbn in IHn.
  destruct (spec st0);cbn in *;
    revert IHn;
    apply Zis_gcd_ind;
    intros Hd1 Hd2 Hdx;
    apply Zis_gcd_intro; try assumption.
  * assert (Hodd : Z.odd d = true) by (exact (divstep.odd_divisor _ _ Hd1 (Zodd_2p_plus_1 f'))).
    eapply Gauss;[apply Hd2|].
    apply rel_prime_mod_rev;[lia|].
    rewrite Zmod_odd, Hodd.
    apply rel_prime_1.
  * intros x Hxf Hxg.
    apply Hdx; try assumption.
    auto with *.
  * assert (Hodd : Z.odd d = true) by (exact (divstep.odd_divisor _ _ Hd1 (Zodd_2p_plus_1 f'))).
    apply Gauss with 2.
    + replace (2 * (g' + f' + 1)) with ((2 * g' + 1) + (2 * f' + 1)) by ring.
      apply Z.divide_add_r; assumption.
    + apply rel_prime_mod_rev;[lia|].
      rewrite Zmod_odd, Hodd.
      apply rel_prime_1.
  * intros x Hxf Hxg.
    apply Hdx; try assumption.
    replace (2 * f' + 1) with ((2*(g' + f' + 1)) - (2 * g' + 1)) by ring.
    apply Z.divide_sub_r; try assumption.
    auto with *.
  * assert (Hodd : Z.odd d = true) by (exact (divstep.odd_divisor _ _ Hd1 (Zodd_2p_plus_1 f'))).
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
