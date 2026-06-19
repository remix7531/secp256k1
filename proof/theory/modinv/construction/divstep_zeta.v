(** * theory.modinv.construction.divstep_zeta: the constant-time (zeta) divstep machine --
    [ZState] / [zstep] / [zstep_n] (branching on [zeta < 0] instead of [0 < delta]),
    its per-step bridge [z_to_state] to the variable-time [step], the accumulated
    matrix [ztrans_n], the per-limb [update_de] modular tracking, and the driver
    glue ([scale_m] / [zstep_n_mod] / [zupdate_de_eqm_gen]). *)
(** Copyright (C) 2026 remix7531
    Ported from BlockstreamResearch/simplicity Coq/C/divstep.v
    (commit c1dddedd), Copyright (c) 2018 Blockstream, originally MIT.
    Upstream notice reproduced in proof/README.md.
    SPDX-License-Identifier: MIT *)

(** Builds on the variable-time machine in [divstep] and the matrix algebra in
    [divstep_trans].

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
Require Import secp256k1.theory.modinv.construction.divstep_trans.

Open Scope list_scope.
Open Scope Z_scope.
Arguments Z.add !x !y.
Arguments Z.sub !m !n.
Arguments Z.mul !x !y.

(* ================================================================= *)
(** ** Per-limb modular reduction -- [pre_div62Modulo] / [update_de]. *)

(** Reduce [a] mod [M] toward a multiple of [2^62] (the per-limb safegcd update). *)
Definition pre_div62Modulo (M a : Z) : Z :=
  a - (((mod_inv M (2^62))*a) mod 2^62) * M.

(** [pre_div62Modulo] preserves the residue mod [M]. *)
Lemma pre_div62Modulo_mod (M a : Z) : pre_div62Modulo M a mod M = a mod M.
Proof.
  unfold pre_div62Modulo, Z.sub.
  rewrite <- Z.mul_opp_l.
  apply Z_mod_plus_full.
Qed.

(** For odd [M], [pre_div62Modulo M a] is divisible by [2^62]. *)
Lemma pre_div62Modulo_divide M a : Zodd M -> (2^62 | pre_div62Modulo M a).
Proof.
  intros HM.
  apply Z.mod_divide;[lia|].
  unfold pre_div62Modulo.
  rewrite <- Zminus_mod_idemp_r, Zmult_mod_idemp_l.
  replace (mod_inv M (2 ^ 62) * a * M) with (mod_inv M (2 ^ 62) * M * a) by ring.
  rewrite <- Zmult_mod_idemp_l, mod_inv_mul_l.
  replace (Z.gcd M (2 ^ 62)) with 1;
  [rewrite Z.mul_1_l, Zminus_mod_idemp_r, Z.sub_diag; reflexivity|].
  symmetry.
  apply Zgcd_1_rel_prime.
  apply Zpow_facts.rel_prime_Zpower_r;[lia|].
  apply Zgcd_1_rel_prime.
  apply Z.bezout_1_gcd.
  apply Zodd_ex_iff in HM.
  destruct HM as [m HMm].
  exists 1; exists (-m).
  lia.
Qed.

(** One safegcd [(d, e)] update: apply [mtx], reduce each component mod [M],
    and shift right by [62]. *)
Definition update_de (M d e : Z) (mtx : Trans.M2x2) : (Z * Z) :=
  let vec := Trans.ap mtx
              {| Trans.x := d + if d <? 0 then M else 0;
                 Trans.y := e + if e <? 0 then M else 0
               |} in
  ( pre_div62Modulo M (Trans.x vec) / 2^62
  , pre_div62Modulo M (Trans.y vec) / 2^62
  ).

(** [update_de] keeps both outputs within the [(-2m, m)] window. *)
Lemma update_de_bound m d e mtx : Zodd m ->
   Z.abs (Trans.u mtx) + Z.abs (Trans.v mtx) <= 2 ^ 62 ->
   Z.abs (Trans.q mtx) + Z.abs (Trans.r mtx) <= 2 ^ 62 ->
   -2 * m < d < m -> -2 * m < e < m ->
   -2 * m < fst (update_de m d e mtx) < m /\ -2 * m < snd (update_de m d e mtx) < m.
Proof.
  intros Hoddm Huv Hqr Hmd Hme.
  unfold update_de.
  set (x := Trans.x _).
  set (y := Trans.y _).
  assert (Hm1 : 1 <= m) by lia.
  assert (Hxbound : Z.abs x <= 2^62 * (m - 1)).
  { cbn.
    eapply Z.le_trans;[apply Z.abs_triangle|].
    rewrite !Z.abs_mul.
    apply Z.le_trans with ((Z.abs (Trans.u mtx) + Z.abs (Trans.v mtx))*(m - 1));[|nia].
    destruct (Z.ltb_spec0 d 0); destruct (Z.ltb_spec0 e 0);
    rewrite Z.mul_add_distr_r; apply Z.add_le_mono; apply Zmult_le_compat_l; lia. }
  assert (Hybound : Z.abs y <= 2^62 * (m - 1)).
  { cbn.
    eapply Z.le_trans;[apply Z.abs_triangle|].
    rewrite !Z.abs_mul.
    apply Z.le_trans with ((Z.abs (Trans.q mtx) + Z.abs (Trans.r mtx))*(m - 1));[|nia].
    destruct (Z.ltb_spec0 d 0); destruct (Z.ltb_spec0 e 0);
    rewrite Z.mul_add_distr_r; apply Z.add_le_mono; apply Zmult_le_compat_l; lia. }
  cbn -[Z.div Z.pow x y].
  unfold pre_div62Modulo.
  assert (Hxmod : 0 <= (mod_inv m (2 ^ 62) * x) mod 2 ^ 62 < 2^62) by (apply Z.mod_pos_bound;lia).
  assert (Hymod : 0 <= (mod_inv m (2 ^ 62) * y) mod 2 ^ 62 < 2^62) by (apply Z.mod_pos_bound;lia).
  rewrite <- !Z.shiftr_div_pow2 by lia.
  split.
  * cut (-2*m + 1 <= Z.shiftr (x - (mod_inv m (2 ^ 62) * x) mod 2 ^ 62 * m) 62 < m);[lia|apply shiftr_bounds;nia].
  * cut (-2*m + 1 <= Z.shiftr (y - (mod_inv m (2 ^ 62) * y) mod 2 ^ 62 * m) 62 < m);[lia|apply shiftr_bounds;nia].
Qed.

(** Matrix-generic core of the [update_de] tracking lemmas.  For ANY [2x2]
    matrix [mtx] and raw target vector [(f1, g1)] satisfying the [scale (2^62)]
    relation [ap mtx (f0, g0) = scale (2^62) (f1, g1)], one [update_de] step
    tracks [(f0, g0)] to [(f1, g1)] modulo [m].  The three public tracking
    lemmas -- [update_de_eqm] (variable-time), [zupdate_de_eqm] (constant-time),
    and [zupdate_de_eqm_gen] (arbitrary matrix) -- are all instances of this,
    supplying the [trans_n_step] / [ztrans_n_step] scaling relation as [Hrel]. *)
Lemma update_de_eqm_core m x d e (mtx : Trans.M2x2) (f0 g0 f1 g1 : Z) : Zodd m ->
  Trans.ap mtx {| Trans.x := f0; Trans.y := g0 |}
    = Trans.scale (2^62) {| Trans.x := f1; Trans.y := g1 |} ->
  eqm m (x * d) f0 ->
  eqm m (x * e) g0 ->
  eqm m (x * fst (update_de m d e mtx)) f1 /\
  eqm m (x * snd (update_de m d e mtx)) g1.
Proof.
  intros Hoddm Hrel Hf Hg.
  unfold update_de.
  generalize (fun a => pre_div62Modulo_divide m a Hoddm).
  generalize (pre_div62Modulo_mod m).
  revert Hrel.
  cbn [Trans.x Trans.y Trans.scale Trans.ap Trans.u Trans.v Trans.q Trans.r].
  destruct mtx as [u v q r].
  cbn [Trans.x Trans.y Trans.scale Trans.ap Trans.u Trans.v Trans.q Trans.r].
  intros Hrel.
  injection Hrel; clear Hrel; intros Hgqr Hfuv.
  cbn -[Z.div pre_div62Modulo] in *.
  intros Hpre1 Hpre2.
  assert (Hn : 0 < 2^62) by lia.
  assert (Hinv : mod_inv (2^62) m * (2^62) mod m = 1 mod m).
  { rewrite mod_inv_mul_l.
    f_equal.
    rewrite Zgcd_1_rel_prime.
    apply rel_prime_sym.
    apply Zpow_facts.rel_prime_Zpower_r;[lia|].
    apply rel_prime_sym.
    apply prime_rel_prime;[apply prime_2|].
    rewrite Zodd_equiv in Hoddm.
    destruct Hoddm as [b ->].
    intros Hdivide.
    apply (Z.divide_add_cancel_r _ _ _ (Z.divide_factor_l _ _)) in Hdivide.
    apply Z.divide_1_r_abs in Hdivide.
    discriminate. }
  (* the [scale (2^62)] relation carries [2^62] as a numeric literal; refold it
     so the [Hinv] / [Hpre1] rewrites match the divisor in the goal *)
  change 4611686018427387904 with (2^62) in *.
  unfold eqm.
  rewrite <- !(Zmult_mod_idemp_l x).
  replace x with (x*1) by ring.
  rewrite <- !(Zmult_mod_idemp_r 1), <-Hinv, !Zmult_mod_idemp_r, !Zmult_mod_idemp_l.
  rewrite <-!Z.mul_assoc, <-!Zdivide_Zdiv_eq by auto.
  rewrite !Z.mul_assoc, <-!(Zmult_mod_idemp_r (pre_div62Modulo m _)), !Hpre1.
  assert (Hab : forall a b, eqm m (a * (d + (if d <? 0 then m else 0)) + b * (e + (if e <? 0 then m else 0))) (a*d + b*e)).
  { intros a b.
    apply Zplus_eqm;apply Zmult_eqm;try apply eqm_refl;destruct (Z.ltb _ _);unfold eqm;
     rewrite <-Zplus_mod_idemp_r, ?Z_mod_same_full, ?Zmod_0_l;f_equal;try ring. }
  rewrite !Hab, !Zmult_mod_idemp_r.
  rewrite !(Z.mul_comm (x * _)), !Z.mul_assoc, !(Z.mul_add_distr_r _ _ x).
  rewrite <-!Z.mul_assoc, !(Z.mul_comm _ x).
  rewrite <-!(Zmult_mod_idemp_l (_ + _)), !(Zplus_mod (_ * (x * d))), <- !(Zmult_mod_idemp_r (x * _)).
  rewrite Hf, Hg, !Zmult_mod_idemp_r, <-!Zplus_mod, !Zmult_mod_idemp_l.
  (* substitute the matrix relation, then [Hinv] collapses [2^62 * mod_inv = 1] *)
  rewrite Hfuv, Hgqr.
  assert (Hclose : forall z, (2 ^ 62 * z * mod_inv (2 ^ 62) m) mod m = z mod m).
  { intros z.
    rewrite <-(Z.mul_assoc (2 ^ 62)), (Z.mul_comm z), Z.mul_assoc, (Z.mul_comm (2 ^ 62) (mod_inv (2 ^ 62) m)), <-Zmult_mod_idemp_l, Hinv, Zmult_mod_idemp_l, Z.mul_1_l.
    reflexivity. }
  split; apply Hclose.
Qed.

(** [update_de] (over 62 steps) tracks [f] / [g] of [step_n 62] modulo [m]. *)
Lemma update_de_eqm m x d e st : Zodd m ->
  eqm m (x * d) (f st) ->
  eqm m (x * e) (g st) ->
  eqm m (x * fst (update_de m d e (Trans.trans_n 62 st))) (f (fst (step_n 62 st))) /\
  eqm m (x * snd (update_de m d e (Trans.trans_n 62 st))) (g (fst (step_n 62 st))).
Proof.
  intros Hoddm Hf Hg.
  apply (update_de_eqm_core m x d e (Trans.trans_n 62 st)
           (f st) (g st) (f (fst (step_n 62 st))) (g (fst (step_n 62 st)))); try assumption.
  symmetry.
  change (2^62) with (2^Z.of_nat 62).
  exact (Trans.trans_n_step 62 st).
Qed.

(* ================================================================= *)
(** ** Constant-time (zeta) divstep machine -- [ZState] / [zstep] / [zstep_n]. *)

(** The constant-time driver ([secp256k1_modinv64_divsteps_59], and the
    top-level [secp256k1_modinv64]) runs the SAME three H/S/D maps on [(f, g)]
    as [step], but branches on the sign of [zeta = -(delta + 1/2)] (the C test
    [zeta >> 63], i.e. [zeta < 0]) instead of [0 < delta].  The [(f, g)] maps and
    the emitted [Step] tag of one zeta-step are exactly those of one model [step]
    on a state whose [delta := -zeta]: with [zeta < 0  <->  0 < -zeta] the same
    H/D/S branch is selected.  (The half-integer offset between [delta] and
    [zeta] means [delta] does NOT evolve in lockstep, so the bridge [z_to_state] is
    used only PER STEP -- to read off which of H/S/D fired -- never iterated.)
    Every matrix-algebra and gcd/eqm fact the variable-time driver needs ports to
    the zeta machine by destructing [z_spec] in place of [spec]. *)

(** Constant-time divstep state: [zeta], the pair [(zf, zg)], oddness of [zf]. *)
Record ZState : Set :=
 { zeta : Z;
   zf : Z;
   zg : Z;
   zodd_f : Zodd zf
 }.

(** Initial constant-time state: [zeta = -1] (delta = 1/2), [f = m], [g = x]. *)
Definition zinit (m x : Z) (oddm : Zodd m) : ZState :=
{| zeta := -1;
   zf := m;
   zg := x;
   zodd_f := oddm
 |}.

(** One constant-time divstep: branches on [zg] parity and [zeta < 0]. *)
Definition zstep (st : ZState) : ZState * Step :=
match Zeven_odd_dec (zg st) with
| left _ => ({| zeta := zeta st - 1;
                zf := zf st;
                zg := zg st / 2;
                zodd_f := zodd_f st
              |}
            , Step.H)
| right odd_g =>
    if (zeta st <? 0)%Z
    then ({| zeta := - zeta st - 2;
             zf := zg st;
             zg := (zg st - zf st) / 2;
             zodd_f := odd_g
           |}
         , Step.D)
    else ({| zeta := zeta st - 1;
             zf := zf st;
             zg := (zg st + zf st) / 2;
             zodd_f := zodd_f st
           |}
         , Step.S)
end.

(** [n]-fold constant-time divstep; the last step is first in the list (to match
    [step_n]'s matrix-multiplication order). *)
Fixpoint zstep_n (n : nat) : ZState -> ZState * list Step :=
match n with
| O => fun st => (st, nil)
| Datatypes.S n => fun st =>
    let (st0, xs) := zstep_n n st in
    let (st1, x) := zstep st0 in
    (st1, x :: xs)
end.

(* ----------------------------------------------------------------- *)
(** *** Per-step bridge to the [step] machine -- [z_to_state] / [z_spec]. *)

(** Map a constant-time state to the model [State] selecting the same branch
    via [delta := -zeta].  Used PER STEP only (see the module note): the [(f, g)]
    fields and the H/D/S selection of [step (z_to_state st)] match [zstep st]. *)
Definition z_to_state (st : ZState) : State :=
{| delta := - zeta st;
   f := zf st;
   g := zg st;
   odd_f := zodd_f st
 |}.

(** The [(f, g)] vector and the [Step] tag of one zeta-step are exactly those of
    one model [step] on [z_to_state st].  This packages the sign-case analysis so
    downstream lemmas can destruct it as they would [spec]. *)
Lemma z_to_state_step st :
  f (fst (step (z_to_state st))) = zf (fst (zstep st)) /\
  g (fst (step (z_to_state st))) = zg (fst (zstep st)) /\
  snd (step (z_to_state st)) = snd (zstep st).
Proof.
  destruct st as [z0 f0 g0 Hf0].
  unfold zstep, step, z_to_state; cbn -[Z.div].
  destruct (Zeven_odd_dec g0) as [Hg0|Hg0].
  - (* H-case: g even -- f kept, g halved, tags H *)
    repeat split; reflexivity.
  - (* odd g: the sign branches line up via [zeta < 0  <->  0 < -zeta] *)
    destruct (z0 <? 0) eqn:Hz.
    + (* D-case: zeta < 0  <->  0 < -zeta *)
      apply Z.ltb_lt in Hz.
      replace (0 <? - z0) with true by (symmetry; apply Z.ltb_lt; lia).
      cbn -[Z.div].
      repeat split; reflexivity.
    + (* S-case: zeta >= 0  <->  -zeta <= 0 *)
      apply Z.ltb_ge in Hz.
      replace (0 <? - z0) with false by (symmetry; apply Z.ltb_ge; lia).
      cbn -[Z.div].
      repeat split; reflexivity.
Qed.

(** [Spec]-style characterization of [zstep]: [zstep st] is a model [step] on
    [z_to_state st], so it satisfies the SAME [Spec] inductive.  Destruct this for
    case-access to the H/D/S form of any zeta-step. *)
Lemma z_spec st : Spec (z_to_state st) (step (z_to_state st)).
Proof.
  apply spec.
Qed.

(** The [Step] tag of [zstep] equals that of the bridged [step]. *)
Lemma zstep_snd st : snd (zstep st) = snd (step (z_to_state st)).
Proof.
  symmetry.
  apply z_to_state_step.
Qed.

(** [zf] of [zstep] equals [f] of the bridged [step]. *)
Lemma zstep_zf st : zf (fst (zstep st)) = f (fst (step (z_to_state st))).
Proof.
  symmetry.
  apply z_to_state_step.
Qed.

(** [zg] of [zstep] equals [g] of the bridged [step]. *)
Lemma zstep_zg st : zg (fst (zstep st)) = g (fst (step (z_to_state st))).
Proof.
  symmetry.
  apply z_to_state_step.
Qed.

(* ----------------------------------------------------------------- *)
(** *** [zstep_n] unfolding -- [zstep_n_fst_s] / [zstep_n_app]. *)

(** State after [S n] zeta-steps: one [zstep] on the [n]-step state. *)
Lemma zstep_n_fst_s n st :
  fst (zstep_n (Datatypes.S n) st) = fst (zstep (fst (zstep_n n st))).
Proof.
  cbn.
  destruct (zstep_n n st) as [st0 l].
  cbn.
  destruct (zstep st0) as [st1 x].
  reflexivity.
Qed.

(** Step-list after [S n] zeta-steps: the head step prepended. *)
Lemma zstep_n_snd_S n st :
  snd (zstep_n (Datatypes.S n) st) = snd (zstep (fst (zstep_n n st))) :: snd (zstep_n n st).
Proof.
  cbn.
  destruct (zstep_n n st) as [st0 l].
  cbn.
  destruct (zstep st0) as [st1 x].
  reflexivity.
Qed.

(** [zstep_n] splits as a concatenation: [zstep_n (n + m) = zstep_n n . zstep_n m]. *)
Lemma zstep_n_app (n m : nat) st : zstep_n (n + m) st = let st1 := zstep_n m st in
  (fst (zstep_n n (fst st1)), snd (zstep_n n (fst st1)) ++ snd st1).
Proof.
  induction n;[destruct (zstep_n _ _);reflexivity|].
  cbn.
  rewrite IHn.
  cbn.
  destruct (zstep_n n _) as [z l].
  cbn.
  destruct (zstep z).
  reflexivity.
Qed.

(** State projection of the [zstep_n] split. *)
Lemma zstep_n_app_fst (n m : nat) st :
  fst (zstep_n (n + m) st) = fst (zstep_n n (fst (zstep_n m st))).
Proof.
  rewrite zstep_n_app.
  reflexivity.
Qed.

(** Step-list projection of the [zstep_n] split. *)
Lemma zstep_n_app_snd (n m : nat) st :
  snd (zstep_n (n + m) st) = snd (zstep_n n (fst (zstep_n m st))) ++ snd (zstep_n m st).
Proof.
  rewrite zstep_n_app.
  reflexivity.
Qed.

(* ----------------------------------------------------------------- *)
(** *** Divisible-[zg] shift -- [zg_hs]. *)

(** When [zg] is divisible by [2^n], [zg] is right-shifted by [n] across [n]
    zeta-steps.  Mirrors [g_hs]; the per-step [g]-map is the bridged [step]'s. *)
Lemma zg_hs n st : (2^(Z.of_nat n) | zg st) ->
  zg (fst (zstep_n n st)) = zg st / 2^(Z.of_nat n).
Proof.
  induction n;[intros;rewrite Z.div_1_r; reflexivity|].
  rewrite Nat2Z.inj_succ, Z.pow_succ_r by lia.
  rewrite zstep_n_fst_s.
  intros Hg.
  set (st0 := fst (zstep_n n st)) in *.
  change (zg st0) with (g (z_to_state st0)) in IHn.
  assert (Hdivide : (2 ^ Z.of_nat n | zg st)) by (etransitivity;[|apply Hg]; auto with *).
  divide_halving_massage Hg n.
  rewrite <- IHn in Hg by assumption.
  rewrite (zstep_zg st0).
  destruct (z_spec st0);
  cbn in Hg;
  try solve [rewrite Zmod_odd, Z.add_comm, Z.odd_add_mul_2 in Hg;
             discriminate].
  cbn [fst g].
  cbn [g] in IHn.
  f_equal.
  rewrite (Z.mul_comm 2 (2^Z.of_nat n)).
  rewrite <- Zdiv_Zdiv by lia.
  rewrite <- IHn by assumption.
  rewrite Z.mul_comm, Z_div_mult by lia.
  reflexivity.
Qed.

(* ----------------------------------------------------------------- *)
(** *** Fixed point and gcd -- [zfixed] / [zgcd]. *)

(** Once [zg = 0] the zeta-state is fixed: [zf] preserved and [zg] stays [0]. *)
Lemma zfixed st n : zg st = 0 ->
 zf (fst (zstep_n n st)) = zf st /\ zg (fst (zstep_n n st)) = 0.
Proof.
  intros Hg.
  induction n;[auto|].
  rewrite zstep_n_fst_s.
  destruct IHn as [IHf IHg].
  unfold zstep.
  destruct (fst (zstep_n n st)) as [z0 zf0 zg0 Hf0].
  cbn in *.
  rewrite IHg.
  cbn.
  auto.
Qed.

(** [zf] projection of [zfixed]. *)
Lemma zfixed_f st n : zg st = 0 ->
 zf (fst (zstep_n n st)) = zf st.
Proof.
  intros Hg.
  destruct (zfixed st n Hg).
  assumption.
Qed.

(** [zg] projection of [zfixed]. *)
Lemma zfixed_g st n : zg st = 0 ->
 zg (fst (zstep_n n st)) = 0.
Proof.
  intros Hg.
  destruct (zfixed st n Hg).
  assumption.
Qed.

(** The gcd of [(zf, zg)] is invariant across [n] zeta-steps.  Mirrors [gcd];
    the per-step algebra is identical (the [Spec] cases are the same), so it
    reuses the bridged [z_spec]. *)
Lemma zgcd st d n : Zis_gcd (zf st) (zg st) d ->
 Zis_gcd (zf (fst (zstep_n n st))) (zg (fst (zstep_n n st))) d.
Proof.
  intros Hgcd.
  induction n;[auto|].
  rewrite zstep_n_fst_s.
  set (st0 := fst (zstep_n n st)) in *.
  rewrite (zstep_zf st0), (zstep_zg st0).
  change (zf st0) with (f (z_to_state st0)) in IHn.
  change (zg st0) with (g (z_to_state st0)) in IHn.
  destruct (z_spec st0);cbn in *;
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

(* ----------------------------------------------------------------- *)
(** *** Magnitude bounds -- [zf_step_bounds] / [zg_step_bounds] / [zfg_bounds]. *)

(** [zf] after one zeta-step is bounded by [max |zf| |zg|]. *)
Lemma zf_step_bounds st : Z.abs (zf (fst (zstep st))) <= Z.max (Z.abs (zf st)) (Z.abs (zg st)).
Proof.
  rewrite (zstep_zf st).
  change (zf st) with (f (z_to_state st)).
  change (zg st) with (g (z_to_state st)).
  apply f_step_bounds.
Qed.

(** Twice [zg] after one zeta-step is bounded by [|zf| + |zg|]. *)
Lemma zg_step_bounds st : 2 * Z.abs (zg (fst (zstep st))) <= Z.abs (zf st) + Z.abs (zg st).
Proof.
  rewrite (zstep_zg st).
  change (zf st) with (f (z_to_state st)).
  change (zg st) with (g (z_to_state st)).
  apply g_step_bounds.
Qed.

(** Both [zf] and [zg] stay bounded by [max |zf| |zg|] across [n] zeta-steps. *)
Lemma zfg_bounds st n :
 Z.abs (zf (fst (zstep_n n st))) <= Z.max (Z.abs (zf st)) (Z.abs (zg st)) /\
 Z.abs (zg (fst (zstep_n n st))) <= Z.max (Z.abs (zf st)) (Z.abs (zg st)).
Proof.
  induction n;[cbn; lia|].
  rewrite zstep_n_fst_s.
  assert (Hf := zf_step_bounds (fst (zstep_n n st))).
  assert (Hg := zg_step_bounds (fst (zstep_n n st))).
  assert (HM : Z.max (Z.abs (zf (fst (zstep_n n st)))) (Z.abs (zg (fst (zstep_n n st)))) <=
               Z.max (Z.abs (zf st)) (Z.abs (zg st))) by lia.
  lia.
Qed.

(** Strict variant: when [|zg| < |zf|], [zg] stays strictly below [max |zf| |zg|]. *)
Lemma zfg_bounds_strict st n :
 Z.abs (zg st) < Z.abs (zf st) ->
 Z.abs (zf (fst (zstep_n n st))) <= Z.max (Z.abs (zf st)) (Z.abs (zg st)) /\
 Z.abs (zg (fst (zstep_n n st))) < Z.max (Z.abs (zf st)) (Z.abs (zg st)).
Proof.
  intros Hlt.
  induction n;[cbn; lia|].
  rewrite zstep_n_fst_s.
  assert (Hf := zf_step_bounds (fst (zstep_n n st))).
  assert (Hg := zg_step_bounds (fst (zstep_n n st))).
  assert (HM : Z.max (Z.abs (zf (fst (zstep_n n st)))) (Z.abs (zg (fst (zstep_n n st)))) <=
               Z.max (Z.abs (zf st)) (Z.abs (zg st))) by lia.
  lia.
Qed.

(* ----------------------------------------------------------------- *)
(** *** [zeta] drift -- [zeta_step_bounds] / [zeta_bounds]. *)

(** One zeta-step moves [zeta] within the [[-zeta - 2, zeta + 1]] envelope; in
    particular [|new zeta| <= |zeta| + 2]. *)
Lemma zeta_step_bounds st : Z.abs (zeta (fst (zstep st))) <= Z.abs (zeta st) + 2.
Proof.
  unfold zstep.
  destruct (Zeven_odd_dec (zg st)) as [Hg|Hg].
  - (* H: zeta -> zeta + 1 *)
    cbn.
    lia.
  - (* odd g: D (zeta -> -zeta-2) or S (zeta -> zeta-1) *)
    destruct (zeta st <? 0);cbn;lia.
Qed.

(** [zeta] grows by at most [2] per step: [|zeta|] after [n] steps is bounded by
    [|zeta| + 2n].  (The driver only needs a coarse envelope to discharge the C
    [VERIFY_CHECK(zeta >= -591 && zeta <= 591)].) *)
Lemma zeta_bounds n st : Z.abs (zeta (fst (zstep_n n st))) <= Z.abs (zeta st) + 2 * Z.of_nat n.
Proof.
  induction n;[cbn;lia|].
  rewrite zstep_n_fst_s.
  assert (Hstep := zeta_step_bounds (fst (zstep_n n st))).
  rewrite Nat2Z.inj_succ.
  lia.
Qed.

(* ================================================================= *)
(** ** Constant-time transition-matrix algebra -- [zfg] / [ztrans_n]. *)

(** The [(zf, zg)] vector of a constant-time state. *)
Definition zfg st := {| Trans.x := zf st; Trans.y := zg st |}.

(** One zeta-step doubles the [(zf, zg)] vector, realized by [Trans.trans] of the
    emitted tag.  Mirrors [Trans.trans_step]; the per-step tag and [(f, g)] maps
    are the bridged [step]'s, so [z_spec] supplies the same three cases. *)
Lemma ztrans_step st :
  Trans.scale 2 (zfg (fst (zstep st))) = Trans.ap (Trans.trans (snd (zstep st))) (zfg st).
Proof.
  unfold zfg.
  rewrite (zstep_zf st), (zstep_zg st), (zstep_snd st).
  change (zf st) with (f (z_to_state st)).
  change (zg st) with (g (z_to_state st)).
  change ({| Trans.x := f (z_to_state st); Trans.y := g (z_to_state st) |})
    with (Trans.fg (z_to_state st)).
  change ({| Trans.x := f (fst (step (z_to_state st)));
             Trans.y := g (fst (step (z_to_state st))) |})
    with (Trans.fg (fst (step (z_to_state st)))).
  apply Trans.trans_step.
Qed.

(** The accumulated constant-time transition matrix over [n] zeta-steps. *)
Definition ztrans_n (n : nat) (st : ZState) : Trans.M2x2 :=
  Trans.prod (map Trans.trans (snd (zstep_n n st))).

(** [ztrans_n (S n)] factors as a [trans] times [ztrans_n n]. *)
Lemma ztrans_n_S n st : {x | ztrans_n (Datatypes.S n) st = Trans.mul (Trans.trans x) (ztrans_n n st)}.
Proof.
  unfold ztrans_n.
  rewrite zstep_n_snd_S.
  cbn.
  exists (snd (zstep (fst (zstep_n n st)))).
  reflexivity.
Qed.

(** [ztrans_n] scales the [(zf, zg)] vector by [2^n].  This is the fact the
    divsteps_59 spec exposes (the C output matrix is [8 * ztrans_n 59], so
    [ap (ztrans_n 59 st) (zfg st) = scale (2^59) (zfg (fst (zstep_n 59 st)))]). *)
Lemma ztrans_n_step n st :
  Trans.scale (2^(Z.of_nat n)) (zfg (fst (zstep_n n st))) = Trans.ap (ztrans_n n st) (zfg st).
Proof.
  induction n.
  - rewrite Z.pow_0_r.
    destruct st; unfold Trans.scale, zfg, Trans.ap, ztrans_n; cbn.
    f_equal; ring.
  - rewrite Nat2Z.inj_succ, Z.pow_succ_r by lia.
    rewrite zstep_n_fst_s.
    assert (Htrans := ztrans_step (fst (zstep_n n st))).
    unfold ztrans_n.
    rewrite zstep_n_snd_S.
    cbn [map Trans.prod fold_right].
    fold (ztrans_n n st).
    rewrite Trans.ap_mul, <- IHn, Trans.ap_scale, Z.mul_comm, Trans.scale_mul.
    f_equal.
    rewrite Htrans.
    reflexivity.
Qed.

(** [det (ztrans_n n st) = 2^n]. *)
Lemma det_ztrans_n n st : Trans.det (ztrans_n n st) = 2^(Z.of_nat n).
Proof.
  revert st.
  induction n; try reflexivity.
  intros st.
  destruct (ztrans_n_S n st) as [x ->].
  rewrite Trans.det_mul, Trans.det_trans, Nat2Z.inj_succ, Z.pow_succ_r by lia.
  congruence.
Qed.

(** [ztrans_n n st] is bounded by [2^n]. *)
Lemma bounded_ztrans_n n st : Trans.bounded (2^(Z.of_nat n)) (ztrans_n n st).
Proof.
  induction n; try apply Trans.bounded_I.
  destruct (ztrans_n_S n st) as [x ->].
  rewrite Nat2Z.inj_succ, Z.pow_succ_r by lia.
  auto using Trans.bounded_mul_trans.
Qed.

(** [ztrans_n] composes across a [zstep_n] split. *)
Lemma ztrans_n_step_n (n m : nat) (st : ZState) :
  Trans.mul (ztrans_n n (fst (zstep_n m st))) (ztrans_n m st) = ztrans_n (n + m) st.
Proof.
  unfold ztrans_n.
  rewrite zstep_n_app_snd, map_app, Trans.prod_app.
  reflexivity.
Qed.

(* ----------------------------------------------------------------- *)
(** *** [update_de] tracking + H-shift form -- [ztrans_hs] / [zupdate_de_eqm]. *)

(** When [2^n | zg st], the accumulated zeta-matrix is the pure H-shift form
    [[2^n 0; 0 1]].  Mirrors [Trans.trans_hs]; needed for the [x = 0 -> d' = 0]
    invariant (with [g = 0] the [update_de] [q]/[v] entries vanish). *)
Lemma ztrans_hs n st : (2^(Z.of_nat n) | zg st) ->
  ztrans_n n st = {| Trans.u := 2^(Z.of_nat n); Trans.v := 0; Trans.q := 0; Trans.r := 1 |}.
Proof.
  induction n;[intros; reflexivity|].
  rewrite Nat2Z.inj_succ, Z.pow_succ_r by lia.
  intros Hg.
  unfold ztrans_n in *.
  rewrite zstep_n_snd_S.
  cbn [map Trans.prod fold_right].
  fold (ztrans_n n st).
  assert (Hg' : (2 ^ Z.of_nat n | zg st)) by (etransitivity;[|apply Hg]; auto with *).
  divide_halving_massage Hg n.
  assert (HzgHs : zg (fst (zstep_n n st)) = zg st / 2^(Z.of_nat n)) by (apply zg_hs; assumption).
  rewrite <- HzgHs in Hg.
  transitivity (Trans.mul (Trans.trans Step.H) {| Trans.u := 2^(Z.of_nat n); Trans.v := 0; Trans.q := 0; Trans.r := 1 |}).
  - (* main goal: equal to the H-product *)
    rewrite <- IHn by assumption.
    f_equal.
    assert (Heven : Zeven (zg (fst (zstep_n n st)))).
    { apply Zeven_bool_iff.
      rewrite Zeven_mod.
      apply Z.eqb_eq.
      assumption. }
    unfold zstep.
    destruct (Zeven_odd_dec (zg (fst (zstep_n n st)))) as [Heven'|Hodd'].
    + reflexivity.
    + elim (Zodd_not_Zeven _ Hodd' Heven).
  - (* side goal: the H-product reduces to the shift form *)
    unfold Trans.mul;cbn;f_equal; ring.
Qed.

(** [update_de] (over [n] zeta-steps, here [62]) tracks [zf] / [zg] modulo [m].
    Matrix-generic like [update_de_eqm]: it generalizes [ztrans_n_step] and runs
    the identical modular algebra. *)
Lemma zupdate_de_eqm m x d e st : Zodd m ->
  eqm m (x * d) (zf st) ->
  eqm m (x * e) (zg st) ->
  eqm m (x * fst (update_de m d e (ztrans_n 62 st))) (zf (fst (zstep_n 62 st))) /\
  eqm m (x * snd (update_de m d e (ztrans_n 62 st))) (zg (fst (zstep_n 62 st))).
Proof.
  intros Hoddm Hf Hg.
  apply (update_de_eqm_core m x d e (ztrans_n 62 st)
           (zf st) (zg st) (zf (fst (zstep_n 62 st))) (zg (fst (zstep_n 62 st)))); try assumption.
  symmetry.
  change (2^62) with (2^Z.of_nat 62).
  exact (ztrans_n_step 62 st).
Qed.

(* ================================================================= *)
(** ** Constant-time driver glue -- [scale_m] / [zstep_n_mod] / [zupdate_de_eqm_gen]. *)

(** *** Matrix scaling -- [Trans.scale_m]. *)

(** Scale every entry of a [2x2] matrix by [c].  The const-time [divsteps_59]
    output matrix is [scale_m 8 (ztrans_n 59 st)] (the C builds [8*I], so the
    accumulated 59-step matrix is pre-multiplied by [8]); the driver needs its
    [ap]/[bounded]/[det] laws to relate the call result to the zeta model.
    Lives in this file rather than the [Trans] module of [divstep_trans], since it
    is only used by the zeta driver; spelled [divstep_zeta.scale_m] downstream. *)
Definition scale_m (c : Z) (m : Trans.M2x2) : Trans.M2x2 :=
{| Trans.u := c * Trans.u m;
   Trans.v := c * Trans.v m;
   Trans.q := c * Trans.q m;
   Trans.r := c * Trans.r m
|}.

(** Applying a scaled matrix scales the result vector: [ap (scale_m c m) vec
    = scale c (ap m vec)]. *)
Lemma ap_scale_m c m vec :
  Trans.ap (scale_m c m) vec = Trans.scale c (Trans.ap m vec).
Proof.
  destruct m, vec.
  unfold Trans.ap, Trans.scale, scale_m; simpl; f_equal; ring.
Qed.

(** The determinant of a scaled matrix scales by [c^2]. *)
Lemma det_scale_m c m : Trans.det (scale_m c m) = c ^ 2 * Trans.det m.
Proof.
  destruct m.
  unfold scale_m, Trans.det; cbn; ring.
Qed.

(** A scaled matrix is bounded by [c * b] when the base is bounded by [b]
    (for [0 < c], the scaling is monotone on the row sums; the strict lower
    bound [-b < u + v] needs [c > 0], not merely [c >= 0]). *)
Lemma bounded_scale_m c b m : 0 < c -> Trans.bounded b m -> Trans.bounded (c * b) (scale_m c m).
Proof.
  intros Hc [[Huv1 Huv2] [Hqr1 Hqr2]].
  unfold Trans.bounded, scale_m; simpl.
  rewrite !Z.abs_mul, (Z.abs_eq c) by lia.
  repeat split.
  - rewrite <-Z.mul_add_distr_l.
    apply Zmult_le_compat_l; lia.
  - replace (c * Trans.u m + c * Trans.v m) with (c * (Trans.u m + Trans.v m)) by ring.
    nia.
  - rewrite <-Z.mul_add_distr_l.
    apply Zmult_le_compat_l; lia.
  - replace (c * Trans.q m + c * Trans.r m) with (c * (Trans.q m + Trans.r m)) by ring.
    nia.
Qed.

(** [scale_m c (ztrans_n (S n))] left-multiplies the emitted step's [trans] onto
    [scale_m c (ztrans_n n)] (scaling commutes with [trans] multiplication). *)
Lemma scale_m_ztrans_n_s (c : Z) (n : nat) (st : ZState) :
  scale_m c (ztrans_n (S n) st) =
  Trans.mul
    (Trans.trans (snd (zstep (fst (zstep_n n st)))))
    (scale_m c (ztrans_n n st)).
Proof.
  unfold ztrans_n.
  rewrite zstep_n_snd_S.
  cbn [map Trans.prod fold_right].
  destruct (Trans.trans (snd (zstep (fst (zstep_n n st)))))
    as [a b cc d].
  destruct (Trans.prod (map Trans.trans (snd (zstep_n n st))))
    as [e ff gg h].
  unfold scale_m, Trans.mul.
  cbn.
  f_equal; ring.
Qed.

(** *** Mod-[2^n]-invariance of [zstep_n] -- [zstep_n_mod]. *)

(** Strong form: two states congruent mod [2^n] in [zf], [zg] with equal [zeta]
    end with equal [zeta] and step list, and stay congruent mod [2^0 = 1]
    (trivially) in [zf], [zg].  The induction needs all four conclusions
    together: the next step's parity test reads [zg mod 2] and its sign test
    reads [zeta], so carrying the running congruence/equality forces the branch
    to agree.  Mirrors the [delta]-machine's [step_n_mod] per-step case split. *)
Lemma zstep_n_mod_strong n st1 st2 :
  eqm (2^Z.of_nat n) (zf st1) (zf st2) ->
  eqm (2^Z.of_nat n) (zg st1) (zg st2) ->
  zeta st1 = zeta st2 ->
  zeta (fst (zstep_n n st1)) = zeta (fst (zstep_n n st2)) /\
  snd (zstep_n n st1) = snd (zstep_n n st2) /\
  eqm 1 (zf (fst (zstep_n n st1))) (zf (fst (zstep_n n st2))) /\
  eqm 1 (zg (fst (zstep_n n st1))) (zg (fst (zstep_n n st2))).
Proof.
  revert st1 st2.
  induction n;[simpl;repeat split;try congruence; try apply eqm_refl|].
  intros st1 st2 Hf Hg Hzeta.
  replace (S n) with (n + 1)%nat by lia.
  rewrite !zstep_n_app_fst, !zstep_n_app_snd.

  (* halving preserves the congruence at one lower power *)
  assert (Hdiv2 : forall a b, eqm (2 ^ Z.of_nat (S n)) a b -> eqm (2 ^ Z.of_nat n) (a / 2) (b / 2)).
  { intros a b.
    unfold eqm.
    rewrite <-!Z.land_ones, <-!(Z.shiftr_div_pow2 _ 1) by lia.
    replace (Z.of_nat n) with (Z.of_nat (S n) - 1) by lia.
    rewrite <-!extra_math.Z_shiftr_ones, <-!Z.shiftr_land by lia.
    congruence. }
  assert (Hg2 : eqm 2 (zg st1) (zg st2)).
  { change 2 with (2^1).
    apply (extra_math.eqm_2_pow_le 1 (Z.of_nat (S n)));[lia|assumption]. }

  (* one [zstep]: same parity (mod 2) and same [zeta] sign select the same branch *)
  simpl (zstep_n 1 st1).
  simpl (zstep_n 1 st2).
  unfold zstep.
  destruct (Zeven_odd_dec (zg st1)) as [Heg1|Hog1];
  destruct (Zeven_odd_dec (zg st2)) as [Heg2|Hog2];
  try solve
  [ exfalso;
    rewrite <-?Zeven_bool_iff, <-?Zodd_bool_iff, ?Zeven_mod, ?Zodd_mod in *;
    repeat match goal with H : (_ =? _) = true |- _ => apply Z.eqb_eq in H end;
    unfold eqm in Hg2; change (2^1) with 2 in Hg2; congruence ].
  - (* H-case: g even -- f kept, g halved, tag H *)
    cbn [fst snd].
    destruct (IHn {| zeta := zeta st1 - 1; zf := zf st1; zg := zg st1 / 2; zodd_f := zodd_f st1 |}
                  {| zeta := zeta st2 - 1; zf := zf st2; zg := zg st2 / 2; zodd_f := zodd_f st2 |}) as [HA [HB [HC HD]]].
    + cbn [zf].
      eapply (extra_math.eqm_2_pow_le (Z.of_nat n) (Z.of_nat (S n)));[lia|assumption].
    + cbn [zg].
      apply Hdiv2.
      assumption.
    + cbn [zeta].
      rewrite Hzeta.
      reflexivity.
    + cbn [zf zg zeta] in *.
      repeat split; try assumption.
      rewrite HB.
      reflexivity.
  - (* odd g: D (zeta < 0) or S (zeta >= 0); the sign branches agree via [Hzeta] *)
    rewrite Hzeta.
    cbn [fst snd].
    destruct (zeta st2 <? 0) eqn:Hz.
    + (* D-case: f := g, g := (g - f)/2, tag D *)
      cbn [fst snd].
      destruct (IHn {| zeta := - zeta st2 - 2; zf := zg st1; zg := (zg st1 - zf st1) / 2; zodd_f := Hog1 |}
                    {| zeta := - zeta st2 - 2; zf := zg st2; zg := (zg st2 - zf st2) / 2; zodd_f := Hog2 |}) as [HA [HB [HC HD]]].
      * cbn [zf].
        eapply (extra_math.eqm_2_pow_le (Z.of_nat n) (Z.of_nat (S n)));[lia|assumption].
      * cbn [zg].
        apply Hdiv2.
        apply Zminus_eqm; assumption.
      * cbn [zeta].
        reflexivity.
      * cbn [zf zg zeta] in *.
        repeat split; try assumption.
        rewrite HB.
        reflexivity.
    + (* S-case: f kept, g := (g + f)/2, tag S *)
      cbn [fst snd].
      destruct (IHn {| zeta := zeta st2 - 1; zf := zf st1; zg := (zg st1 + zf st1) / 2; zodd_f := zodd_f st1 |}
                    {| zeta := zeta st2 - 1; zf := zf st2; zg := (zg st2 + zf st2) / 2; zodd_f := zodd_f st2 |}) as [HA [HB [HC HD]]].
      * cbn [zf].
        eapply (extra_math.eqm_2_pow_le (Z.of_nat n) (Z.of_nat (S n)));[lia|assumption].
      * cbn [zg].
        apply Hdiv2.
        apply Zplus_eqm; assumption.
      * cbn [zeta].
        reflexivity.
      * cbn [zf zg zeta] in *.
        repeat split; try assumption.
        rewrite HB.
        reflexivity.
Qed.

(** The [zstep_n_mod] the const driver uses: equal [zeta] and step list (hence
    equal [ztrans_n]) from a mod-[2^n] match in [zf], [zg]. *)
Lemma zstep_n_mod n st1 st2 :
  eqm (2^Z.of_nat n) (zf st1) (zf st2) ->
  eqm (2^Z.of_nat n) (zg st1) (zg st2) ->
  zeta st1 = zeta st2 ->
  zeta (fst (zstep_n n st1)) = zeta (fst (zstep_n n st2)) /\
  snd (zstep_n n st1) = snd (zstep_n n st2).
Proof.
  intros Hf Hg Hzeta.
  destruct (zstep_n_mod_strong n st1 st2 Hf Hg Hzeta) as [Hz [Hs _]].
  split; assumption.
Qed.

(** *** Matrix-generic [update_de] tracking -- [zupdate_de_eqm_gen]. *)

(** Generalization of [zupdate_de_eqm] to an ARBITRARY matrix [M] and target
    [st'], given the [scale (2^62)] relation [ap M (zfg st) = scale (2^62)
    (zfg st')].  The const driver instantiates [M := scale_m 8 (ztrans_n 59 sti)],
    [st' := fst (zstep_n 59 sti)] -- with [ap_scale_m] + [ztrans_n_step] giving
    [ap (scale_m 8 (ztrans_n 59 sti)) (zfg sti) = scale 8 (scale (2^59)
    (zfg (fst (zstep_n 59 sti)))) = scale (2^62) (...)] (since [8*2^59 = 2^62]).
    It is a direct instance of [update_de_eqm_core] (the [zfg] projections unfold
    definitionally to the raw record vectors the core is stated over). *)
Lemma zupdate_de_eqm_gen m x d e (M : Trans.M2x2) (st st' : ZState) : Zodd m ->
  Trans.ap M (zfg st) = Trans.scale (2^62) (zfg st') ->
  eqm m (x * d) (zf st) ->
  eqm m (x * e) (zg st) ->
  eqm m (x * fst (update_de m d e M)) (zf st') /\
  eqm m (x * snd (update_de m d e M)) (zg st').
Proof.
  intros Hoddm Hrel Hf Hg.
  apply (update_de_eqm_core m x d e M (zf st) (zg st) (zf st') (zg st')); assumption.
Qed.
