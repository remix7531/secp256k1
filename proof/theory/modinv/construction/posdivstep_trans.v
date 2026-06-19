(** * theory.modinv.construction.posdivstep_trans: the positive-divstep
    transition-matrix algebra -- the per-step matrices ([ptrans]) and their
    [n]-step product ([ptrans_n]), with the determinant ([abs_det_ptrans_n])
    and row-sum bound ([bounded_ptrans_n]) the driver needs. *)
(** Copyright (C) 2026 remix7531
    Adapted from BlockstreamResearch/simplicity Coq/C/divstep.v
    (commit c1dddedd), Copyright (c) 2018 Blockstream, originally MIT.
    Upstream notice reproduced in proof/README.md.
    SPDX-License-Identifier: MIT *)

(** The matrix section of the positive-divstep machine in [posdivstep]: it
    reuses [Module Trans] from [divstep_trans] wholesale and mirrors that
    file's divstep-specific half ([trans] .. [trans_n_step_n]) one-for-one.

    The [D] matrix is the only difference.  A positive divstep replaces
    [(f, g)] by [(g, (g + f) / 2)] with no negation, so its [q] entry is [1]
    rather than [-1] and its determinant is [-2] rather than [2].  Hence
    [Trans.det_trans] (determinant exactly [2]) does not carry over and
    becomes [abs_det_ptrans] here -- which is what the C's own comment claims,
    and why the C checks the aggregate against [+-2^62] rather than [2^62]. *)

Require Import ZArith.
Require Import Lia.
Require Import List.

Require Import secp256k1.theory.modinv.construction.divstep.
Require Import secp256k1.theory.modinv.construction.divstep_trans.
Require Import secp256k1.theory.modinv.construction.posdivstep.

Open Scope list_scope.
Open Scope Z_scope.
Arguments Z.add !x !y.
Arguments Z.sub !m !n.
Arguments Z.mul !x !y.

(* ================================================================= *)
(** ** Single-step matrices -- [ptrans] / [pfg] / [ptrans_step]. *)

(** The transition matrix of a single positive divstep.  [D] is the branch
    that differs from [Trans.trans]: [q = 1], not [-1]. *)
Definition ptrans (s : divstep.Step) : Trans.M2x2 :=
match s with
| divstep.Step.H => {| Trans.u := 2; Trans.v := 0; Trans.q := 0; Trans.r := 1 |}
| divstep.Step.D => {| Trans.u := 0; Trans.v := 2; Trans.q := 1; Trans.r := 1 |}
| divstep.Step.S => {| Trans.u := 2; Trans.v := 0; Trans.q := 1; Trans.r := 1 |}
end.

(** The [(f, g)] vector of a state (mirrors [Trans.fg]). *)
Definition pfg (st : posdivstep.State) : Trans.V2 :=
{| Trans.x := posdivstep.f st;
   Trans.y := posdivstep.g st
|}.

(** One positive divstep doubles the [(f, g)] vector, realized by [ptrans]. *)
Lemma ptrans_step st :
  Trans.scale 2 (pfg (fst (pstep st))) = Trans.ap (ptrans (snd (pstep st))) (pfg st).
Proof.
  destruct (spec st);
    unfold Trans.scale, Trans.ap, pfg;
    cbn;
    f_equal;
    ring.
Qed.

(** Each single-step matrix has determinant [2] ([H], [S]) or [-2] ([D]). *)
Lemma det_ptrans s : Trans.det (ptrans s) = 2 \/ Trans.det (ptrans s) = -2.
Proof.
  destruct s.
  - (* D: the un-negated swap, determinant -2 *)
    right.
    reflexivity.
  - (* S: determinant 2 *)
    left.
    reflexivity.
  - (* H: determinant 2 *)
    left.
    reflexivity.
Qed.

(** The determinant of a single-step matrix has absolute value [2]. *)
Lemma abs_det_ptrans s : Z.abs (Trans.det (ptrans s)) = 2.
Proof.
  destruct s; reflexivity.
Qed.

(** Left-multiplying by a [ptrans] doubles the bound.  [Trans.bounded_mul_trans]
    is stated for the divstep [Trans.trans] and does not apply. *)
Lemma bounded_mul_ptrans b m s :
  Trans.bounded b m -> Trans.bounded (2 * b) (Trans.mul (ptrans s) m).
Proof.
  destruct m as [mu mv mq mr].
  intros [Huv Hqr].
  simpl in *.
  destruct s;
    unfold Trans.bounded;
    simpl;
    lia.
Qed.

(* ================================================================= *)
(** ** Accumulated matrices -- [ptrans_n] / [ptrans_n_step] / [bounded_ptrans_n]. *)

(** The accumulated transition matrix over [n] positive divsteps. *)
Definition ptrans_n (n : nat) (st : posdivstep.State) : Trans.M2x2 :=
  Trans.prod (map ptrans (snd (pstep_n n st))).

(** [ptrans_n (S n)] factors as a [ptrans] times [ptrans_n n]. *)
Lemma ptrans_n_S n st :
  {s | ptrans_n (S n) st = Trans.mul (ptrans s) (ptrans_n n st)}.
Proof.
  unfold ptrans_n.
  simpl.
  destruct (pstep_n n st) as [st0 xs] eqn:Hxs.
  destruct (pstep st0) as [st1 s].
  exists s.
  reflexivity.
Qed.

(** [ptrans_n] scales the [(f, g)] vector by [2^n]. *)
Lemma ptrans_n_step n st :
  Trans.scale (2 ^ Z.of_nat n) (pfg (fst (pstep_n n st)))
    = Trans.ap (ptrans_n n st) (pfg st).
Proof.
  induction n.
  - (* base: no step, the identity matrix *)
    rewrite Z.pow_0_r.
    destruct st.
    unfold Trans.scale, pfg, Trans.ap.
    cbn.
    f_equal; ring.
  - (* step: peel the last [pstep] off the front of the product *)
    rewrite Nat2Z.inj_succ, Z.pow_succ_r by lia.
    unfold ptrans_n in *.
    simpl.
    destruct (pstep_n n st) as [st0 xs].
    simpl in *.
    assert (Hstep := ptrans_step st0).
    destruct (pstep st0) as [st1 s].
    simpl in *.
    rewrite Trans.ap_mul, <- IHn, Trans.ap_scale, Z.mul_comm, Trans.scale_mul by auto.
    f_equal.
    apply Hstep.
Qed.

(** [Z.abs (det (ptrans_n n st)) = 2^n]: the aggregate determinant is [+-2^n],
    which is the C's [secp256k1_modinv64_det_check_pow2(t, 62, 1)]. *)
Lemma abs_det_ptrans_n n st :
  Z.abs (Trans.det (ptrans_n n st)) = 2 ^ Z.of_nat n.
Proof.
  revert st.
  induction n.
  - (* base: the empty product is the identity, determinant 1 *)
    intros st.
    reflexivity.
  - (* step: one more factor of absolute determinant 2 *)
    intros st.
    destruct (ptrans_n_S n st) as [s ->].
    rewrite Trans.det_mul, Z.abs_mul, abs_det_ptrans, Nat2Z.inj_succ, Z.pow_succ_r by lia.
    congruence.
Qed.

(** [ptrans_n n st] is bounded by [2^n]. *)
Lemma bounded_ptrans_n n st : Trans.bounded (2 ^ Z.of_nat n) (ptrans_n n st).
Proof.
  induction n.
  - (* base: the empty product is the identity *)
    apply Trans.bounded_I.
  - (* step: one more [ptrans] factor doubles the bound *)
    destruct (ptrans_n_S n st) as [s ->].
    rewrite Nat2Z.inj_succ, Z.pow_succ_r by lia.
    auto using bounded_mul_ptrans.
Qed.

(* ----------------------------------------------------------------- *)
(** *** Composition across a step split. *)

(** The [pstep_n] split: [n + m] steps are the last [n] applied to the state
    after the first [m], with the step lists concatenated.  The local mirror of
    [divstep.step_n_app]; it lives here rather than in [posdivstep] because
    [ptrans_n_step_n] is its only consumer, so fold it into [posdivstep] if
    that file ever grows its own composition lemmas. *)
Lemma pstep_n_app (n m : nat) (st : posdivstep.State) :
  pstep_n (n + m) st = let st1 := pstep_n m st in
    (fst (pstep_n n (fst st1)), snd (pstep_n n (fst st1)) ++ snd st1).
Proof.
  induction n.
  - (* base: no extra steps, the left factor is empty *)
    change (0 + m)%nat with m.
    destruct (pstep_n m st).
    reflexivity.
  - (* step: the same head [pstep] on both sides *)
    cbn.
    rewrite IHn.
    cbn.
    destruct (pstep_n n (fst (pstep_n m st))) as [st0 xs].
    cbn.
    destruct (pstep st0) as [st1 x].
    reflexivity.
Qed.

(** Step-list projection of [pstep_n_app]. *)
Lemma pstep_n_app_snd (n m : nat) (st : posdivstep.State) :
  snd (pstep_n (n + m) st)
    = snd (pstep_n n (fst (pstep_n m st))) ++ snd (pstep_n m st).
Proof.
  rewrite pstep_n_app.
  reflexivity.
Qed.

(** [ptrans_n] composes across a [pstep_n] split. *)
Lemma ptrans_n_step_n (n m : nat) (st : posdivstep.State) :
  Trans.mul (ptrans_n n (fst (pstep_n m st))) (ptrans_n m st) = ptrans_n (n + m) st.
Proof.
  unfold ptrans_n.
  rewrite pstep_n_app_snd, map_app, Trans.prod_app.
  reflexivity.
Qed.
