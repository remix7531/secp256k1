(** * Verif_scalar_split_lambda: Proof of body_secp256k1_scalar_split_lambda *)
(** Copyright (C) 2026 remix7531
    SPDX-License-Identifier: MIT *)

Require Import secp256k1.vst.base.
Require Import secp256k1.theory.scalar.glv.
Require Import secp256k1.theory.arithmetic.
Require Import secp256k1.contract.helper.notations.
Require Import secp256k1.contract.gprog.scalar.
Require Import secp256k1.tactics.core.
Require Import secp256k1.tactics.int128.
Require Import secp256k1.tactics.scalar.

(* ================================================================= *)
(** ** secp256k1_scalar_split_lambda -- GLV decomposition [r1 + lambda*r2 = k (mod N)]. *)

(* ----------------------------------------------------------------- *)
(** *** Constant tables as [Scalar]s (each table value is [< N]) *)

(** The five global constant tables ([lambda], [-b1], [-b2], [g1], [g2]) are
    stored as [u256_at] (a [UInt256] view), but [mul] / [mul_shift_var] want
    [scalar_at] (a [Scalar] view).  Each table value is [< N], so we package
    it as a [Scalar] and bridge the two views (the limb lists are equal). *)

Program Definition s_lambda : Scalar := mkScalar secp256k1_lambda _.
Next Obligation. unfold secp256k1_lambda, secp256k1_N; lia. Qed.

Program Definition s_minus_b1 : Scalar := mkScalar minus_b1_z _.
Next Obligation. unfold minus_b1_z, secp256k1_N; lia. Qed.

Program Definition s_minus_b2 : Scalar := mkScalar minus_b2_z _.
Next Obligation. unfold minus_b2_z, secp256k1_N; lia. Qed.

Program Definition s_g1 : Scalar := mkScalar g1_z _.
Next Obligation. unfold g1_z, secp256k1_N; lia. Qed.

Program Definition s_g2 : Scalar := mkScalar g2_z _.
Next Obligation. unfold g2_z, secp256k1_N; lia. Qed.

(** The [u256_at] views of the tables coincide with the [scalar_at] views of
    the packaged [Scalar]s (the underlying limb lists are definitionally
    equal, since the values agree). *)
Lemma uint256_to_val_c_lambda : uint256_to_val c_lambda = scalar_to_val s_lambda.
Proof. reflexivity. Qed.

Lemma uint256_to_val_c_minus_b1 :
  uint256_to_val c_minus_b1 = scalar_to_val s_minus_b1.
Proof. reflexivity. Qed.

Lemma uint256_to_val_c_minus_b2 :
  uint256_to_val c_minus_b2 = scalar_to_val s_minus_b2.
Proof. reflexivity. Qed.

Lemma uint256_to_val_c_g1 : uint256_to_val c_g1 = scalar_to_val s_g1.
Proof. reflexivity. Qed.

Lemma uint256_to_val_c_g2 : uint256_to_val c_g2 = scalar_to_val s_g2.
Proof. reflexivity. Qed.

(* ----------------------------------------------------------------- *)
(** *** The model-level result of the C body *)

(** The C computes (writing through [c1], [c2], [r2], [r1] in place):
      c1 = round(k*g1 / 2^384);   c2 = round(k*g2 / 2^384);
      c1 = c1 * (-b1);            c2 = c2 * (-b2);
      r2 = c1 + c2;
      r1 = -(r2 * lambda) + k.
    With each [secp256k1_scalar_*] callee modelled by its functional
    operation, this is the following pair of [Scalar]s (parameterised by the
    two rounded products [c1], [c2], which the callee [mul_shift_var] pins
    down via [scalar_val ci = scalar_mul_shift k s_gi 384]). *)

Definition split_r2 (c1 c2 : Scalar) : Scalar :=
  scalar_add (scalar_mul c1 s_minus_b1) (scalar_mul c2 s_minus_b2).

(** [r1 = -(r2 * lambda) + k], with [r2 = split_r2 c1 c2]. *)
Definition split_r1 (c1 c2 k : Scalar) : Scalar :=
  scalar_add (scalar_negate (scalar_mul (split_r2 c1 c2) s_lambda)) k.

(* ----------------------------------------------------------------- *)
(** *** The congruence  r1 + lambda*r2 == k  (mod N)   [PROVED] *)

(** This is the easy half of the postcondition and holds for *any* [r2]:
    [r1] is defined as [-(r2*lambda) + k mod N], so
    [r1 + lambda*r2 == (-(r2*lambda) + k) + lambda*r2 == k  (mod N)],
    independently of how [r2] was obtained. *)
Lemma split_lambda_congruence : forall (r2 kk : Scalar),
  (scalar_val (scalar_add (scalar_negate (scalar_mul r2 s_lambda)) kk)
     + secp256k1_lambda * scalar_val r2) mod secp256k1_N = scalar_val kk.
Proof.
  intros r2 kk.

  (* Setup: unfold the scalar ops and name the shared product [M = r2*lambda mod N]. *)
  unfold scalar_add, scalar_negate, scalar_mul.
  simpl.
  rewrite Z.add_mod_idemp_l by (unfold secp256k1_N; lia).
  pose proof (scalar_range kk) as Hk.
  set (M := (r2 * secp256k1_lambda) mod secp256k1_N) in *.
  assert (HM : M mod secp256k1_N = M) by (apply Z.mod_mod; unfold secp256k1_N; lia).
  assert (Hlam : (secp256k1_lambda * scalar_val r2) mod secp256k1_N = M)
    by (unfold M; rewrite Z.mul_comm; reflexivity).

  (* Main: regroup so the [+lambda*r2] cancels [M], shed the extra [+N]. *)
  rewrite <- Z.add_assoc.
  rewrite Z.add_mod_idemp_l by (unfold secp256k1_N; lia).
  replace (secp256k1_N - M + (kk + secp256k1_lambda * r2))
    with ((secp256k1_lambda * r2 - M) + kk + secp256k1_N) by ring.
  rewrite <- Z.add_mod_idemp_r by (unfold secp256k1_N; lia).
  rewrite Z_mod_same_full.
  rewrite Z.add_0_r.
  rewrite Zplus_mod.
  rewrite Zminus_mod.
  rewrite Hlam.
  rewrite HM.
  rewrite Z.sub_diag.
  rewrite Zmod_0_l.
  rewrite Z.add_0_l.

  (* Closeout: the residue is just [kk], already in range. *)
  rewrite Zmod_mod.
  apply Z.mod_small.
  exact Hk.
Qed.

(** Instantiated at the body's [r1] / [r2]: the first postcondition conjunct. *)
Corollary split_lambda_congruence_body : forall (c1 c2 k : Scalar),
  (scalar_val (split_r1 c1 c2 k)
     + secp256k1_lambda * scalar_val (split_r2 c1 c2)) mod secp256k1_N
   = scalar_val k.
Proof.
  intros c1 c2 k.
  unfold split_r1.
  apply split_lambda_congruence.
Qed.

(* ================================================================= *)
(** ** 128-bit output bounds -- the GLV lattice estimate, fully over [Z]. *)

(** The two output bounds are the GLV decomposition lattice estimate sketched
    in the C source ([src/scalar_impl.h], [secp256k1_scalar_split_lambda_verify],
    lemmas 1-5).  The upstream argument is over the reals with rounding and
    absolute values; we formalise it entirely over [Z] by clearing the [2^384]
    and [N] denominators, so every step is an exact ring identity or a constant
    inequality closed by [vm_compute].  The two reusable abstract facts -- the
    round-half-up error bound [mul_shift_doubled_error] and the
    linear-combination bound [abs_lincomb_bound] -- live in [theory.scalar.glv]. *)

(* ----------------------------------------------------------------- *)
(** *** The short lattice basis and its derived constants *)

(** The GLV basis [(a1, b1)], [(a2, b2)]: a short basis of the lattice
    [{ (i, j) : i + j*lambda == 0 (mod N) }].  [b1] is negative. *)
Definition a1_z : Z := 0x3086d221a7d46bcde86c90e49284eb15.
Definition a2_z : Z := 0x0114ca50f7a8e2f3f657c1108d9d44cfd8.
Definition b1_z : Z := -0xe4437ed6010e88286f547fa90abfe4c3.
Definition b2_z : Z := 0x3086d221a7d46bcde86c90e49284eb15.

(** Cleared-denominator approximation errors: [g1] approximates [2^384*b2/N]
    and [g2] approximates [2^384*(-b1)/N], so [glvD1], [glvD2] are the (small)
    integer residues [N*gi - (+/-bj)*2^384]. *)
Definition glvD1 : Z := secp256k1_N * g1_z - b2_z * 2 ^ 384.
Definition glvD2 : Z := secp256k1_N * g2_z + b1_z * 2 ^ 384.

(** The defining lattice facts, all concrete -> [vm_compute]. *)
Lemma glv_det : a1_z * b2_z - b1_z * a2_z = secp256k1_N.
Proof. vm_compute. reflexivity. Qed.

Lemma glv_congr1 : (a1_z + b1_z * secp256k1_lambda) mod secp256k1_N = 0.
Proof. vm_compute. reflexivity. Qed.

Lemma glv_congr2 : (a2_z + b2_z * secp256k1_lambda) mod secp256k1_N = 0.
Proof. vm_compute. reflexivity. Qed.

Lemma glv_mb1 : minus_b1_z = - b1_z.
Proof. vm_compute. reflexivity. Qed.

Lemma glv_mb2 : minus_b2_z = secp256k1_N - b2_z.
Proof. vm_compute. reflexivity. Qed.

(** Signs and ranges of the constants. *)
Lemma a1_pos : 0 < a1_z. Proof. unfold a1_z; lia. Qed.
Lemma a2_pos : 0 < a2_z. Proof. unfold a2_z; lia. Qed.
Lemma b1_neg : b1_z < 0. Proof. unfold b1_z; lia. Qed.
Lemma b2_pos : 0 < b2_z. Proof. unfold b2_z; lia. Qed.

(** The two cleared residual inequalities ("round up to [2^128]"): the whole
    point of the chosen short basis.  Concrete -> [vm_compute]. *)
Lemma glv_resid1 :
  a1_z * (secp256k1_N * 2 ^ 383 + 2 ^ 256 * Z.abs glvD1)
  + a2_z * (secp256k1_N * 2 ^ 383 + 2 ^ 256 * Z.abs glvD2)
  < 2 ^ 384 * secp256k1_N * 2 ^ 128.
Proof. vm_compute. reflexivity. Qed.

Lemma glv_resid2 :
  (- b1_z) * (secp256k1_N * 2 ^ 383 + 2 ^ 256 * Z.abs glvD1)
  + b2_z * (secp256k1_N * 2 ^ 383 + 2 ^ 256 * Z.abs glvD2)
  < 2 ^ 384 * secp256k1_N * 2 ^ 128.
Proof. vm_compute. reflexivity. Qed.

(* ----------------------------------------------------------------- *)
(** *** The rounded products and their cleared error bounds (Lemmas 1-2) *)

(** [cval k g = round(k*g / 2^384)] -- the model value of [mul_shift_var k g 384]. *)
Definition cval (kk gg : Z) : Z :=
  (kk * gg) / 2 ^ 384 + ((kk * gg) / 2 ^ 383) mod 2.

(** The doubled rounding error of [cval], from [theory.scalar.glv]. *)
Lemma cval_err : forall kk gg, 0 <= kk -> 0 <= gg ->
  Z.abs (2 ^ 384 * cval kk gg - kk * gg) <= 2 ^ 383.
Proof.
  intros kk gg Hk Hg.
  pose proof (mul_shift_doubled_error (kk * gg) 384 ltac:(lia) ltac:(nia)) as H.
  replace (384 - 1) with 383 in H by lia.
  unfold cval.
  exact H.
Qed.

(** Lemma 1: cleared bound on [N*c1 - k*b2]. *)
Lemma glv_lemma1 : forall kk, 0 <= kk < secp256k1_N ->
  Z.abs (2 ^ 384 * (secp256k1_N * cval kk g1_z - kk * b2_z))
    <= secp256k1_N * 2 ^ 383 + 2 ^ 256 * Z.abs glvD1.
Proof.
  intros kk [Hk0 HkN].
  set (c1 := cval kk g1_z).

  (* Main: the cleared bound is the linear combination [N*err1 - k*glvD1]. *)
  assert (Hlc : 1 * Z.abs (2 ^ 384 * (secp256k1_N * c1 - kk * b2_z))
                <= Z.abs secp256k1_N * (2 ^ 383) + Z.abs kk * Z.abs glvD1).
  { apply (abs_lincomb_bound 1 (2 ^ 384 * (secp256k1_N * c1 - kk * b2_z))
             secp256k1_N kk (2 ^ 384 * c1 - kk * g1_z) glvD1 (2 ^ 383) (Z.abs glvD1)).
    - (* factor: 0 <= 1 *)
      lia.
    - (* ring identity: combination matches the cleared residue *)
      unfold glvD1. ring.
    - (* per-term error: |2^384*c1 - k*g1| <= 2^383 via [cval_err] *)
      unfold c1. apply cval_err; [lia | unfold g1_z; lia].
    - (* residue bound: |glvD1| <= |glvD1| *)
      apply Z.le_refl. }

  (* Closeout: drop the [*1] factor, replace [|k|] by [N < 2^256]. *)
  rewrite Z.mul_1_l in Hlc.
  rewrite (Z.abs_eq secp256k1_N) in Hlc by lia.
  rewrite (Z.abs_eq kk) in Hlc by lia.
  eapply Z.le_trans; [exact Hlc | ].
  apply Z.add_le_mono; [apply Z.le_refl | ].
  apply Z.mul_le_mono_nonneg_r; [apply Z.abs_nonneg | ].
  pose proof secp256k1_N_range. lia.
Qed.

(** Lemma 2: cleared bound on [N*c2 - k*(-b1)]. *)
Lemma glv_lemma2 : forall kk, 0 <= kk < secp256k1_N ->
  Z.abs (2 ^ 384 * (secp256k1_N * cval kk g2_z + kk * b1_z))
    <= secp256k1_N * 2 ^ 383 + 2 ^ 256 * Z.abs glvD2.
Proof.
  intros kk [Hk0 HkN].
  set (c2 := cval kk g2_z).

  (* Main: the cleared bound is the linear combination [N*err2 - k*glvD2]. *)
  assert (Hlc : 1 * Z.abs (2 ^ 384 * (secp256k1_N * c2 + kk * b1_z))
                <= Z.abs secp256k1_N * (2 ^ 383) + Z.abs kk * Z.abs glvD2).
  { apply (abs_lincomb_bound 1 (2 ^ 384 * (secp256k1_N * c2 + kk * b1_z))
             secp256k1_N kk (2 ^ 384 * c2 - kk * g2_z) glvD2 (2 ^ 383) (Z.abs glvD2)).
    - (* factor: 0 <= 1 *)
      lia.
    - (* ring identity: combination matches the cleared residue *)
      unfold glvD2. ring.
    - (* per-term error: |2^384*c2 - k*g2| <= 2^383 via [cval_err] *)
      unfold c2. apply cval_err; [lia | unfold g2_z; lia].
    - (* residue bound: |glvD2| <= |glvD2| *)
      apply Z.le_refl. }

  (* Closeout: drop the [*1] factor, replace [|k|] by [N < 2^256]. *)
  rewrite Z.mul_1_l in Hlc.
  rewrite (Z.abs_eq secp256k1_N) in Hlc by lia.
  rewrite (Z.abs_eq kk) in Hlc by lia.
  eapply Z.le_trans; [exact Hlc | ].
  apply Z.add_le_mono; [apply Z.le_refl | ].
  apply Z.mul_le_mono_nonneg_r; [apply Z.abs_nonneg | ].
  pose proof secp256k1_N_range. lia.
Qed.

(* ----------------------------------------------------------------- *)
(** *** The lattice coordinates [k1], [k2] and their 128-bit bounds (Lemmas 3-4) *)

(** The lattice coordinates of [k] in the short basis: [k1] / [k2]. *)
Definition glvk1 (kk c1 c2 : Z) : Z := kk - c1 * a1_z - c2 * a2_z.
Definition glvk2 (c1 c2 : Z) : Z := - c1 * b1_z - c2 * b2_z.

(** Lemma 3: [|k1| < 2^128].  [2^384*N*k1] is the linear combination
    [(-a1)*E1 + (-a2)*E2] (a ring identity given the determinant [glv_det]);
    bound the two pieces by Lemmas 1-2, then the cleared residual [glv_resid1]
    closes the [< 2^128] after cancelling the positive factor [2^384*N]. *)
Lemma glv_k1_bound : forall kk, 0 <= kk < secp256k1_N ->
  Z.abs (glvk1 kk (cval kk g1_z) (cval kk g2_z)) < 2 ^ 128.
Proof.
  intros kk [Hk0 HkN].

  (* Setup: name the rounded products and the positive cancel factor [M = 2^384*N]. *)
  set (c1 := cval kk g1_z) in *.
  set (c2 := cval kk g2_z) in *.
  set (M := 2 ^ 384 * secp256k1_N) in *.
  assert (HM : 0 < M).
  { unfold M. apply Z.mul_pos_pos;
    [apply Z.pow_pos_nonneg; lia | pose proof secp256k1_N_range; lia]. }

  (* Main: bound [M*|k1|] by the linear combination [(-a1)*E1 + (-a2)*E2]. *)
  assert (Hbound : M * Z.abs (glvk1 kk c1 c2)
                   <= a1_z * (secp256k1_N * 2 ^ 383 + 2 ^ 256 * Z.abs glvD1)
                      + a2_z * (secp256k1_N * 2 ^ 383 + 2 ^ 256 * Z.abs glvD2)).
  { eapply Z.le_trans.
    - apply (abs_lincomb_bound M (glvk1 kk c1 c2) (- a1_z) (- a2_z)
               (2 ^ 384 * (secp256k1_N * c1 - kk * b2_z))
               (2 ^ 384 * (secp256k1_N * c2 + kk * b1_z))
               (secp256k1_N * 2 ^ 383 + 2 ^ 256 * Z.abs glvD1)
               (secp256k1_N * 2 ^ 383 + 2 ^ 256 * Z.abs glvD2)).
      + (* factor: 0 < M *)
        exact HM.
      + (* ring identity: M*k1 = (-a1)*E1 + (-a2)*E2 (needs [glv_det]) *)
        unfold glvk1, M. set (P := 2 ^ 384). rewrite <- glv_det. ring.
      + (* piece 1: Lemma 1 bounds E1 *)
        apply glv_lemma1; lia.
      + (* piece 2: Lemma 2 bounds E2 *)
        apply glv_lemma2; lia.
    - (* turn the [|-a_i|] coefficients positive *)
      rewrite (Z.abs_neq (- a1_z)) by (pose proof a1_pos; lia).
      rewrite (Z.abs_neq (- a2_z)) by (pose proof a2_pos; lia).
      lia. }

  (* Closeout: the cleared residual [glv_resid1] gives [M*|k1| < M*2^128]; cancel [M]. *)
  assert (Hlt : M * Z.abs (glvk1 kk c1 c2) < M * 2 ^ 128).
  { eapply Z.le_lt_trans; [exact Hbound | ].
    unfold M. exact glv_resid1. }
  apply (proj2 (Z.mul_lt_mono_pos_l M (Z.abs (glvk1 kk c1 c2)) (2 ^ 128) HM)).
  exact Hlt.
Qed.

(** Lemma 4: [|k2| < 2^128].  Mirrors Lemma 3 with coefficients [(-b1), (-b2)]
    and the residual [glv_resid2]. *)
Lemma glv_k2_bound : forall kk, 0 <= kk < secp256k1_N ->
  Z.abs (glvk2 (cval kk g1_z) (cval kk g2_z)) < 2 ^ 128.
Proof.
  intros kk [Hk0 HkN].

  (* Setup: name the rounded products and the positive cancel factor [M = 2^384*N]. *)
  set (c1 := cval kk g1_z) in *.
  set (c2 := cval kk g2_z) in *.
  set (M := 2 ^ 384 * secp256k1_N) in *.
  assert (HM : 0 < M).
  { unfold M. apply Z.mul_pos_pos;
    [apply Z.pow_pos_nonneg; lia | pose proof secp256k1_N_range; lia]. }

  (* Main: bound [M*|k2|] by the linear combination [(-b1)*E1 + (-b2)*E2]. *)
  assert (Hbound : M * Z.abs (glvk2 c1 c2)
                   <= (- b1_z) * (secp256k1_N * 2 ^ 383 + 2 ^ 256 * Z.abs glvD1)
                      + b2_z * (secp256k1_N * 2 ^ 383 + 2 ^ 256 * Z.abs glvD2)).
  { eapply Z.le_trans.
    - apply (abs_lincomb_bound M (glvk2 c1 c2) (- b1_z) (- b2_z)
               (2 ^ 384 * (secp256k1_N * c1 - kk * b2_z))
               (2 ^ 384 * (secp256k1_N * c2 + kk * b1_z))
               (secp256k1_N * 2 ^ 383 + 2 ^ 256 * Z.abs glvD1)
               (secp256k1_N * 2 ^ 383 + 2 ^ 256 * Z.abs glvD2)).
      + (* factor: 0 < M *)
        exact HM.
      + (* ring identity: M*k2 = (-b1)*E1 + (-b2)*E2 (needs [glv_det]) *)
        unfold glvk2, M. set (P := 2 ^ 384). rewrite <- glv_det. ring.
      + (* piece 1: Lemma 1 bounds E1 *)
        apply glv_lemma1; lia.
      + (* piece 2: Lemma 2 bounds E2 *)
        apply glv_lemma2; lia.
    - (* turn the [|-b_i|] coefficients positive ([b1 < 0], [b2 > 0]) *)
      rewrite (Z.abs_eq (- b1_z)) by (pose proof b1_neg; lia).
      rewrite (Z.abs_neq (- b2_z)) by (pose proof b2_pos; lia).
      lia. }

  (* Closeout: the cleared residual [glv_resid2] gives [M*|k2| < M*2^128]; cancel [M]. *)
  assert (Hlt : M * Z.abs (glvk2 c1 c2) < M * 2 ^ 128).
  { eapply Z.le_lt_trans; [exact Hbound | ].
    unfold M. exact glv_resid2. }
  apply (proj2 (Z.mul_lt_mono_pos_l M (Z.abs (glvk2 c1 c2)) (2 ^ 128) HM)).
  exact Hlt.
Qed.

(* ----------------------------------------------------------------- *)
(** *** The congruences  r2 == k2,  r1 == k1  (mod N)  (Lemma 5) *)

(** [r2 = c1*(-b1) + c2*(-b2) = k2  (mod N)], using [minus_bi == -bi (mod N)]. *)
Lemma split_r2_mod : forall x y,
  (x * minus_b1_z + y * minus_b2_z) mod secp256k1_N = glvk2 x y mod secp256k1_N.
Proof.
  intros x y.
  rewrite glv_mb1, glv_mb2.
  replace (x * (- b1_z) + y * (secp256k1_N - b2_z))
     with (glvk2 x y + y * secp256k1_N) by (unfold glvk2; ring).
  rewrite Z_mod_plus_full.
  reflexivity.
Qed.

(** [r1 = k - r2*lambda = k1  (mod N)], using [r2 == k2] and the two
    congruences [ai + bi*lambda == 0 (mod N)]. *)
Lemma split_r1_mod_core : forall R2 k' x y,
  R2 mod secp256k1_N = glvk2 x y mod secp256k1_N ->
  ((secp256k1_N - (R2 * secp256k1_lambda) mod secp256k1_N) mod secp256k1_N
     + k') mod secp256k1_N
   = glvk1 k' x y mod secp256k1_N.
Proof.
  intros R2 k' x y H.
  pose proof secp256k1_N_range.

  (* Setup: shed the extra [+N], then push the [r2 == k2] hypothesis inside. *)
  rewrite Z.add_mod_idemp_l by lia.
  replace (secp256k1_N - (R2 * secp256k1_lambda) mod secp256k1_N + k')
     with ((k' - (R2 * secp256k1_lambda) mod secp256k1_N) + 1 * secp256k1_N) by ring.
  rewrite Z_mod_plus_full.
  rewrite Zminus_mod_idemp_r.
  rewrite (Zminus_mod k' (R2 * secp256k1_lambda)).
  rewrite <- (Z.mul_mod_idemp_l R2 secp256k1_lambda secp256k1_N) by lia.
  rewrite H.
  rewrite (Z.mul_mod_idemp_l (glvk2 x y) secp256k1_lambda secp256k1_N) by lia.
  rewrite <- (Zminus_mod k' (glvk2 x y * secp256k1_lambda)).

  (* Main: [k' - k2*lambda = k1 + (x*(a1+b1*lambda) + y*(a2+b2*lambda))]. *)
  assert (HAB : k' - glvk2 x y * secp256k1_lambda
                = glvk1 k' x y + (x * (a1_z + b1_z * secp256k1_lambda)
                                  + y * (a2_z + b2_z * secp256k1_lambda))).
  { unfold glvk1, glvk2. ring. }
  rewrite HAB.

  (* Closeout: the two congruences [ai + bi*lambda == 0] kill the correction term. *)
  rewrite Z.add_mod by lia.
  rewrite (Z.add_mod (x * (a1_z + b1_z * secp256k1_lambda))
                     (y * (a2_z + b2_z * secp256k1_lambda)) secp256k1_N) by lia.
  rewrite (Z.mul_mod x (a1_z + b1_z * secp256k1_lambda) secp256k1_N) by lia.
  rewrite glv_congr1.
  rewrite Z.mul_0_r, Zmod_0_l.
  rewrite (Z.mul_mod y (a2_z + b2_z * secp256k1_lambda) secp256k1_N) by lia.
  rewrite glv_congr2.
  rewrite Z.mul_0_r, Zmod_0_l.
  rewrite Z.add_0_r, Zmod_mod.
  reflexivity.
Qed.

(* ----------------------------------------------------------------- *)
(** *** Bridges from the C [Scalar] operations to the [Z] coordinates *)

(** [mul_shift_var k gi 384] evaluates to [cval (k) gi]. *)
Lemma cval_mul_shift1 : forall k : Scalar,
  scalar_mul_shift k s_g1 384 = cval (scalar_val k) g1_z.
Proof. intros k. reflexivity. Qed.

Lemma cval_mul_shift2 : forall k : Scalar,
  scalar_mul_shift k s_g2 384 = cval (scalar_val k) g2_z.
Proof. intros k. reflexivity. Qed.

(** Unfold the C [Scalar] result of [split_r2] / [split_r1] to its [Z] value. *)
Lemma split_r2_val : forall c1 c2 : Scalar,
  scalar_val (split_r2 c1 c2)
   = glvk2 (scalar_val c1) (scalar_val c2) mod secp256k1_N.
Proof.
  intros c1 c2.
  unfold split_r2, scalar_add, scalar_mul.
  cbn [scalar_val].
  rewrite <- Z.add_mod by (unfold secp256k1_N; lia).
  apply split_r2_mod.
Qed.

Lemma split_r1_val : forall c1 c2 k : Scalar,
  scalar_val (split_r1 c1 c2 k)
   = ((secp256k1_N - (scalar_val (split_r2 c1 c2) * secp256k1_lambda) mod secp256k1_N)
        mod secp256k1_N + scalar_val k) mod secp256k1_N.
Proof.
  intros c1 c2 k.
  unfold split_r1, scalar_add, scalar_negate, scalar_mul.
  cbn [scalar_val].
  reflexivity.
Qed.

(* ----------------------------------------------------------------- *)
(** *** The two output bounds [PROVED] *)

(** The two rounding hypotheses [scalar_val ci = scalar_mul_shift k s_gi 384]
    are exactly the [mul_shift_var] postconditions established by the two
    [forward_call]s in the body, so the bounds are stated relative to the real
    [c1], [c2] (not arbitrary scalars). *)
Lemma split_r2_bound : forall (c1 c2 k : Scalar),
  scalar_val c1 = scalar_mul_shift k s_g1 384 ->
  scalar_val c2 = scalar_mul_shift k s_g2 384 ->
  (scalar_val (split_r2 c1 c2) < 2 ^ 128
   \/ secp256k1_N - scalar_val (split_r2 c1 c2) < 2 ^ 128)%Z.
Proof.
  intros c1 c2 k Hc1 Hc2.

  (* Reduce [r2] to [k2 mod N], then discharge via Lemma 4 and the window split. *)
  rewrite split_r2_val.
  rewrite Hc1, Hc2.
  rewrite cval_mul_shift1, cval_mul_shift2.
  apply small_abs_mod_window.
  - pose proof secp256k1_N_range; lia.
  - pose proof N_gt_2_128; lia.
  - apply glv_k2_bound.
    apply scalar_range.
Qed.

Lemma split_r1_bound : forall (c1 c2 k : Scalar),
  scalar_val c1 = scalar_mul_shift k s_g1 384 ->
  scalar_val c2 = scalar_mul_shift k s_g2 384 ->
  (scalar_val (split_r1 c1 c2 k) < 2 ^ 128
   \/ secp256k1_N - scalar_val (split_r1 c1 c2 k) < 2 ^ 128)%Z.
Proof.
  intros c1 c2 k Hc1 Hc2.
  rewrite split_r1_val.

  (* Feed [r2 == k2 (mod N)] to [split_r1_mod_core] so [r1] reduces to [k1 mod N]. *)
  assert (HR2 : scalar_val (split_r2 c1 c2) mod secp256k1_N
                = glvk2 (cval (scalar_val k) g1_z) (cval (scalar_val k) g2_z)
                    mod secp256k1_N).
  { rewrite split_r2_val.
    rewrite Zmod_mod.
    rewrite Hc1, Hc2.
    rewrite cval_mul_shift1, cval_mul_shift2.
    reflexivity. }
  rewrite (split_r1_mod_core (scalar_val (split_r2 c1 c2)) (scalar_val k)
             (cval (scalar_val k) g1_z) (cval (scalar_val k) g2_z) HR2).

  (* Then discharge via Lemma 3 and the window split. *)
  apply small_abs_mod_window.
  - pose proof secp256k1_N_range; lia.
  - pose proof N_gt_2_128; lia.
  - apply glv_k1_bound.
    apply scalar_range.
Qed.

(* ================================================================= *)
(** ** Body proof -- the in-place [mul]/[add]/[negate] decomposition pipeline.

    The C body calls the scalar primitives partly IN PLACE:

        secp256k1_scalar_mul(&c1, &c1, &minus_b1);   (* r == a, alias *)
        secp256k1_scalar_mul(&c2, &c2, &minus_b2);   (* r == a, alias *)
        secp256k1_scalar_add(r2, &c1, &c2);          (* distinct *)
        secp256k1_scalar_mul(r1, r2, &const_lambda); (* distinct *)
        secp256k1_scalar_negate(r1, r1);             (* r == a, alias *)
        secp256k1_scalar_add(r1, r1, k);             (* r == a, alias *)

    The four in-place calls pass [alias = true] to the alias-aware [mul] /
    [add] / [negate] funspecs (a single writable chunk backs the coinciding
    result and first argument); the two distinct calls pass [alias = false].
    Each [forward_call] leaves a frame entailment closed by [cancel].

    The result scalars are exactly the model terms [split_r1] / [split_r2]
    (threaded through [Hr1f_eq] / [Hr2v_eq]); the three postcondition
    conjuncts then close via [split_lambda_congruence_body], [split_r1_bound],
    [split_r2_bound]. *)
Lemma body_secp256k1_scalar_split_lambda:
  semax_body Vprog Gprog
    f_secp256k1_scalar_split_lambda spec_secp256k1_scalar_split_lambda.
Proof.
  start_function.

  (* ===== Bridge: the constant tables, viewed as [Scalar]s ===== *)
  rewrite uint256_to_val_c_g1.
  rewrite uint256_to_val_c_g2.
  rewrite uint256_to_val_c_minus_b1.
  rewrite uint256_to_val_c_minus_b2.
  rewrite uint256_to_val_c_lambda.

  (* ===== Phase 1: the two rounded multiply-shifts ===== *)

  (* secp256k1_scalar_mul_shift_var(&c1, k, &g1, 384) *)
  forward_call (v_c1, k_ptr, gv _g1, 384, k, s_g1, Tsh, shk, sh_tab).
  Intros c1.
  rename H into Hc1.

  (* secp256k1_scalar_mul_shift_var(&c2, k, &g2, 384) *)
  forward_call (v_c2, k_ptr, gv _g2, 384, k, s_g2, Tsh, shk, sh_tab).
  Intros c2.
  rename H into Hc2.

  (* ===== Phase 2: the lattice combination ===== *)

  (* secp256k1_scalar_mul(&c1, &c1, &minus_b1): in place (alias) *)
  forward_call (v_c1, v_c1, gv _minus_b1, c1, s_minus_b1, Tsh, Tsh, sh_tab, true).
  cancel.
  Intros c1m.
  rename H into Hc1m.

  (* secp256k1_scalar_mul(&c2, &c2, &minus_b2): in place (alias) *)
  forward_call (v_c2, v_c2, gv _minus_b2, c2, s_minus_b2, Tsh, Tsh, sh_tab, true).
  cancel.
  Intros c2m.
  rename H into Hc2m.

  (* secp256k1_scalar_add(r2, &c1, &c2): distinct *)
  forward_call (r2_ptr, v_c1, v_c2, c1m, c2m, sh2, Tsh, Tsh, false).
  cancel.
  Intros r2v.
  rename H into Hr2.

  (* secp256k1_scalar_mul(r1, r2, &secp256k1_const_lambda): distinct *)
  forward_call (r1_ptr, r2_ptr, gv _secp256k1_const_lambda, r2v, s_lambda, sh1, sh2, sh_tab, false).
  cancel.
  Intros r1m.
  rename H into Hr1m.

  (* secp256k1_scalar_negate(r1, r1): in place (alias).  negate's POST is now the
     additive-inverse PROPERTY [(r1m + r1n) mod N = 0]; recover the [r1n =
     scalar_negate r1m] value form via uniqueness, so the rest of the proof is
     unchanged. *)
  forward_call (r1_ptr, r1_ptr, r1m, sh1, sh1, true).
  Intros r1n.
  rename H into Hr1n.
  apply scalar_negate_unique in Hr1n.

  (* secp256k1_scalar_add(r1, r1, k): in place (alias) *)
  forward_call (r1_ptr, r1_ptr, k_ptr, r1n, k, sh1, sh1, shk, true).
  cancel.
  Intros r1f.
  rename H into Hr1f.

  (* ===== Phase 3: identify the results with [split_r2] / [split_r1] ===== *)

  assert (Hr2v_eq : r2v = split_r2 c1 c2).
  { unfold split_r2. rewrite Hr2, Hc1m, Hc2m. reflexivity. }
  assert (Hr1f_eq : r1f = split_r1 c1 c2 k).
  { unfold split_r1. rewrite Hr1f, Hr1n, Hr1m, Hr2v_eq. reflexivity. }

  (* ===== Phase 4: postcondition ===== *)

  Exists r1f r2v.
  entailer!.
  rewrite Hr1f_eq.
  rewrite Hr2v_eq.
  split; [ | split].
  - (* congruence  r1 + lambda*r2 == k  (mod N) *)
    apply split_lambda_congruence_body.
  - (* |r1| < 2^128 (signed) *)
    apply split_r1_bound; assumption.
  - (* |r2| < 2^128 (signed) *)
    apply (split_r2_bound c1 c2 k); assumption.
Qed.
