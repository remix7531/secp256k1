(** * vst.modinv.verif.impl.modinv64_update_fg_62: body proof for secp256k1_modinv64_update_fg_62. *)
(** Copyright (C) 2026 remix7531
    Ported from BlockstreamResearch/simplicity Coq/C/secp256k1/verif_modinv64_impl.v
    (commit c1dddedd), Copyright (c) 2018 Blockstream, originally MIT.
    Upstream notice reproduced in proof/README.md.
    SPDX-License-Identifier: MIT *)

Require Import secp256k1.vst.base.
Require Import secp256k1.vst.int128.contract.
Require Import secp256k1.theory.int128.int128.
Require Import secp256k1.vst.helper.notations.
Require Import secp256k1.vst.modinv.impl.
Require Import secp256k1.vst.gprog.
Require Import secp256k1.theory.integers.extra_math.
Require Import secp256k1.theory.modinv.bounds.
Require Import secp256k1.theory.modinv.divsteps.theory.
Require Import secp256k1.theory.modinv.divsteps.bound724.
Require Import secp256k1.theory.modinv.construction.inverse.
Require secp256k1.theory.modinv.construction.divstep.
Require secp256k1.theory.modinv.construction.divstep_trans.
Require Import secp256k1.vst.tactics.core.
Require Import secp256k1.vst.tactics.hygiene.

(* ================================================================= *)
(** ** secp256k1_modinv64_update_fg_62 -- [(mtx * [f,g]) / 2^62] on 5 limbs. *)

(** The fixed 5-limb, fully unrolled counterpart of [..._update_fg_62_var]
    ([len = 5]): the [..._var] loop is unrolled into four explicit limb blocks
    (storing output limbs 0..3) plus the top-limb tail (output limb 4), with the
    generic-matrix [reprn 5 ((u*f+v*g)/2^62)] / [reprn 5 ((q*f+r*g)/2^62)]
    floor-division postcondition. *)
Lemma body_secp256k1_modinv64_update_fg_62:
  semax_body Vprog Gprog
    f_secp256k1_modinv64_update_fg_62 spec_secp256k1_modinv64_update_fg_62.
Proof.
  start_function.

  (* ===== Setup: limb lengths, load M62 + f0..f4 / g0..g4 / u,v,q,r ===== *)

  rename H into Hff.
  rename H0 into Hgg.

  assert (Hlf : Zlength (Signed62.reprn 5 ff) = 5) by apply Signed62.reprn_Zlength.
  assert (Hlg : Zlength (Signed62.reprn 5 gg) = 5) by apply Signed62.reprn_Zlength.

  unfold Trans_repr.

  (* const uint64_t M62 = UINT64_MAX >> 2 *)
  forward.

  (* const int64_t f0 = f->v[0] *)
  forward.
  (* const int64_t f1 = f->v[1] *)
  forward.
  (* const int64_t f2 = f->v[2] *)
  forward.
  (* const int64_t f3 = f->v[3] *)
  forward.
  (* const int64_t f4 = f->v[4] *)
  forward.

  (* const int64_t g0 = g->v[0] *)
  forward.
  (* const int64_t g1 = g->v[1] *)
  forward.
  (* const int64_t g2 = g->v[2] *)
  forward.
  (* const int64_t g3 = g->v[3] *)
  forward.
  (* const int64_t g4 = g->v[4] *)
  forward.

  (* const int64_t u = t->u *)
  forward.
  (* const int64_t v = t->v *)
  forward.
  (* const int64_t q = t->q *)
  forward.
  (* const int64_t r = t->r *)
  forward.

  set (f := ff) in *.
  set (g := gg) in *.
  set (len := 5%nat) in *.

  change (62 * 5 + 1) with (62 * Z.of_nat len + 1) in Hff, Hgg.

  (* HZnth: limb i of (reprn len a) is the 62-bit window of a at offset 62*i *)
  assert (HZnth : forall a i, 0 <= i < Z.of_nat len ->
          Znth i (Signed62.reprn len a) =
          Int64.repr (Z.shiftr (if Z.of_nat len =? i + 1 then a else a mod 2^(62 * (i + 1))) (62 * i))).
  { intros a i Hi.
    rewrite f_if, (f_if (fun f => f (62 * i))).
    rewrite Z.mul_add_distr_l, (Z.add_comm (62 * i)), <- Z_shiftr_mod_2 by lia.
    assert (Ha := Signed62.reprn_Zlength len a).
    elim (Z.eqb_spec); intros Hlen.
    - (* branch: top limb -- window of the full value a *)
      replace i with (Z.of_nat len - 1)%Z by lia.
      rewrite <- Ha at 1.
      rewrite Znth_last, Signed62.reprn_last by lia.
      reflexivity.
    - (* branch: interior limb -- window of a mod 2^(62*(i+1)) *)
      rewrite Signed62.reprn_Znth by lia.
      reflexivity. }

  (* fi/gi i = the low 62*i bits of f/g (the running limb-i window) *)
  pose (fi := fun i => if Z.of_nat len =? i then f else f mod 2^(62*i)).
  pose (gi := fun i => if Z.of_nat len =? i then g else g mod 2^(62*i)).

  (* Hfij/Hgij: re-taking the smaller window of a larger one is idempotent *)
  assert (Hfij : forall i j, j <= Z.of_nat len -> 0 <= i < j -> (fi j) mod 2^(62 * i) = fi i).
  { intros i j Hj Hij.
    unfold fi.
    replace (Z.of_nat len =? i) with false by lia.
    destruct (Z.of_nat len =? j); try reflexivity.
    rewrite <- !Z.land_ones, <- Z.land_assoc, Z_land_ones_min, Z.min_r by lia.
    reflexivity. }

  assert (Hgij : forall i j, j <= Z.of_nat len -> 0 <= i < j -> (gi j) mod 2^(62 * i) = gi i).
  { intros i j Hj Hij.
    unfold gi.
    replace (Z.of_nat len =? i) with false by lia.
    destruct (Z.of_nat len =? j); try reflexivity.
    rewrite <- !Z.land_ones, <- Z.land_assoc, Z_land_ones_min, Z.min_r by lia.
    reflexivity. }

  (* Hfi/Hgi: the limb-i window fits in 62*i+1 signed bits *)
  assert (Hfi : forall i, 0 <= i -> -2 ^ (62*i + 1) <= fi i <= 2 ^ (62*i + 1) - 1).
  { intros i Hi.
    unfold fi.
    elim Z.eqb_spec.
    - (* branch: i = len -- the window is all of f *)
      intros <-.
      lia.
    - (* branch: i < len -- the window is f mod 2^(62*i) *)
      intros _.
      assert (Hp : 0 < 2 ^ (62 * i)) by (apply Z.pow_pos_nonneg; lia).
      pose proof (Z.mod_pos_bound f (2 ^ (62 * i)) Hp) as Hm.
      rewrite Z.pow_add_r by lia.
      lia. }

  assert (Hgi : forall i, 0 <= i -> -2 ^ (62*i + 1) <= gi i <= 2 ^ (62*i + 1) - 1).
  { intros i Hi.
    unfold gi.
    elim Z.eqb_spec.
    - (* branch: i = len -- the window is all of g *)
      intros <-.
      lia.
    - (* branch: i < len -- the window is g mod 2^(62*i) *)
      intros _.
      assert (Hp : 0 < 2 ^ (62 * i)) by (apply Z.pow_pos_nonneg; lia).
      pose proof (Z.mod_pos_bound g (2 ^ (62 * i)) Hp) as Hm.
      rewrite Z.pow_add_r by lia.
      lia. }

  assert (Hf1 := Hfi 1 ltac:(lia)).
  assert (Hg1 := Hgi 1 ltac:(lia)).

  (* Name the matrix entries u,v,q,r and their bounds from the PRE [bounded] hyp *)
  destruct H1 as [[Huv Huv'] [Hqr Hqr']].
  set (u := divstep_trans.Trans.u mtx) in *.
  set (v := divstep_trans.Trans.v mtx) in *.
  set (q := divstep_trans.Trans.q mtx) in *.
  set (r := divstep_trans.Trans.r mtx) in *.

  set (T := (Vlong (Int64.repr u),(Vlong (Int64.repr v),
         (Vlong (Int64.repr q), Vlong (Int64.repr r))))).

  (* H6262i: a 2^a-bounded times a 2^b-bounded value is 2^(a+b)-bounded *)
  assert (H6262i : forall a b x y, -2 ^ a <= x <= 2 ^ a -> -2 ^ b <= y <= 2 ^ b ->
    -(2 ^ a * 2 ^ b) <= x * y <= 2 ^ a * 2 ^ b).
  { intros a b x y Hx Hy.
    rewrite <- Z.abs_le in *.
    rewrite Z.abs_mul.
    apply Z.le_trans with (Z.abs x * 2 ^ b).
    - (* |x| * |y| <= |x| * 2^b *)
      apply Z.mul_le_mono_nonneg_l.
      + lia.
      + apply Hy.
    - (* |x| * 2^b <= 2^a * 2^b *)
      apply Z.mul_le_mono_nonneg_r.
      + lia.
      + apply Hx. }

  (* product bounds for the cf/cg accumulations *)
  assert (Hufi : forall i, 0 <= i -> -(2 ^ 62 * 2^(62 * i + 1)) <= u * fi i <= 2 ^ 62 * 2^(62 * i + 1))
    by (intros; specialize (Hfi i); apply H6262i; lia).
  assert (Hvgi : forall i, 0 <= i -> -(2 ^ 62 * 2^(62 * i + 1)) <= v * gi i <= 2 ^ 62 * 2^(62 * i + 1))
    by (intros; specialize (Hgi i); apply H6262i; lia).
  assert (Hqfi : forall i, 0 <= i -> -(2 ^ 62 * 2^(62 * i + 1)) <= q * fi i <= 2 ^ 62 * 2^(62 * i + 1))
    by (intros; specialize (Hfi i); apply H6262i; lia).
  assert (Hrgi : forall i, 0 <= i -> -(2 ^ 62 * 2^(62 * i + 1)) <= r * gi i <= 2 ^ 62 * 2^(62 * i + 1))
    by (intros; specialize (Hgi i); apply H6262i; lia).

  (* model-typed wrappers for the i64 matrix entries *)
  assert (Habsu : -2^62 <= u <= 2^62) by (apply Z.abs_le; lia).
  assert (Habsv : -2^62 <= v <= 2^62) by (apply Z.abs_le; lia).
  assert (Habsq : -2^62 <= q <= 2^62) by (apply Z.abs_le; lia).
  assert (Habsr : -2^62 <= r <= 2^62) by (apply Z.abs_le; lia).

  assert (HuB : -2^63 <= u < 2^63) by (change (2^63) with (2 * 2^62); lia).
  assert (HvB : -2^63 <= v < 2^63) by (change (2^63) with (2 * 2^62); lia).
  assert (HqB : -2^63 <= q < 2^63) by (change (2^63) with (2 * 2^62); lia).
  assert (HrB : -2^63 <= r < 2^63) by (change (2^63) with (2 * 2^62); lia).

  set (uI := mkInt64 u HuB).
  set (vI := mkInt64 v HvB).
  set (qI := mkInt64 q HqB).
  set (rI := mkInt64 r HrB).

  assert (HuI : i64_val uI = u) by reflexivity.
  assert (HvI : i64_val vI = v) by reflexivity.
  assert (HqI : i64_val qI = q) by reflexivity.
  assert (HrI : i64_val rI = r) by reflexivity.

  (* HZf/HZg: array limb i loaded as the window Int64 [Z.shiftr (fi (i+1)) (62*i)] *)
  assert (HZf : forall i, 0 <= i < Z.of_nat len -> Znth i (Signed62.reprn len f) = Int64.repr (Z.shiftr (fi (i+1)) (62*i))).
  { intros i Hi.
    rewrite HZnth by lia.
    reflexivity. }

  assert (HZg : forall i, 0 <= i < Z.of_nat len -> Znth i (Signed62.reprn len g) = Int64.repr (Z.shiftr (gi (i+1)) (62*i))).
  { intros i Hi.
    rewrite HZnth by lia.
    reflexivity. }

  (* HfS/HgS: the shifted limb window fits in [Int64] *)
  assert (HfS : forall i, 0 <= i -> -2^63 <= Z.shiftr (fi (i+1)) (62*i) < 2^63).
  { intros i Hi.
    apply shiftr_bounds.
    specialize (Hfi (i+1) ltac:(lia)).
    replace (62 * (i+1) + 1) with (62*i + 63) in Hfi by ring.
    rewrite Z.pow_add_r in Hfi by lia.
    nia. }

  assert (HgS : forall i, 0 <= i -> -2^63 <= Z.shiftr (gi (i+1)) (62*i) < 2^63).
  { intros i Hi.
    apply shiftr_bounds.
    specialize (Hgi (i+1) ltac:(lia)).
    replace (62 * (i+1) + 1) with (62*i + 63) in Hgi by ring.
    rewrite Z.pow_add_r in Hgi by lia.
    nia. }

  (* the bottom limbs fi 1, gi 1 fit in [Int64] *)
  assert (Hf1B : -2^63 <= fi 1 < 2^63) by (replace 63 with (62*1+1) by lia; lia).
  assert (Hg1B : -2^63 <= gi 1 < 2^63) by (replace 63 with (62*1+1) by lia; lia).

  set (f0I := mkInt64 (fi 1) Hf1B).
  set (g0I := mkInt64 (gi 1) Hg1B).

  assert (Hf0I : i64_val f0I = fi 1) by reflexivity.
  assert (Hg0I : i64_val g0I = gi 1) by reflexivity.

  (* rewrite the bottom temps to the window form so [forward_call] matches *)
  rewrite (HZf 0) by lia.

  rewrite (HZg 0) by lia.
  change (62 * 0) with 0.
  rewrite !Z.shiftr_0_r.
  change (0 + 1)%Z with 1%Z.

  (* ===== Bottom limb: cf = u*f0 + v*g0; cg = q*f0 + r*g0; >>62 ===== *)

  assert (Huf1 := Hufi 1 ltac:(lia)).
  assert (Hvg1 := Hvgi 1 ltac:(lia)).
  assert (Hqf1 := Hqfi 1 ltac:(lia)).
  assert (Hrg1 := Hrgi 1 ltac:(lia)).

  (* secp256k1_i128_mul(&cf, u, f0) *)
  forward_call (v_cf, uI, f0I, Tsh).

  (* secp256k1_i128_accum_mul(&cf, v, g0) *)
  forward_call (v_cf, mul_i64 uI f0I, vI, g0I, Tsh).
  { cbn [i128_val mul_i64].
    rewrite HuI, HvI, Hf0I, Hg0I.
    lia. }
  Intros cf0.
  rename H into Hcf0.
  cbn [i128_val mul_i64] in Hcf0.
  rewrite HuI, HvI, Hf0I, Hg0I in Hcf0.

  (* secp256k1_i128_mul(&cg, q, f0) *)
  forward_call (v_cg, qI, f0I, Tsh).

  (* secp256k1_i128_accum_mul(&cg, r, g0) *)
  forward_call (v_cg, mul_i64 qI f0I, rI, g0I, Tsh).
  { cbn [i128_val mul_i64].
    rewrite HqI, HrI, Hf0I, Hg0I.
    lia. }
  Intros cg0.
  rename H into Hcg0.
  cbn [i128_val mul_i64] in Hcg0.
  rewrite HqI, HrI, Hf0I, Hg0I in Hcg0.

  (* secp256k1_i128_rshift(&cf, 62) *)
  forward_call (v_cf, cf0, 62, Tsh).
  Intros cf1.
  rename H into Hcf1.
  rewrite Hcf0 in Hcf1.

  (* secp256k1_i128_rshift(&cg, 62) *)
  forward_call (v_cg, cg0, 62, Tsh).
  Intros cg1.
  rename H into Hcg1.
  rewrite Hcg0 in Hcg1.

  change (Int64.shru _ _) with (Int64.repr (Z.ones 62)).

  (* ===== Window algebra: the splice and fold facts for the limb blocks ===== *)

  (* convert the data to [pad] form so [pad_*] lemmas apply *)
  rewrite <- (Signed62.pad5 (Signed62.reprn len f)) by apply Signed62.reprn_length.
  rewrite <- (Signed62.pad5 (Signed62.reprn len g)) by apply Signed62.reprn_length.

  (* post-window values + helper facts for the splice/window math *)
  set (Ff := (u * f + v * g) / 2^62) in *.
  set (Fg := (q * f + r * g) / 2^62) in *.
  assert (Hfi62 : forall i, 0 <= i -> fi i mod 2^(62*i) = f mod 2^(62*i)).
  { intros i Hi.
    unfold fi.
    destruct Z.eqb.
    - (* branch: i = len -- the window is f itself *)
      reflexivity.
    - (* branch: i < len -- re-taking the same window is idempotent *)
      apply Zmod_mod. }

  assert (Hgi62 : forall i, 0 <= i -> gi i mod 2^(62*i) = g mod 2^(62*i)).
  { intros i Hi.
    unfold gi.
    destruct Z.eqb.
    - (* branch: i = len -- the window is g itself *)
      reflexivity.
    - (* branch: i < len -- re-taking the same window is idempotent *)
      apply Zmod_mod. }

  (* the [i128_to_u64] reduction mod 2^64 is absorbed by the subsequent & M62 *)
  assert (Hmod6462 : forall a, Z.land (a mod 2^64) (Z.ones 62) = Z.land a (Z.ones 62)).
  { intros a.
    rewrite !Z.land_ones by lia.
    rewrite <- Znumtheory.Zmod_div_mod by (try lia; exists (2^2); reflexivity).
    reflexivity. }

  (* Hstore: the masked low 62 bits of the (i+1)-window equal the limb of [Ff]/[Fg] *)
  assert (Hstore : forall c d (a b : Z -> Z) j, 0 <= j ->
    (forall i, 0 <= i -> a i mod 2^(62*i) = f mod 2^(62*i)) ->
    (forall i, 0 <= i -> b i mod 2^(62*i) = g mod 2^(62*i)) ->
    Z.shiftr (c * a (j+2) + d * b (j+2)) (62*(j+1)) mod 2^62
    = Z.shiftr (c * f + d * g) (62*(j+1)) mod 2^62).
  { intros c d a b j Hj Ha Hb.
    rewrite !(Z_shiftr_mod_2 _ (62*(j+1)) 62) by lia.
    replace (62 + 62 * (j + 1)) with (62 * (j + 2)) by ring.
    rewrite <- Z.add_mod_idemp_l, <- Z.add_mod_idemp_r by lia.
    rewrite <- (Z.mul_mod_idemp_r c (a (j+2))), <- (Z.mul_mod_idemp_r d (b (j+2))) by lia.
    rewrite Ha, Hb by lia.
    rewrite !Z.mul_mod_idemp_r, Z.add_mod_idemp_l, Z.add_mod_idemp_r by lia.
    reflexivity. }

  (* Hfold: combine the running window with the new product terms into the (i+1)-window *)
  assert (Hfold : forall c d (a b : Z -> Z) i, 0 <= i ->
    a (i+1) mod 2^(62*i) = a i -> b (i+1) mod 2^(62*i) = b i ->
    Z.shiftr (c * a i + d * b i) (62*i) + c * Z.shiftr (a (i+1)) (62*i) + d * Z.shiftr (b (i+1)) (62*i)
    = Z.shiftr (c * a (i+1) + d * b (i+1)) (62*i)).
  { intros c d a b i Hi Hax Hbx.
    rewrite !Z.shiftr_div_pow2 by lia.
    rewrite <- Hax, <- Hbx.
    replace (c * (a (i+1) mod 2^(62*i)) + d * (b (i+1) mod 2^(62*i)))
      with ((c * a (i+1) + d * b (i+1)) - (c * (a (i+1) / 2^(62*i)) + d * (b (i+1) / 2^(62*i))) * 2^(62*i))
      by (rewrite (Z_div_mod_eq_full (a (i+1)) (2^(62*i))) at 1;
          rewrite (Z_div_mod_eq_full (b (i+1)) (2^(62*i))) at 1; ring).
    replace (c * a (i + 1) + d * b (i + 1) -
     (c * (a (i + 1) / 2 ^ (62 * i)) + d * (b (i + 1) / 2 ^ (62 * i))) * 2 ^ (62 * i))
     with (c * a (i + 1) + d * b (i + 1) +
     (- (c * (a (i + 1) / 2 ^ (62 * i)) + d * (b (i + 1) / 2 ^ (62 * i)))) * 2 ^ (62 * i)) by ring.
    rewrite Z.div_add by lia.
    ring. }

  (* cast the bottom windows into [Z.shiftr _ (62*1)] form (the invariant shape) *)
  replace ((u * fi 1 + v * gi 1) / 2 ^ 62)
    with (Z.shiftr (u * fi 1 + v * gi 1) (62*1)) in Hcf1
    by (rewrite Z.shiftr_div_pow2 by lia; reflexivity).
  replace ((q * fi 1 + r * gi 1) / 2 ^ 62)
    with (Z.shiftr (q * fi 1 + r * gi 1) (62*1)) in Hcg1
    by (rewrite Z.shiftr_div_pow2 by lia; reflexivity).

  (* ===== Power-of-two arithmetic facts for the i128 overflow side-conditions ===== *)

  assert (Hppf : forall i, 0 <= i -> 2^62 * 2^(62*i+1) = 2^(62*i) * 2^63).
  { intros i Hi.
    rewrite <- !Z.pow_add_r by lia.
    f_equal.
    lia. }

  assert (Hpw : 2^63 + 2^63 <= 2^66 /\ 2^66 + 2^125 + 2^125 <= 2^127 /\ -(2^127) <= -2^66 - 2^125 - 2^125 /\ 2^125 = 2^62 * 2^63).
  { replace 66 with (63 + 3) at 2 3 by lia.
    replace 127 with (125 + 2) by lia.
    replace 125 with (62 + 63) at 5 6 7 by lia.
    rewrite !(Z.pow_add_r) by lia.
    lia. }

  destruct Hpw as [Hpw63 [Hpw127 [Hpw127' Hpw125]]].

  (* Hwf/Hwg: the running limb-i window fits in [-2^66, 2^66) *)
  assert (Hwf : forall i, 0 <= i -> -2^66 <= Z.shiftr (u * fi i + v * gi i) (62 * i) < 2^66).
  { intros i Hi.
    apply shiftr_bounds.
    pose proof (Hufi i ltac:(lia)) as Hu.
    pose proof (Hvgi i ltac:(lia)) as Hv.
    rewrite Hppf in Hu, Hv by lia.
    assert (Hp : 0 <= 2^(62*i)) by (apply Z.pow_nonneg; lia).
    nia. }

  assert (Hwg : forall i, 0 <= i -> -2^66 <= Z.shiftr (q * fi i + r * gi i) (62 * i) < 2^66).
  { intros i Hi.
    apply shiftr_bounds.
    pose proof (Hqfi i ltac:(lia)) as Hu.
    pose proof (Hrgi i ltac:(lia)) as Hv.
    rewrite Hppf in Hu, Hv by lia.
    assert (Hp : 0 <= 2^(62*i)) by (apply Z.pow_nonneg; lia).
    nia. }

  (* product bounds for one shifted-limb times a matrix entry: [-2^125, 2^125] *)
  assert (Hpuf : forall i, 0 <= i -> -2^125 <= u * Z.shiftr (fi (i+1)) (62*i) <= 2^125).
  { intros i Hi.
    rewrite Hpw125.
    pose proof (HfS i ltac:(lia)).
    apply H6262i; lia. }

  assert (Hpvg : forall i, 0 <= i -> -2^125 <= v * Z.shiftr (gi (i+1)) (62*i) <= 2^125).
  { intros i Hi.
    rewrite Hpw125.
    pose proof (HgS i ltac:(lia)).
    apply H6262i; lia. }

  assert (Hpqf : forall i, 0 <= i -> -2^125 <= q * Z.shiftr (fi (i+1)) (62*i) <= 2^125).
  { intros i Hi.
    rewrite Hpw125.
    pose proof (HfS i ltac:(lia)).
    apply H6262i; lia. }

  assert (Hprg : forall i, 0 <= i -> -2^125 <= r * Z.shiftr (gi (i+1)) (62*i) <= 2^125).
  { intros i Hi.
    rewrite Hpw125.
    pose proof (HgS i ltac:(lia)).
    apply H6262i; lia. }

  (* HSf/HSg: the windows nest (a (i+1) reduced mod 2^(62*i) = a i), for Hfold *)
  assert (HSf : forall i, 0 <= i < Z.of_nat len -> fi (i+1) mod 2^(62*i) = fi i).
  { intros i Hi.
    apply Hfij; lia. }

  assert (HSg : forall i, 0 <= i < Z.of_nat len -> gi (i+1) mod 2^(62*i) = gi i).
  { intros i Hi.
    apply Hgij; lia. }

  (* convenient closed forms for the limb store values, via Hstore/Hmod6462 *)
  assert (HstoreZf : forall j, 0 <= j < Z.of_nat len - 1 ->
    Int64.repr (Z.land ((Z.shiftr (u * fi (j+2) + v * gi (j+2)) (62*(j+1))) mod 2^64) (Z.ones 62))
    = Znth j (Signed62.reprn len Ff)).
  { intros j Hj.
    rewrite Hmod6462, Z.land_ones by lia.
    rewrite Signed62.reprn_Znth by lia.
    f_equal.
    rewrite (Hstore u v fi gi j) by (lia || (intros; apply Hfi62; lia) || (intros; apply Hgi62; lia)).
    unfold Ff.
    rewrite <- (Z.shiftr_div_pow2 (u*f+v*g) 62) by lia.
    rewrite Z.shiftr_shiftr by lia.
    f_equal.
    f_equal.
    lia. }

  assert (HstoreZg : forall j, 0 <= j < Z.of_nat len - 1 ->
    Int64.repr (Z.land ((Z.shiftr (q * fi (j+2) + r * gi (j+2)) (62*(j+1))) mod 2^64) (Z.ones 62))
    = Znth j (Signed62.reprn len Fg)).
  { intros j Hj.
    rewrite Hmod6462, Z.land_ones by lia.
    rewrite Signed62.reprn_Znth by lia.
    f_equal.
    rewrite (Hstore q r fi gi j) by (lia || (intros; apply Hfi62; lia) || (intros; apply Hgi62; lia)).
    unfold Fg.
    rewrite <- (Z.shiftr_div_pow2 (q*f+r*g) 62) by lia.
    rewrite Z.shiftr_shiftr by lia.
    f_equal.
    f_equal.
    lia. }

  (* ===== Limb iterations i = 1,2,3,4 (store into f/g[i-1]) ===== *)

  (* Per-limb block (uniform for i=1..4): load f_i/g_i windows, accumulate
     u*f_i,v*g_i into cf and q*f_i,r*g_i into cg, store the masked low 62 bits
     into f/g[i-1] (= [Znth (i-1) (reprn 5 Ff/Fg)] by HstoreZf/HstoreZg), then
     >>62.  The cf/cg invariant advances limb i -> i+1 via Hfold; the array
     splice advances via Signed62.pad_upd_Znth.  Final top limb (i=5) stores
     the signed i128_to_i64 result into f/g[4]. *)
  assert (Hp125 : 0 < 2^125) by (apply Z.pow_pos_nonneg; lia).

  (* ===== Limb i=1: accumulate f1/g1, store f/g[0], >>62 ===== *)

  rewrite (HZf 1) by lia.
  set (f1I := mkInt64 (Z.shiftr (fi (1+1)) (62*1)) (HfS 1 ltac:(lia))).
  assert (Hf1I : i64_val f1I = Z.shiftr (fi (1+1)) (62*1)) by reflexivity.

  rewrite (HZg 1) by lia.
  set (g1I := mkInt64 (Z.shiftr (gi (1+1)) (62*1)) (HgS 1 ltac:(lia))).
  assert (Hg1I : i64_val g1I = Z.shiftr (gi (1+1)) (62*1)) by reflexivity.

  (* secp256k1_i128_accum_mul(&cf, u, f1) *)
  forward_call (v_cf, cf1, uI, f1I, Tsh).
  { rewrite Hcf1, HuI.
    change (i64_val f1I) with (Z.shiftr (fi (1+1)) (62*1)).
    pose proof (Hwf 1 ltac:(lia)).
    pose proof (Hpuf 1 ltac:(lia)).
    lia. }
  Intros cf2.
  rename H into Hcf2.
  rewrite Hcf1, HuI in Hcf2.
  change (i64_val f1I) with (Z.shiftr (fi (1+1)) (62*1)) in Hcf2.

  (* secp256k1_i128_accum_mul(&cf, v, g1) *)
  forward_call (v_cf, cf2, vI, g1I, Tsh).
  { rewrite Hcf2, HvI.
    change (i64_val g1I) with (Z.shiftr (gi (1+1)) (62*1)).
    pose proof (Hwf 1 ltac:(lia)).
    pose proof (Hpuf 1 ltac:(lia)).
    pose proof (Hpvg 1 ltac:(lia)).
    lia. }
  Intros cf3.
  rename H into Hcf3.
  rewrite Hcf2, HvI in Hcf3.
  change (i64_val g1I) with (Z.shiftr (gi (1+1)) (62*1)) in Hcf3.

  (* secp256k1_i128_accum_mul(&cg, q, f1) *)
  forward_call (v_cg, cg1, qI, f1I, Tsh).
  { rewrite Hcg1, HqI.
    change (i64_val f1I) with (Z.shiftr (fi (1+1)) (62*1)).
    pose proof (Hwg 1 ltac:(lia)).
    pose proof (Hpqf 1 ltac:(lia)).
    lia. }
  Intros cg2.
  rename H into Hcg2.
  rewrite Hcg1, HqI in Hcg2.
  change (i64_val f1I) with (Z.shiftr (fi (1+1)) (62*1)) in Hcg2.

  (* secp256k1_i128_accum_mul(&cg, r, g1) *)
  forward_call (v_cg, cg2, rI, g1I, Tsh).
  { rewrite Hcg2, HrI.
    change (i64_val g1I) with (Z.shiftr (gi (1+1)) (62*1)).
    pose proof (Hwg 1 ltac:(lia)).
    pose proof (Hpqf 1 ltac:(lia)).
    pose proof (Hprg 1 ltac:(lia)).
    lia. }
  Intros cg3.
  rename H into Hcg3.
  rewrite Hcg2, HrI in Hcg3.
  change (i64_val g1I) with (Z.shiftr (gi (1+1)) (62*1)) in Hcg3.

  (* _t'1 = secp256k1_i128_to_u64(&cf) *)
  forward_call (v_cf, cf3, Tsh).
  Intros cfu1.
  rename H into Hcfu.
  rewrite Hcf3 in Hcfu.

  (* f->v[0] = _t'1 & M62 *)
  forward.

  (* secp256k1_i128_rshift(&cf, 62) *)
  forward_call (v_cf, cf3, 62, Tsh).
  Intros cfi3.
  rename H into Hcfi3.
  rewrite Hcf3 in Hcfi3.

  (* _t'2 = secp256k1_i128_to_u64(&cg) *)
  forward_call (v_cg, cg3, Tsh).
  Intros cgu1.
  rename H into Hcgu.
  rewrite Hcg3 in Hcgu.

  (* g->v[0] = _t'2 & M62 *)
  forward.

  (* secp256k1_i128_rshift(&cg, 62) *)
  forward_call (v_cg, cg3, 62, Tsh).
  Intros cgi3.
  rename H into Hcgi3.
  rewrite Hcg3 in Hcgi3.

  (* advance the cf/cg window invariant 1 -> 2 *)
  rewrite (Hfold u v fi gi 1 ltac:(lia) (HSf 1 ltac:(lia)) (HSg 1 ltac:(lia))) in Hcfi3.
  rewrite <- (Z.shiftr_div_pow2 _ 62) in Hcfi3 by lia.
  rewrite Z.shiftr_shiftr in Hcfi3 by lia.

  rewrite (Hfold q r fi gi 1 ltac:(lia) (HSf 1 ltac:(lia)) (HSg 1 ltac:(lia))) in Hcgi3.
  rewrite <- (Z.shiftr_div_pow2 _ 62) in Hcgi3 by lia.
  rewrite Z.shiftr_shiftr in Hcgi3 by lia.

  change (1+1)%Z with 2%Z in Hcfi3, Hcgi3.
  replace (62*1+62) with (62*2) in Hcfi3, Hcgi3 by lia.

  (* fold the stored low-62 windows into limb 0 of reprn 5 Ff / Fg *)
  replace (Z.shiftr (u * fi 1 + v * gi 1) (62 * 1) + u * Z.shiftr (fi (1 + 1)) (62 * 1) + v * Z.shiftr (gi (1 + 1)) (62 * 1))
    with (Z.shiftr (u * fi (1+1) + v * gi (1+1)) (62*1)) in Hcfu
    by (symmetry; apply (Hfold u v fi gi 1); [lia | apply (HSf 1); lia | apply (HSg 1); lia]).

  replace (Z.shiftr (q * fi 1 + r * gi 1) (62 * 1) + q * Z.shiftr (fi (1 + 1)) (62 * 1) + r * Z.shiftr (gi (1 + 1)) (62 * 1))
    with (Z.shiftr (q * fi (1+1) + r * gi (1+1)) (62*1)) in Hcgu
    by (symmetry; apply (Hfold q r fi gi 1); [lia | apply (HSf 1); lia | apply (HSg 1); lia]).

  assert (HSVf1 : Vlong (Int64.and (Int64.repr (u64_val cfu1)) (Int64.repr (Z.ones 62))) = Vlong (Znth 0 (Signed62.reprn len Ff))).
  { rewrite and64_repr, Hcfu.
    rewrite <- (HstoreZf 0) by lia.
    reflexivity. }

  assert (HSVg1 : Vlong (Int64.and (Int64.repr (u64_val cgu1)) (Int64.repr (Z.ones 62))) = Vlong (Znth 0 (Signed62.reprn len Fg))).
  { rewrite and64_repr, Hcgu.
    rewrite <- (HstoreZg 0) by lia.
    reflexivity. }

  rewrite HSVf1, HSVg1.

  rewrite (Signed62.pad_upd_Znth (Znth 0 (Signed62.reprn len Ff)) 0 (Signed62.reprn len f)) by (rewrite Signed62.reprn_Zlength; lia).
  rewrite (Signed62.pad_upd_Znth (Znth 0 (Signed62.reprn len Fg)) 0 (Signed62.reprn len g)) by (rewrite Signed62.reprn_Zlength; lia).

  clear HSVf1 HSVg1 Hcfu Hcgu cf2 cf3 cg2 cg3 Hcf2 Hcf3 Hcg2 Hcg3.

  (* ===== Limb i=2: accumulate f2/g2, store f/g[1], >>62 ===== *)

  rewrite (HZf 2) by lia.
  set (f2I := mkInt64 (Z.shiftr (fi (2+1)) (62*2)) (HfS 2 ltac:(lia))).
  assert (Hf2I : i64_val f2I = Z.shiftr (fi (2+1)) (62*2)) by reflexivity.

  rewrite (HZg 2) by lia.
  set (g2I := mkInt64 (Z.shiftr (gi (2+1)) (62*2)) (HgS 2 ltac:(lia))).
  assert (Hg2I : i64_val g2I = Z.shiftr (gi (2+1)) (62*2)) by reflexivity.

  (* secp256k1_i128_accum_mul(&cf, u, f2) *)
  forward_call (v_cf, cfi3, uI, f2I, Tsh).
  { rewrite Hcfi3, HuI.
    change (i64_val f2I) with (Z.shiftr (fi (2+1)) (62*2)).
    pose proof (Hwf 2 ltac:(lia)).
    pose proof (Hpuf 2 ltac:(lia)).
    lia. }
  Intros cf2.
  rename H into Hcf2.
  rewrite Hcfi3, HuI in Hcf2.
  change (i64_val f2I) with (Z.shiftr (fi (2+1)) (62*2)) in Hcf2.

  (* secp256k1_i128_accum_mul(&cf, v, g2) *)
  forward_call (v_cf, cf2, vI, g2I, Tsh).
  { rewrite Hcf2, HvI.
    change (i64_val g2I) with (Z.shiftr (gi (2+1)) (62*2)).
    pose proof (Hwf 2 ltac:(lia)).
    pose proof (Hpuf 2 ltac:(lia)).
    pose proof (Hpvg 2 ltac:(lia)).
    lia. }
  Intros cf3.
  rename H into Hcf3.
  rewrite Hcf2, HvI in Hcf3.
  change (i64_val g2I) with (Z.shiftr (gi (2+1)) (62*2)) in Hcf3.

  (* secp256k1_i128_accum_mul(&cg, q, f2) *)
  forward_call (v_cg, cgi3, qI, f2I, Tsh).
  { rewrite Hcgi3, HqI.
    change (i64_val f2I) with (Z.shiftr (fi (2+1)) (62*2)).
    pose proof (Hwg 2 ltac:(lia)).
    pose proof (Hpqf 2 ltac:(lia)).
    lia. }
  Intros cg2.
  rename H into Hcg2.
  rewrite Hcgi3, HqI in Hcg2.
  change (i64_val f2I) with (Z.shiftr (fi (2+1)) (62*2)) in Hcg2.

  (* secp256k1_i128_accum_mul(&cg, r, g2) *)
  forward_call (v_cg, cg2, rI, g2I, Tsh).
  { rewrite Hcg2, HrI.
    change (i64_val g2I) with (Z.shiftr (gi (2+1)) (62*2)).
    pose proof (Hwg 2 ltac:(lia)).
    pose proof (Hpqf 2 ltac:(lia)).
    pose proof (Hprg 2 ltac:(lia)).
    lia. }
  Intros cg3.
  rename H into Hcg3.
  rewrite Hcg2, HrI in Hcg3.
  change (i64_val g2I) with (Z.shiftr (gi (2+1)) (62*2)) in Hcg3.

  (* _t'3 = secp256k1_i128_to_u64(&cf) *)
  forward_call (v_cf, cf3, Tsh).
  Intros cfu2.
  rename H into Hcfu.
  rewrite Hcf3 in Hcfu.

  (* f->v[1] = _t'3 & M62 *)
  forward.

  (* secp256k1_i128_rshift(&cf, 62) *)
  forward_call (v_cf, cf3, 62, Tsh).
  Intros cfi3b.
  rename H into Hcfi3b.
  rewrite Hcf3 in Hcfi3b.

  (* _t'4 = secp256k1_i128_to_u64(&cg) *)
  forward_call (v_cg, cg3, Tsh).
  Intros cgu2.
  rename H into Hcgu.
  rewrite Hcg3 in Hcgu.

  (* g->v[1] = _t'4 & M62 *)
  forward.

  (* secp256k1_i128_rshift(&cg, 62) *)
  forward_call (v_cg, cg3, 62, Tsh).
  Intros cgi3b.
  rename H into Hcgi3b.
  rewrite Hcg3 in Hcgi3b.

  (* advance the cf/cg window invariant 2 -> 3 *)
  rewrite (Hfold u v fi gi 2 ltac:(lia) (HSf 2 ltac:(lia)) (HSg 2 ltac:(lia))) in Hcfi3b.
  rewrite <- (Z.shiftr_div_pow2 _ 62) in Hcfi3b by lia.
  rewrite Z.shiftr_shiftr in Hcfi3b by lia.

  rewrite (Hfold q r fi gi 2 ltac:(lia) (HSf 2 ltac:(lia)) (HSg 2 ltac:(lia))) in Hcgi3b.
  rewrite <- (Z.shiftr_div_pow2 _ 62) in Hcgi3b by lia.
  rewrite Z.shiftr_shiftr in Hcgi3b by lia.

  change (2+1)%Z with 3%Z in Hcfi3b, Hcgi3b.
  replace (62*2+62) with (62*3) in Hcfi3b, Hcgi3b by lia.

  (* fold the stored low-62 windows into limb 1 of reprn 5 Ff / Fg *)
  replace (Z.shiftr (u * fi 2 + v * gi 2) (62 * 2) + u * Z.shiftr (fi (2 + 1)) (62 * 2) + v * Z.shiftr (gi (2 + 1)) (62 * 2))
    with (Z.shiftr (u * fi (2+1) + v * gi (2+1)) (62*2)) in Hcfu
    by (symmetry; apply (Hfold u v fi gi 2); [lia | apply (HSf 2); lia | apply (HSg 2); lia]).

  replace (Z.shiftr (q * fi 2 + r * gi 2) (62 * 2) + q * Z.shiftr (fi (2 + 1)) (62 * 2) + r * Z.shiftr (gi (2 + 1)) (62 * 2))
    with (Z.shiftr (q * fi (2+1) + r * gi (2+1)) (62*2)) in Hcgu
    by (symmetry; apply (Hfold q r fi gi 2); [lia | apply (HSf 2); lia | apply (HSg 2); lia]).

  assert (HSVf2 : Vlong (Int64.and (Int64.repr (u64_val cfu2)) (Int64.repr (Z.ones 62))) = Vlong (Znth 1 (Signed62.reprn len Ff))).
  { rewrite and64_repr, Hcfu.
    rewrite <- (HstoreZf 1) by lia.
    repeat f_equal; lia. }

  assert (HSVg2 : Vlong (Int64.and (Int64.repr (u64_val cgu2)) (Int64.repr (Z.ones 62))) = Vlong (Znth 1 (Signed62.reprn len Fg))).
  { rewrite and64_repr, Hcgu.
    rewrite <- (HstoreZg 1) by lia.
    repeat f_equal; lia. }

  rewrite HSVf2, HSVg2.

  rewrite (Signed62.pad_upd_Znth (Znth 1 (Signed62.reprn len Ff)) 1) by (rewrite Zlength_upd_Znth, Signed62.reprn_Zlength; lia).
  rewrite (Signed62.pad_upd_Znth (Znth 1 (Signed62.reprn len Fg)) 1) by (rewrite Zlength_upd_Znth, Signed62.reprn_Zlength; lia).

  clear HSVf2 HSVg2 Hcfu Hcgu cf2 cf3 cg2 cg3 Hcf2 Hcf3 Hcg2 Hcg3.

  (* ===== Limb i=3: accumulate f3/g3, store f/g[2], >>62 ===== *)

  rewrite (HZf 3) by lia.
  set (f3I := mkInt64 (Z.shiftr (fi (3+1)) (62*3)) (HfS 3 ltac:(lia))).
  assert (Hf3I : i64_val f3I = Z.shiftr (fi (3+1)) (62*3)) by reflexivity.

  rewrite (HZg 3) by lia.
  set (g3I := mkInt64 (Z.shiftr (gi (3+1)) (62*3)) (HgS 3 ltac:(lia))).
  assert (Hg3I : i64_val g3I = Z.shiftr (gi (3+1)) (62*3)) by reflexivity.

  (* secp256k1_i128_accum_mul(&cf, u, f3) *)
  forward_call (v_cf, cfi3b, uI, f3I, Tsh).
  { rewrite Hcfi3b, HuI.
    change (i64_val f3I) with (Z.shiftr (fi (3+1)) (62*3)).
    pose proof (Hwf 3 ltac:(lia)).
    pose proof (Hpuf 3 ltac:(lia)).
    lia. }
  Intros cf2.
  rename H into Hcf2.
  rewrite Hcfi3b, HuI in Hcf2.
  change (i64_val f3I) with (Z.shiftr (fi (3+1)) (62*3)) in Hcf2.

  (* secp256k1_i128_accum_mul(&cf, v, g3) *)
  forward_call (v_cf, cf2, vI, g3I, Tsh).
  { rewrite Hcf2, HvI.
    change (i64_val g3I) with (Z.shiftr (gi (3+1)) (62*3)).
    pose proof (Hwf 3 ltac:(lia)).
    pose proof (Hpuf 3 ltac:(lia)).
    pose proof (Hpvg 3 ltac:(lia)).
    lia. }
  Intros cf3.
  rename H into Hcf3.
  rewrite Hcf2, HvI in Hcf3.
  change (i64_val g3I) with (Z.shiftr (gi (3+1)) (62*3)) in Hcf3.

  (* secp256k1_i128_accum_mul(&cg, q, f3) *)
  forward_call (v_cg, cgi3b, qI, f3I, Tsh).
  { rewrite Hcgi3b, HqI.
    change (i64_val f3I) with (Z.shiftr (fi (3+1)) (62*3)).
    pose proof (Hwg 3 ltac:(lia)).
    pose proof (Hpqf 3 ltac:(lia)).
    lia. }
  Intros cg2.
  rename H into Hcg2.
  rewrite Hcgi3b, HqI in Hcg2.
  change (i64_val f3I) with (Z.shiftr (fi (3+1)) (62*3)) in Hcg2.

  (* secp256k1_i128_accum_mul(&cg, r, g3) *)
  forward_call (v_cg, cg2, rI, g3I, Tsh).
  { rewrite Hcg2, HrI.
    change (i64_val g3I) with (Z.shiftr (gi (3+1)) (62*3)).
    pose proof (Hwg 3 ltac:(lia)).
    pose proof (Hpqf 3 ltac:(lia)).
    pose proof (Hprg 3 ltac:(lia)).
    lia. }
  Intros cg3.
  rename H into Hcg3.
  rewrite Hcg2, HrI in Hcg3.
  change (i64_val g3I) with (Z.shiftr (gi (3+1)) (62*3)) in Hcg3.

  (* _t'5 = secp256k1_i128_to_u64(&cf) *)
  forward_call (v_cf, cf3, Tsh).
  Intros cfu3.
  rename H into Hcfu.
  rewrite Hcf3 in Hcfu.

  (* f->v[2] = _t'5 & M62 *)
  forward.

  (* secp256k1_i128_rshift(&cf, 62) *)
  forward_call (v_cf, cf3, 62, Tsh).
  Intros cfi3c.
  rename H into Hcfi3c.
  rewrite Hcf3 in Hcfi3c.

  (* _t'6 = secp256k1_i128_to_u64(&cg) *)
  forward_call (v_cg, cg3, Tsh).
  Intros cgu3.
  rename H into Hcgu.
  rewrite Hcg3 in Hcgu.

  (* g->v[2] = _t'6 & M62 *)
  forward.

  (* secp256k1_i128_rshift(&cg, 62) *)
  forward_call (v_cg, cg3, 62, Tsh).
  Intros cgi3c.
  rename H into Hcgi3c.
  rewrite Hcg3 in Hcgi3c.

  (* advance the cf/cg window invariant 3 -> 4 *)
  rewrite (Hfold u v fi gi 3 ltac:(lia) (HSf 3 ltac:(lia)) (HSg 3 ltac:(lia))) in Hcfi3c.
  rewrite <- (Z.shiftr_div_pow2 _ 62) in Hcfi3c by lia.
  rewrite Z.shiftr_shiftr in Hcfi3c by lia.

  rewrite (Hfold q r fi gi 3 ltac:(lia) (HSf 3 ltac:(lia)) (HSg 3 ltac:(lia))) in Hcgi3c.
  rewrite <- (Z.shiftr_div_pow2 _ 62) in Hcgi3c by lia.
  rewrite Z.shiftr_shiftr in Hcgi3c by lia.

  change (3+1)%Z with 4%Z in Hcfi3c, Hcgi3c.
  replace (62*3+62) with (62*4) in Hcfi3c, Hcgi3c by lia.

  (* fold the stored low-62 windows into limb 2 of reprn 5 Ff / Fg *)
  replace (Z.shiftr (u * fi 3 + v * gi 3) (62 * 3) + u * Z.shiftr (fi (3 + 1)) (62 * 3) + v * Z.shiftr (gi (3 + 1)) (62 * 3))
    with (Z.shiftr (u * fi (3+1) + v * gi (3+1)) (62*3)) in Hcfu
    by (symmetry; apply (Hfold u v fi gi 3); [lia | apply (HSf 3); lia | apply (HSg 3); lia]).

  replace (Z.shiftr (q * fi 3 + r * gi 3) (62 * 3) + q * Z.shiftr (fi (3 + 1)) (62 * 3) + r * Z.shiftr (gi (3 + 1)) (62 * 3))
    with (Z.shiftr (q * fi (3+1) + r * gi (3+1)) (62*3)) in Hcgu
    by (symmetry; apply (Hfold q r fi gi 3); [lia | apply (HSf 3); lia | apply (HSg 3); lia]).

  assert (HSVf3 : Vlong (Int64.and (Int64.repr (u64_val cfu3)) (Int64.repr (Z.ones 62))) = Vlong (Znth 2 (Signed62.reprn len Ff))).
  { rewrite and64_repr, Hcfu.
    rewrite <- (HstoreZf 2) by lia.
    repeat f_equal; lia. }

  assert (HSVg3 : Vlong (Int64.and (Int64.repr (u64_val cgu3)) (Int64.repr (Z.ones 62))) = Vlong (Znth 2 (Signed62.reprn len Fg))).
  { rewrite and64_repr, Hcgu.
    rewrite <- (HstoreZg 2) by lia.
    repeat f_equal; lia. }

  rewrite HSVf3, HSVg3.

  rewrite (Signed62.pad_upd_Znth (Znth 2 (Signed62.reprn len Ff)) 2) by (rewrite !Zlength_upd_Znth, Signed62.reprn_Zlength; lia).
  rewrite (Signed62.pad_upd_Znth (Znth 2 (Signed62.reprn len Fg)) 2) by (rewrite !Zlength_upd_Znth, Signed62.reprn_Zlength; lia).

  clear HSVf3 HSVg3 Hcfu Hcgu cf2 cf3 cg2 cg3 Hcf2 Hcf3 Hcg2 Hcg3.

  (* ===== Limb i=4: accumulate f4/g4, store f/g[3], >>62 ===== *)

  rewrite (HZf 4) by lia.
  set (f4I := mkInt64 (Z.shiftr (fi (4+1)) (62*4)) (HfS 4 ltac:(lia))).
  assert (Hf4I : i64_val f4I = Z.shiftr (fi (4+1)) (62*4)) by reflexivity.

  rewrite (HZg 4) by lia.
  set (g4I := mkInt64 (Z.shiftr (gi (4+1)) (62*4)) (HgS 4 ltac:(lia))).
  assert (Hg4I : i64_val g4I = Z.shiftr (gi (4+1)) (62*4)) by reflexivity.

  (* secp256k1_i128_accum_mul(&cf, u, f4) *)
  forward_call (v_cf, cfi3c, uI, f4I, Tsh).
  { rewrite Hcfi3c, HuI.
    change (i64_val f4I) with (Z.shiftr (fi (4+1)) (62*4)).
    pose proof (Hwf 4 ltac:(lia)).
    pose proof (Hpuf 4 ltac:(lia)).
    lia. }
  Intros cf2.
  rename H into Hcf2.
  rewrite Hcfi3c, HuI in Hcf2.
  change (i64_val f4I) with (Z.shiftr (fi (4+1)) (62*4)) in Hcf2.

  (* secp256k1_i128_accum_mul(&cf, v, g4) *)
  forward_call (v_cf, cf2, vI, g4I, Tsh).
  { rewrite Hcf2, HvI.
    change (i64_val g4I) with (Z.shiftr (gi (4+1)) (62*4)).
    pose proof (Hwf 4 ltac:(lia)).
    pose proof (Hpuf 4 ltac:(lia)).
    pose proof (Hpvg 4 ltac:(lia)).
    lia. }
  Intros cf3.
  rename H into Hcf3.
  rewrite Hcf2, HvI in Hcf3.
  change (i64_val g4I) with (Z.shiftr (gi (4+1)) (62*4)) in Hcf3.

  (* secp256k1_i128_accum_mul(&cg, q, f4) *)
  forward_call (v_cg, cgi3c, qI, f4I, Tsh).
  { rewrite Hcgi3c, HqI.
    change (i64_val f4I) with (Z.shiftr (fi (4+1)) (62*4)).
    pose proof (Hwg 4 ltac:(lia)).
    pose proof (Hpqf 4 ltac:(lia)).
    lia. }
  Intros cg2.
  rename H into Hcg2.
  rewrite Hcgi3c, HqI in Hcg2.
  change (i64_val f4I) with (Z.shiftr (fi (4+1)) (62*4)) in Hcg2.

  (* secp256k1_i128_accum_mul(&cg, r, g4) *)
  forward_call (v_cg, cg2, rI, g4I, Tsh).
  { rewrite Hcg2, HrI.
    change (i64_val g4I) with (Z.shiftr (gi (4+1)) (62*4)).
    pose proof (Hwg 4 ltac:(lia)).
    pose proof (Hpqf 4 ltac:(lia)).
    pose proof (Hprg 4 ltac:(lia)).
    lia. }
  Intros cg3.
  rename H into Hcg3.
  rewrite Hcg2, HrI in Hcg3.
  change (i64_val g4I) with (Z.shiftr (gi (4+1)) (62*4)) in Hcg3.

  (* _t'7 = secp256k1_i128_to_u64(&cf) *)
  forward_call (v_cf, cf3, Tsh).
  Intros cfu4.
  rename H into Hcfu.
  rewrite Hcf3 in Hcfu.

  (* f->v[3] = _t'7 & M62 *)
  forward.

  (* secp256k1_i128_rshift(&cf, 62) *)
  forward_call (v_cf, cf3, 62, Tsh).
  Intros cfL.
  rename H into HcfL.
  rewrite Hcf3 in HcfL.

  (* _t'8 = secp256k1_i128_to_u64(&cg) *)
  forward_call (v_cg, cg3, Tsh).
  Intros cgu4.
  rename H into Hcgu.
  rewrite Hcg3 in Hcgu.

  (* g->v[3] = _t'8 & M62 *)
  forward.

  (* secp256k1_i128_rshift(&cg, 62) *)
  forward_call (v_cg, cg3, 62, Tsh).
  Intros cgL.
  rename H into HcgL.
  rewrite Hcg3 in HcgL.

  (* advance the cf/cg window invariant 4 -> 5 (the full top window) *)
  rewrite (Hfold u v fi gi 4 ltac:(lia) (HSf 4 ltac:(lia)) (HSg 4 ltac:(lia))) in HcfL.
  rewrite <- (Z.shiftr_div_pow2 _ 62) in HcfL by lia.
  rewrite Z.shiftr_shiftr in HcfL by lia.

  rewrite (Hfold q r fi gi 4 ltac:(lia) (HSf 4 ltac:(lia)) (HSg 4 ltac:(lia))) in HcgL.
  rewrite <- (Z.shiftr_div_pow2 _ 62) in HcgL by lia.
  rewrite Z.shiftr_shiftr in HcgL by lia.

  change (4+1)%Z with 5%Z in HcfL, HcgL.
  replace (62*4+62) with (62*5) in HcfL, HcgL by lia.

  unfold fi, gi in HcfL, HcgL.
  change (Z.of_nat len) with 5 in HcfL, HcgL.
  rewrite !Z.eqb_refl in HcfL, HcgL.

  (* store the masked limb 3 windows into limb 3 of reprn 5 Ff / Fg *)
  replace (Z.shiftr (u * fi 4 + v * gi 4) (62 * 4) + u * Z.shiftr (fi (4 + 1)) (62 * 4) + v * Z.shiftr (gi (4 + 1)) (62 * 4))
    with (Z.shiftr (u * fi (4+1) + v * gi (4+1)) (62*4)) in Hcfu
    by (symmetry; apply (Hfold u v fi gi 4); [lia | apply (HSf 4); lia | apply (HSg 4); lia]).

  replace (Z.shiftr (q * fi 4 + r * gi 4) (62 * 4) + q * Z.shiftr (fi (4 + 1)) (62 * 4) + r * Z.shiftr (gi (4 + 1)) (62 * 4))
    with (Z.shiftr (q * fi (4+1) + r * gi (4+1)) (62*4)) in Hcgu
    by (symmetry; apply (Hfold q r fi gi 4); [lia | apply (HSf 4); lia | apply (HSg 4); lia]).

  assert (HSVf4 : Vlong (Int64.and (Int64.repr (u64_val cfu4)) (Int64.repr (Z.ones 62))) = Vlong (Znth 3 (Signed62.reprn len Ff))).
  { rewrite and64_repr, Hcfu.
    rewrite <- (HstoreZf 3) by lia.
    repeat f_equal; lia. }

  assert (HSVg4 : Vlong (Int64.and (Int64.repr (u64_val cgu4)) (Int64.repr (Z.ones 62))) = Vlong (Znth 3 (Signed62.reprn len Fg))).
  { rewrite and64_repr, Hcgu.
    rewrite <- (HstoreZg 3) by lia.
    repeat f_equal; lia. }

  rewrite HSVf4, HSVg4.

  rewrite (Signed62.pad_upd_Znth (Znth 3 (Signed62.reprn len Ff)) 3) by (rewrite !Zlength_upd_Znth, Signed62.reprn_Zlength; lia).
  rewrite (Signed62.pad_upd_Znth (Znth 3 (Signed62.reprn len Fg)) 3) by (rewrite !Zlength_upd_Znth, Signed62.reprn_Zlength; lia).

  clear HSVf4 HSVg4 Hcfu Hcgu cf2 cf3 cg2 cg3 Hcf2 Hcf3 Hcg2 Hcg3.

  (* ===== Top limb tail: f[4] = i128_to_i64(&cf); g[4] = i128_to_i64(&cg) ===== *)

  (* Hcfdg: c*f + d*g fits 2^(63 + 62*len) when |c|+|d| <= 2^62 *)
  pose proof (accum_bound_62 (62 * Z.of_nat len) f g ltac:(lia) Hff Hgg) as Hcfdg.

  assert (Hufvg : -(2 ^ 63 * 2 ^ (62 * Z.of_nat len)) <= u * f + v * g < 2 ^ 63 * 2 ^ (62 * Z.of_nat len)) by
    (apply Hcfdg; lia).
  assert (Hqfrg : -(2 ^ 63 * 2 ^ (62 * Z.of_nat len)) <= q * f + r * g < 2 ^ 63 * 2 ^ (62 * Z.of_nat len)) by
    (apply Hcfdg; lia).

  (* _t'9 = secp256k1_i128_to_i64(&cf) *)
  forward_call (v_cf, cfL, Tsh).
  { rewrite HcfL.
    apply shiftr_bounds.
    change (Z.of_nat len) with 5 in Hufvg.
    nia. }
  Intros cfr.
  rename H into Hcfr.
  rewrite HcfL in Hcfr.

  (* f->v[4] = _t'9 *)
  forward.

  (* _t'10 = secp256k1_i128_to_i64(&cg) *)
  forward_call (v_cg, cgL, Tsh).
  { rewrite HcgL.
    apply shiftr_bounds.
    change (Z.of_nat len) with 5 in Hqfrg.
    nia. }
  Intros cgr.
  rename H into Hcgr.
  rewrite HcgL in Hcgr.

  (* g->v[4] = _t'10 *)
  forward.

  (* ===== Closeout: the top limb store value is limb 4 of reprn 5 Ff / Fg ===== *)

  unfold int64_to_val.
  rewrite Hcfr, Hcgr.
  assert (HtopFz : Znth 4 (Signed62.reprn len Ff) = Int64.repr (Z.shiftr (u * f + v * g) (62 * 5))).
  { replace 4 with (Zlength (Signed62.reprn len Ff) - 1) by (rewrite Signed62.reprn_Zlength; reflexivity).
    rewrite Znth_last, Signed62.reprn_last by lia.
    unfold Ff.
    change (Z.of_nat len) with 5.
    f_equal.
    rewrite !Z.shiftr_div_pow2 by lia.
    rewrite Z.div_div by (try lia; apply Z.pow_pos_nonneg; lia).
    rewrite <- Z.pow_add_r by lia.
    f_equal. }

  assert (HtopGz : Znth 4 (Signed62.reprn len Fg) = Int64.repr (Z.shiftr (q * f + r * g) (62 * 5))).
  { replace 4 with (Zlength (Signed62.reprn len Fg) - 1) by (rewrite Signed62.reprn_Zlength; reflexivity).
    rewrite Znth_last, Signed62.reprn_last by lia.
    unfold Fg.
    change (Z.of_nat len) with 5.
    f_equal.
    rewrite !Z.shiftr_div_pow2 by lia.
    rewrite Z.div_div by (try lia; apply Z.pow_pos_nonneg; lia).
    rewrite <- Z.pow_add_r by lia.
    f_equal. }

  rewrite <- HtopFz, <- HtopGz.

  rewrite (Signed62.pad_upd_Znth (Znth 4 (Signed62.reprn len Ff)) 4) by (rewrite !Zlength_upd_Znth, Signed62.reprn_Zlength; lia).
  rewrite (Signed62.pad_upd_Znth (Znth 4 (Signed62.reprn len Fg)) 4) by (rewrite !Zlength_upd_Znth, Signed62.reprn_Zlength; lia).

  (* the 5-fold upd_Znth chain of reprn 5 f is reprn 5 Ff *)
  assert (HarrF : upd_Znth 4 (upd_Znth 3 (upd_Znth 2 (upd_Znth 1 (upd_Znth 0 (Signed62.reprn len f) (Znth 0 (Signed62.reprn len Ff))) (Znth 1 (Signed62.reprn len Ff))) (Znth 2 (Signed62.reprn len Ff))) (Znth 3 (Signed62.reprn len Ff))) (Znth 4 (Signed62.reprn len Ff)) = Signed62.reprn len Ff).
  { assert (Hl5 : Zlength (Signed62.reprn len Ff) = 5) by apply Signed62.reprn_Zlength.
    assert (Hlf5 : Zlength (Signed62.reprn len f) = 5) by apply Signed62.reprn_Zlength.
    list_solve. }

  assert (HarrG : upd_Znth 4 (upd_Znth 3 (upd_Znth 2 (upd_Znth 1 (upd_Znth 0 (Signed62.reprn len g) (Znth 0 (Signed62.reprn len Fg))) (Znth 1 (Signed62.reprn len Fg))) (Znth 2 (Signed62.reprn len Fg))) (Znth 3 (Signed62.reprn len Fg))) (Znth 4 (Signed62.reprn len Fg)) = Signed62.reprn len Fg).
  { assert (Hl5 : Zlength (Signed62.reprn len Fg) = 5) by apply Signed62.reprn_Zlength.
    assert (Hlg5 : Zlength (Signed62.reprn len g) = 5) by apply Signed62.reprn_Zlength.
    list_solve. }

  rewrite HarrF, HarrG.

  unfold Ff, Fg.
  entailer!!.
Qed.
