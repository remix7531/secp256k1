(** * verif.modinv.impl.modinv64_update_fg_62_var: body proof for secp256k1_modinv64_update_fg_62_var. *)
(** Copyright (C) 2026 remix7531
    Ported from BlockstreamResearch/simplicity Coq/C/secp256k1/verif_modinv64_impl.v
    (commit c1dddedd), Copyright (c) 2018 Blockstream, originally MIT.
    Upstream notice reproduced in proof/README.md.
    SPDX-License-Identifier: MIT *)

(** Split out from the upstream-ported verif_modinv64_impl.v (one semax_body
    per file, per the project convention). *)

Require Import secp256k1.vst.base.
Require Import secp256k1.contract.helper.structs_int128.
Require Import secp256k1.contract.helper.structs_modinv.
Require Import secp256k1.contract.int128.
Require Import secp256k1.model.int128.
Require Import secp256k1.contract.helper.notations.
Require Import secp256k1.contract.impl.modinv.
Require Import secp256k1.contract.gprog.modinv.
Require Import secp256k1.theory.extra_math.
Require Import secp256k1.theory.modinv.bounds.
Require Import secp256k1.theory.modinv.divsteps.theory.
Require Import secp256k1.theory.modinv.divsteps.bound724.
Require Import secp256k1.theory.modinv.construction.inverse.
Require secp256k1.theory.modinv.construction.divstep_trans.
Require Import secp256k1.tactics.core.
Require Import secp256k1.tactics.hygiene.

(* ================================================================= *)
(** ** secp256k1_modinv64_update_fg_62_var -- [(mtx * [f,g]) / 2^62] on [len] limbs. *)

(** [secp256k1_modinv64_update_fg_62_var(len, f, g, t)] applies the transition
    matrix [t = (u,v;q,r)] in place to [f,g]: it computes [t*[f,g] / 2^62] limb
    by limb, replacing [f,g] with the caller's post-image [f1,g1].  The contract
    is arithmetic: the caller exhibits [f1,g1] together with the identity
    [ap mtx (f0,g0) = scale (2^62) (f1,g1)] and the bound [bounded (2^62) mtx],
    so the same body serves the divstep and the positive-divstep drivers.

    Under the unified VERIFY-OFF extraction the [VERIFY_CHECK] asserts are
    absent from the AST, so this proof drops the verify blocks; the 128-bit
    accumulators [cf],[cg] are carried as model-typed [Int128] records (their
    running [i128_val] tracked in the invariant), and every i128 helper call
    threads its [int128.v] model-typed funspec. *)
Lemma body_secp256k1_modinv64_update_fg_62_var: semax_body Vprog Gprog f_secp256k1_modinv64_update_fg_62_var spec_secp256k1_modinv64_update_fg_62_var.
Proof.
  start_function.

  (* ===== Setup: name f,g and load M62 and u,v,q,r from t ===== *)

  rename H into Hlen.
  rename H0 into Hfg.
  rename H1 into Hbnd.
  rename H2 into Hf_bnd.
  rename H3 into Hg_bnd.

  set (f := f0).
  set (g := g0).
  unfold Trans_repr.

  (* const uint64_t M62 = UINT64_MAX >> 2 *)
  forward.

  (* const int64_t u = t->u *)
  forward.
  (* const int64_t v = t->v *)
  forward.
  (* const int64_t q = t->q *)
  forward.
  (* const int64_t r = t->r *)
  forward.

  (* ===== Limb-extraction lemmas: Znth of a Signed62 padding ===== *)

  (* HZnth: limb i of (reprn len a) is the 62-bit window of a at offset 62*i *)
  assert (HZnth : forall a i, 0 <= i < Z.of_nat len ->
          Znth i (Signed62.reprn len a) =
          Int64.repr (Z.shiftr (if Z.of_nat len =? i + 1 then a else a mod 2^(62 * (i + 1))) (62 * i))).
  { intros a i Hi.
    rewrite f_if, (f_if (fun f => f (62 * i))).
    rewrite Z.mul_add_distr_l, (Z.add_comm (62 * i)), <- Z_shiftr_mod_2 by lia.
    assert (Ha := Signed62.reprn_Zlength len a).
    elim (Z.eqb_spec); intros Hlen'.
    - (* branch: top limb -- window of the full value a *)
      replace i with (Z.of_nat len - 1)%Z by lia.
      rewrite <- Ha at 1.
      rewrite Znth_last, Signed62.reprn_last by lia.
      reflexivity.

    - (* branch: interior limb -- window of a mod 2^(62*(i+1)) *)
      rewrite Signed62.reprn_Znth by lia.
      reflexivity. }

  (* HZnth0: the bottom limb (i=0) of a padded reprn is a mod 2^62 (or a if len=1) *)
  assert (HZnth0 : forall a, @Znth _ Vundef 0 (Signed62.pad (Signed62.reprn len a)) =
          Vlong (Int64.repr (if Z.of_nat len =? 1 then a else a mod 2^62))).
  { intros a.
    specialize (HZnth a 0).
    rewrite Z.shiftr_0_r in HZnth.
    assert (Ha := Signed62.reprn_Zlength len a).
    rewrite Signed62.pad_nth by lia.
    destruct len as [|len].
    { (* branch: len = 0 -- excluded by the PRE bound 1 <= len *)
      lia. }
    destruct len as [|len].
    - (* branch: len = 1 -- the single limb is a itself *)
      rewrite HZnth by lia.
      reflexivity.

    - (* branch: len >= 2 -- the bottom limb is a mod 2^62 *)
      replace (Z.of_nat (S (S len)) =? 0 + 1) with false in HZnth by
        (symmetry; apply Z.eqb_neq; lia).
      rewrite HZnth by lia.
      destruct (Z.eqb_spec (Z.of_nat (S (S len))) 1) as [Hlen1|Hlen1].
      + (* sub-branch: len = 1 -- contradicts len >= 2 *)
        lia.
      + (* sub-branch: len <> 1 -- both sides are a mod 2^62 *)
        reflexivity. }

  (* ===== Bottom limbs: fi = f->v[0], gi = g->v[0] ===== *)

  (* fi = f->v[0] *)
  forward.
  { rewrite HZnth0.
    entailer!!. }

  (* gi = g->v[0] *)
  forward.
  { rewrite (HZnth0 g).
    entailer!!. }

  fold t_secp256k1_u128.
  rewrite (HZnth0 f), (HZnth0 g).
  clear HZnth0.

  (* fi/gi i = the low 62*i bits of f/g (the running limb-i window) *)
  pose (fi := fun i => if Z.of_nat len =? i then f else f mod 2^(62*i)).
  pose (gi := fun i => if Z.of_nat len =? i then g else g mod 2^(62*i)).
  change (if Z.of_nat len =? 1 then f else _) with (fi 1).
  change (if Z.of_nat len =? 1 then g else _) with (gi 1).

  (* ===== Window arithmetic: nesting + size bounds for fi/gi ===== *)

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

  assert (Hf1 := Hfi 1).
  assert (Hg1 := Hgi 1).

  (* ===== Name the matrix entries u,v,q,r and their bounds ===== *)

  destruct Hbnd as [[Huv Huv'] [Hqr Hqr']].
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

  (* ===== cf = u*f[0] + v*g[0] ===== *)

  (* product bounds for the cf accumulation *)
  assert (Hufi : forall i, 0 <= i -> -(2 ^ 62 * 2^(62 * i + 1)) <= u * fi i <= 2 ^ 62 * 2^(62 * i + 1))
    by (intros; specialize (Hfi i); apply H6262i; lia).
  assert (Hvgi : forall i, 0 <= i -> -(2 ^ 62 * 2^(62 * i + 1)) <= v * gi i <= 2 ^ 62 * 2^(62 * i + 1))
    by (intros; specialize (Hgi i); apply H6262i; lia).

  assert (Huf1 := Hufi 1).
  assert (Hvg1 := Hvgi 1).

  (* ===== Model-typed wrappers for the i64 matrix entries and limbs ===== *)

  (* the matrix entries fit in [Int64] (|u|+|v| <= 2^62, |q|+|r| <= 2^62) *)
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

  (* the bottom limbs fi 1, gi 1 fit in [Int64] (in 2^63 by Hf1/Hg1) *)
  assert (Hf1B : -2^63 <= fi 1 < 2^63) by (replace 63 with (62*1+1) by lia; lia).
  assert (Hg1B : -2^63 <= gi 1 < 2^63) by (replace 63 with (62*1+1) by lia; lia).

  set (f0I := mkInt64 (fi 1) Hf1B).
  set (g0I := mkInt64 (gi 1) Hg1B).

  assert (Hf0I : i64_val f0I = fi 1) by reflexivity.
  assert (Hg0I : i64_val g0I = gi 1) by reflexivity.

  (* secp256k1_i128_mul(&cf, u, fi) -- cf = u*fi *)
  forward_call (v_cf, uI, f0I, Tsh).

  (* secp256k1_i128_accum_mul(&cf, v, gi) -- cf += v*gi *)
  forward_call (v_cf, mul_i64 uI f0I, vI, g0I, Tsh).
  { cbn [i128_val mul_i64].
    rewrite HuI, HvI, Hf0I, Hg0I.
    lia. }
  Intros cf0.
  rename H into Hcf0.
  cbn [i128_val mul_i64] in Hcf0.
  rewrite HuI, HvI, Hf0I, Hg0I in Hcf0.

  (* ===== cg = q*f[0] + r*g[0] ===== *)

  (* product bounds for the cg accumulation *)
  assert (Hqfi : forall i, 0 <= i -> -(2 ^ 62 * 2^(62 * i + 1)) <= q * fi i <= 2 ^ 62 * 2^(62 * i + 1))
    by (intros; specialize (Hfi i); apply H6262i; lia).
  assert (Hrgi : forall i, 0 <= i -> -(2 ^ 62 * 2^(62 * i + 1)) <= r * gi i <= 2 ^ 62 * 2^(62 * i + 1))
    by (intros; specialize (Hgi i); apply H6262i; lia).

  assert (Hqf1 := Hqfi 1).
  assert (Hrg1 := Hrgi 1).

  (* secp256k1_i128_mul(&cg, q, fi) -- cg = q*fi *)
  forward_call (v_cg, qI, f0I, Tsh).

  (* secp256k1_i128_accum_mul(&cg, r, gi) -- cg += r*gi *)
  forward_call (v_cg, mul_i64 qI f0I, rI, g0I, Tsh).
  { cbn [i128_val mul_i64].
    rewrite HqI, HrI, Hf0I, Hg0I.
    lia. }
  Intros cg0.
  rename H into Hcg0.
  cbn [i128_val mul_i64] in Hcg0.
  rewrite HqI, HrI, Hf0I, Hg0I in Hcg0.

  change (Int64.shru _ _) with (Int64.repr (Z.ones 62)).

  (* ===== Post-image f1,g1: the caller's matrix identity, component-wise ===== *)

  (* Hfg says ap mtx (f,g) = 2^62 * (f1,g1); its two components are
     2^62*f1 = u*f+v*g and 2^62*g1 = q*f+r*g *)
  symmetry in Hfg.
  injection Hfg as Htransf Htransg.
  change (2^62 * f1 = u*f + v*g) in Htransf.
  change (2^62 * g1 = q*f + r*g) in Htransg.

  (* the limb-i window of fi/gi agrees with that of f/g mod 2^(62*i) *)
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

  (* secp256k1_i128_rshift(&cf, 62) -- drop the verified-zero low limb *)
  forward_call (v_cf, cf0, 62, Tsh).
  Intros cf1.
  rename H into Hcf1.
  rewrite Hcf0 in Hcf1.

  (* secp256k1_i128_rshift(&cg, 62) *)
  forward_call (v_cg, cg0, 62, Tsh).
  Intros cg1.
  rename H into Hcg1.
  rewrite Hcg0 in Hcg1.

  (* ===== Loop i=1..len-1: limb i of t*[f,g], stored shifted into limb i-1 ===== *)

  (* the firstn/skipn splice keeps full length on every iteration *)
  assert (Hlength_firstn_skipn : forall n m x y,
      Zlength (firstn (Z.to_nat n) (Signed62.reprn m x) ++ skipn (Z.to_nat n) (Signed62.reprn m y)) = Z.of_nat m)
    by (intros; rewrite Zlength_app, Zlength_firstn, Zlength_skipn, !Signed62.reprn_Zlength; lia).

  (* invariant: cf,cg hold the limb-i windows; f,g are spliced new-below/old-above *)
  forward_for_simple_bound (Z.of_nat len)
    (EX i:Z, EX cfi:Int128, EX cgi:Int128, PROP (
       i128_val cfi = Z.shiftr (u * (fi i) + v * (gi i)) (62*i);
       i128_val cgi = Z.shiftr (q * (fi i) + r * (gi i)) (62*i) )
       LOCAL (temp _r (Vlong (Int64.repr r));
       temp _q (Vlong (Int64.repr q)); temp _v (Vlong (Int64.repr v));
       temp _u (Vlong (Int64.repr u));
       temp _M62 (Vlong (Int64.repr (Z.ones 62)));
       lvar _cg t_secp256k1_u128 v_cg; lvar _cf t_secp256k1_u128 v_cf;
       temp _len (Vint (Int.repr (Z.of_nat len)));
       temp _f ptrf; temp _g ptrg; temp _t ptrt)
       SEP (i128_at Tsh v_cg cgi;
       i128_at Tsh v_cf cfi;
       data_at shf t_secp256k1_modinv64_signed62
         (Signed62.pad (firstn (Z.to_nat (i - 1)) (Signed62.reprn len ((u * f + v * g) / 2^62)) ++ skipn (Z.to_nat (i - 1)) (Signed62.reprn len f))) ptrf;
       data_at shg t_secp256k1_modinv64_signed62
         (Signed62.pad (firstn (Z.to_nat (i - 1)) (Signed62.reprn len ((q * f + r * g) / 2^62)) ++ skipn (Z.to_nat (i - 1)) (Signed62.reprn len g))) ptrg;
       data_at sht t_secp256k1_modinv64_trans2x2 T ptrt))%assert.

  - (* base: i=1 invariant holds from the bottom-limb accumulators *)
    Exists cf1 cg1.
    change (62 * 1) with 62.
    rewrite !Z.shiftr_div_pow2 by lia.
    rewrite Hcf1, Hcg1.
    entailer!!.

  - (* step: load limb i, accumulate, store the masked low 62 bits into limb i-1 *)
    rename cfi into cfi0.
    rename cgi into cgi0.
    Intros.
    rename H into Hi_bnd.
    rename H0 into Hcfi0.
    rename H1 into Hcgi0.

    (* fi = f->v[i] *)
    forward.
    { rewrite !Signed62.pad_nth by (rewrite Hlength_firstn_skipn; lia).
      entailer. }
    rewrite !Signed62.pad_nth by (rewrite Hlength_firstn_skipn; lia).

    (* gi = g->v[i] *)
    forward.
    { rewrite !Signed62.pad_nth by (rewrite Hlength_firstn_skipn; lia).
      entailer. }
    rewrite !Signed62.pad_nth by (rewrite Hlength_firstn_skipn; lia).

    (* the spliced limb i is still the OLD limb i (only 0..i-2 were overwritten) *)
    rewrite !Znth_app2 by (rewrite Zlength_firstn, Signed62.reprn_Zlength; lia).
    rewrite !Zlength_firstn.
    rewrite !Signed62.reprn_Zlength, !Znth_skipn by lia.
    replace (i - Z.min (Z.max 0 (i - 1)) (Z.of_nat len) + (i - 1)) with i by lia.
    rewrite !HZnth by lia.
    fold (fi (i + 1)) (gi (i + 1)).

    (* specialise the window bounds at i and i+1, in 2^(62*i) * 2^k form *)
    assert (Hi01 : 0 <= i + 1) by lia.
    assert (Hi0 : 0 <= i) by lia.
    specialize (Hfi _ Hi01).
    specialize (Hgi _ Hi01).
    rewrite !Z.mul_add_distr_l, !Z.pow_add_r in Hfi, Hgi by lia.

    (* HfiS/HgiS: the loaded limb (the shifted (i+1)-window) is a valid Int64 *)
    assert (HfiS : -2^63 <= Z.shiftr (fi (i + 1)) (62 * i) < 2^63).
    { apply shiftr_bounds.
      change (2^63) with (2^(62*1) * 2^1).
      nia. }

    assert (HgiS : -2^63 <= Z.shiftr (gi (i + 1)) (62 * i) < 2^63).
    { apply shiftr_bounds.
      change (2^63) with (2^(62*1) * 2^1).
      nia. }

    assert (Hfi_boundA : -2^63 <= Z.shiftr (fi (i + 1)) (62 * i) <= 2^63) by lia.
    assert (Hfi_boundB : -(2^62 * 2^63) <= u * Z.shiftr (fi (i + 1)) (62 * i) <= 2^62 * 2^63) by (apply H6262i; lia).
    assert (Hgi_boundA : -2^63 <= Z.shiftr (gi (i + 1)) (62 * i) <= 2^63) by lia.
    assert (Hgi_boundB : -(2^62 * 2^63) <= v * Z.shiftr (gi (i + 1)) (62 * i) <= 2^62 * 2^63) by (apply H6262i; lia).

    specialize (Hufi _ Hi0).
    specialize (Hvgi _ Hi0).
    specialize (Hqfi _ Hi0).
    specialize (Hrgi _ Hi0).
    rewrite !Z.pow_add_r in Hufi, Hvgi, Hqfi, Hrgi by lia.

    (* Hfgi_boundA: the running cf window fits in [-2^64, 2^64] *)
    assert (Hfgi_boundA : -2^64 <= Z.shiftr (u * fi i + v * gi i) (62 * i) <= 2^64).
    { assert (Hp : 0 < 2 ^ (62 * i)) by (apply Z.pow_pos_nonneg; lia).
      assert (H264 : 2 ^ 62 * 2 ^ 1 + 2 ^ 62 * 2 ^ 1 <= 2 ^ 64)
        by (replace 64 with (62 + 2) by lia; rewrite Z.pow_add_r by lia; lia).
      (* clear -: nia is exponential in the size of the VST context here *)
      assert (Hb : 2 ^ (62 * i) * (-2^64) <= u * fi i + v * gi i < 2 ^ (62 * i) * (2^64 + 1))
        by (clear -Hufi Hvgi Hp H264; nia).
      pose proof (shiftr_bounds _ _ _ _ Hb).
      lia. }

    (* model-typed wrappers for the limb-i loads *)
    set (fiI := mkInt64 (Z.shiftr (fi (i + 1)) (62 * i)) HfiS).
    set (giI := mkInt64 (Z.shiftr (gi (i + 1)) (62 * i)) HgiS).

    assert (HfiI : i64_val fiI = Z.shiftr (fi (i + 1)) (62 * i)) by reflexivity.
    assert (HgiI : i64_val giI = Z.shiftr (gi (i + 1)) (62 * i)) by reflexivity.

    (* secp256k1_i128_accum_mul(&cf, u, fi) -- overflow PRE from Hfgi_boundA/Hfi_boundB *)
    forward_call (v_cf, cfi0, uI, fiI, Tsh).
    Intros cfi1.
    rename H into Hcfi1.
    rewrite Hcfi0, HuI, HfiI in Hcfi1.

    (* secp256k1_i128_accum_mul(&cf, v, gi) *)
    forward_call (v_cf, cfi1, vI, giI, Tsh).
    Intros cfi2.
    rename H into Hcfi2.
    rewrite Hcfi1, HvI, HgiI in Hcfi2.

    (* the same product / window bounds for the cg accumulator *)
    assert (Hfi_boundC : -(2^62 * 2^63) <= q * Z.shiftr (fi (i + 1)) (62 * i) <= 2^62 * 2^63) by (apply H6262i; lia).
    assert (Hgi_boundC : -(2^62 * 2^63) <= r * Z.shiftr (gi (i + 1)) (62 * i) <= 2^62 * 2^63) by (apply H6262i; lia).

    assert (Hfgi_boundB : -2^64 <= Z.shiftr (q * fi i + r * gi i) (62 * i) <= 2^64).
    { assert (Hp : 0 < 2 ^ (62 * i)) by (apply Z.pow_pos_nonneg; lia).
      assert (H264 : 2 ^ 62 * 2 ^ 1 + 2 ^ 62 * 2 ^ 1 <= 2 ^ 64)
        by (replace 64 with (62 + 2) by lia; rewrite Z.pow_add_r by lia; lia).
      (* clear -: nia is exponential in the size of the VST context here *)
      assert (Hb : 2 ^ (62 * i) * (-2^64) <= q * fi i + r * gi i < 2 ^ (62 * i) * (2^64 + 1))
        by (clear -Hqfi Hrgi Hp H264; nia).
      pose proof (shiftr_bounds _ _ _ _ Hb).
      lia. }

    (* secp256k1_i128_accum_mul(&cg, q, fi) *)
    forward_call (v_cg, cgi0, qI, fiI, Tsh).
    Intros cgi1.
    rename H into Hcgi1.
    rewrite Hcgi0, HqI, HfiI in Hcgi1.

    (* secp256k1_i128_accum_mul(&cg, r, gi) *)
    forward_call (v_cg, cgi1, rI, giI, Tsh).
    Intros cgi2.
    rename H into Hcgi2.
    rewrite Hcgi1, HrI, HgiI in Hcgi2.

    (* _t'1 = secp256k1_i128_to_u64(&cf) *)
    forward_call (v_cf, cfi2, Tsh).
    Intros cfu.
    rename H into Hcfu.
    rewrite Hcfi2 in Hcfu.

    (* f->v[i-1] = _t'1 & M62 *)
    forward.

    (* secp256k1_i128_rshift(&cf, 62) *)
    forward_call (v_cf, cfi2, 62, Tsh).
    Intros cfi3.
    rename H into Hcfi3.
    rewrite Hcfi2 in Hcfi3.

    (* _t'2 = secp256k1_i128_to_u64(&cg) *)
    forward_call (v_cg, cgi2, Tsh).
    Intros cgu.
    rename H into Hcgu.
    rewrite Hcgi2 in Hcgu.

    (* g->v[i-1] = _t'2 & M62 *)
    forward.

    (* secp256k1_i128_rshift(&cg, 62) *)
    forward_call (v_cg, cgi2, 62, Tsh).
    Intros cgi3.
    rename H into Hcgi3.
    rewrite Hcgi2 in Hcgi3.

    (* re-establish the invariant for i+1: name the next windows and bound them.
       Expand cfi3/cgi3 = cfi2/cgi2 / 2^62, and re-express the rshift's [/ 2^62]
       as [Z.shiftr _ 62] so the window-folding [replace]s + [Z.shiftr_shiftr]
       apply exactly as in the raw-Z form. *)
    assert (Hmod6462 : forall a, Z.land (a mod 2^64) (Z.ones 62) = Z.land a (Z.ones 62)).
    { intros a.
      rewrite !Z.land_ones by lia.
      rewrite <- Znumtheory.Zmod_div_mod by (try lia; exists (2^2); reflexivity).
      reflexivity. }

    Exists cfi3 cgi3.
    rewrite Hcfi3, Hcgi3.
    rewrite <- !(Z.shiftr_div_pow2 _ 62) by lia.

    (* expose the stored value's three-term sum (cfi2/cgi2) so the window-folding
       [replace]s catch BOTH the invariant accumulator and the masked store *)
    rewrite Hcfu, Hcgu.

    (* fold the new product terms into the limb-(i+1) cf window *)
    replace (Z.shiftr (u * fi i + v * gi i) (62 * i) + u * Z.shiftr (fi (i + 1)) (62 * i) + v * Z.shiftr (gi (i + 1)) (62 * i))
     with (Z.shiftr (u * fi (i + 1) + v * gi (i + 1)) (62 * i)) by
      (rewrite (Z_div_mod_eq_full (fi (i + 1)) (2^(62 * i))) at 1;
       rewrite (Z_div_mod_eq_full (gi (i + 1)) (2^(62 * i))) at 1;
       rewrite Hfij, Hgij by lia;
       replace (u * ((2^(62 * i)) * (fi (i + 1) / (2^(62 * i))) + fi i) + v * ((2^(62 * i)) * (gi (i + 1) / (2^(62 * i))) + gi i))
        with ((u * fi i + v * gi i) + ((u * (fi (i + 1) / (2^(62 * i))) + v * (gi (i + 1) / (2^(62 * i)))) *  2^(62 * i))) by ring;
       rewrite !Z.shiftr_div_pow2, Z.div_add by lia;
       ring).

    (* fold the new product terms into the limb-(i+1) cg window *)
    replace (Z.shiftr (q * fi i + r * gi i) (62 * i) + q * Z.shiftr (fi (i + 1)) (62 * i) + r * Z.shiftr (gi (i + 1)) (62 * i))
     with (Z.shiftr (q * fi (i + 1) + r * gi (i + 1)) (62 * i)) by
      (rewrite (Z_div_mod_eq_full (fi (i + 1)) (2^(62 * i))) at 1;
       rewrite (Z_div_mod_eq_full (gi (i + 1)) (2^(62 * i))) at 1;
       rewrite Hfij, Hgij by lia;
       replace (q * ((2^(62 * i)) * (fi (i + 1) / (2^(62 * i))) + fi i) + r * ((2^(62 * i)) * (gi (i + 1) / (2^(62 * i))) + gi i))
        with ((q * fi i + r * gi i) + ((q * (fi (i + 1) / (2^(62 * i))) + r * (gi (i + 1) / (2^(62 * i)))) *  2^(62 * i))) by ring;
       rewrite !Z.shiftr_div_pow2, Z.div_add by lia;
       ring).
    rewrite !Z.shiftr_shiftr by lia.

    (* re-establish the splice invariant for i+1: stored limb i-1 is the masked low 62 bits.
       [i128_to_u64] returns the value mod 2^64; the subsequent [& M62] absorbs that
       extra reduction (Hmod6462). *)
    autorewrite with int_to_z.
    rewrite !Hmod6462.

    (* splice: limb i-1 of the f/g arrays now holds the new masked value *)
    rewrite !Signed62.pad_upd_Znth by (rewrite Hlength_firstn_skipn; lia).
    rewrite !upd_Znth_app2 by (rewrite Zlength_firstn, Zlength_skipn, Signed62.reprn_Zlength; lia).
    rewrite !Zlength_firstn, !Signed62.reprn_Zlength.
    replace (i - 1 - Z.min (Z.max 0 (i - 1)) (Z.of_nat len)) with 0 by lia.
    rewrite !(skipn_cons (Z.to_nat (i - 1))) by (rewrite Signed62.reprn_length; lia).
    rewrite !upd_Znth0.
    replace (S (Z.to_nat (i - 1))) with (Z.to_nat (i + 1 - 1)) by lia.

    (* the store is the low-62 window of u*f+v*g / q*f+r*g at offset 62*i *)
    replace (Z.ones 62) with (Z.ones (62 * (i + 1) - 62 * i)) by (f_equal; ring).
    rewrite <- !Z_shiftr_ones, <- !Z.shiftr_land, !Z.land_ones by lia.
    rewrite !(Z.add_mod (_*_) (_*_)), <-!(Z.mul_mod_idemp_r _ (fi (i + 1))), <-!(Z.mul_mod_idemp_r _ (gi (i+1))) by lia.
    rewrite !Hfi62, !Hgi62 by lia.
    rewrite !Z.mul_mod_idemp_r, <-!Z.add_mod by lia.
    replace (62 * (i + 1)) with (62 + 62 * i) by ring.
    rewrite <- !Z_shiftr_mod_2 by lia.

    (* refold that window as limb i-1 of [reprn len ((u*f+v*g)/2^62)] *)
    replace (62 * i) with (62 + (62 * (i - 1))) by ring.
    rewrite <- !(Z.shiftr_shiftr _ 62 (62 * (i - 1))), !(Z.shiftr_div_pow2 _ 62) by lia.
    rewrite <- !(Signed62.reprn_Znth _ len) by lia.
    rewrite !Znth_cons by (rewrite Signed62.reprn_Zlength; lia).

    (* re-assemble firstn (i-1) ++ [limb i-1] as firstn i of the new reprn *)
    rewrite !app_assoc, !firstn_app, <- Z2Nat.inj_add by lia.
    replace (i - 1 + 1) with (i + 1 - 1) by lia.
    rewrite !(Z.add_comm _ 62).
    entailer!!.

  - (* ===== Final limb: f->v[len-1] = cf, g->v[len-1] = cg ===== *)
    Intros cfL cgL.
    rename H into HcfL.
    rename H0 into HcgL.
    unfold fi, gi in HcfL, HcgL.
    rewrite !Z.eqb_refl in HcfL, HcgL.

    (* Hcfdg: c*f + d*g fits 2^(63 + 62*len) when |c|+|d| <= 2^62 *)
    pose proof (accum_bound_62 (62 * Z.of_nat len) f g ltac:(lia) Hf_bnd Hg_bnd) as Hcfdg.

    assert (Hufvg : -(2 ^ 63 * 2 ^ (62 * Z.of_nat len)) <= u * f + v * g < 2 ^ 63 * 2 ^ (62 * Z.of_nat len))
      by (apply Hcfdg; lia).
    assert (Hqfrg : -(2 ^ 63 * 2 ^ (62 * Z.of_nat len)) <= q * f + r * g < 2 ^ 63 * 2 ^ (62 * Z.of_nat len))
      by (apply Hcfdg; lia).

    (* _t'3 = secp256k1_i128_to_i64(&cf) *)
    forward_call (v_cf, cfL, Tsh).
    { rewrite HcfL.
      apply shiftr_bounds.
      nia. }
    Intros cfr.
    rename H into Hcfr.
    rewrite HcfL in Hcfr.

    (* f->v[len-1] = _t'3 *)
    forward.

    (* _t'4 = secp256k1_i128_to_i64(&cg) *)
    forward_call (v_cg, cgL, Tsh).
    { rewrite HcgL.
      apply shiftr_bounds.
      nia. }
    Intros cgr.
    rename H into Hcgr.
    rewrite HcgL in Hcgr.

    (* g->v[len-1] = _t'4 *)
    forward.

    (* close: stored top limbs equal reprn_last of the post-step f1,g1 *)
    unfold int64_to_val.
    rewrite Hcfr, Hcgr.
    rewrite !Signed62.pad_upd_Znth by (rewrite Hlength_firstn_skipn; lia).
    rewrite !upd_Znth_app2 by (rewrite Zlength_firstn, Zlength_skipn, Signed62.reprn_Zlength; lia).
    rewrite !Zlength_firstn, !Signed62.reprn_Zlength.
    replace (Z.of_nat len - 1 - Z.min (Z.max 0 (Z.of_nat len - 1)) (Z.of_nat len)) with 0 by lia.
    rewrite !(skipn_cons (Z.to_nat (Z.of_nat len - 1))) by (rewrite Signed62.reprn_length; lia).
    rewrite !upd_Znth0.
    replace (S (Z.to_nat (Z.of_nat len - 1))) with (len) by lia.
    rewrite !skipn_short by (rewrite Signed62.reprn_length; lia).

    (* the stored top limb is the (len-1)-window of the post-step value *)
    replace (62 * Z.of_nat len) with (62 + (62 * (Z.of_nat len - 1))) by ring.
    rewrite <- !(Z.shiftr_shiftr _ 62 (62 * (Z.of_nat len - 1))), !(Z.shiftr_div_pow2 _ 62) by lia.

    (* name index len-1 as the last position of the reprn lists *)
    replace (Z.to_nat (Z.of_nat len - 1)) with (Init.Nat.pred (Datatypes.length (Signed62.reprn len ((u * f + v * g) / 2 ^ 62)))) at 1
     by (rewrite Signed62.reprn_length; lia).
    replace (Z.to_nat (Z.of_nat len - 1)) with (Init.Nat.pred (Datatypes.length (Signed62.reprn len ((q * f + r * g) / 2 ^ 62))))
     by (rewrite Signed62.reprn_length; lia).

    (* fold removelast ++ [last] back into the full reprn, then undo /2^62 *)
    rewrite <- !removelast_firstn_len, <- !(Signed62.reprn_last _ len default) by lia.
    rewrite <- !app_removelast_last by (rewrite <- length_zero_iff_nil, Signed62.reprn_length; lia).
    rewrite <- Htransf, <- Htransg, !(Z.mul_comm (2 ^ 62)), !Z.div_mul by lia.
    entailer!!.
Qed.
