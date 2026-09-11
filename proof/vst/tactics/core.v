(** * vst.tactics.core: generic verification automation (subsystem-free). *)
(** Copyright (C) 2026 remix7531
    SPDX-License-Identifier: MIT *)

(** The generic automation backbone shared by every subsystem's body proofs:

    - the SINGLE [rep_lia_setup2 ::=] override (auto-poses the carried range
      fact for every word value in the goal) -- extend it here, never
      re-override elsewhere;
    - [rep_lia] projector/constant rewrites ([u64_val_mk], [int64_modulus_eq]);
    - [Inhabitant] instances for the model word types (for [deadvars!]);
    - [fold_limb]/[refold_div] goal normalisation over [theory.bits];
    - the pure carry vocabulary ([Z_div_add_carry], [carry_value],
      [limb_add_0/1/2], [ltu_carry_b2z], [eqm_of_mod_eq]);
    - generic [Int64] shift / mul / zero-test bridges, on top of the word
      <-> [Z] bridges and the [int_to_z] database re-exported from
      [vst.integers].

    Subsystem-specific automation lives in [tactics.int128] / [tactics.scalar]
    / [tactics.field]; this file never imports a contract. *)

Require Export secp256k1.vst.base.
Require Export secp256k1.theory.integers.arithmetic.
Require Export secp256k1.theory.integers.bits.
Require Export secp256k1.vst.array_data_at.
Require Export secp256k1.vst.integers.
Require Export secp256k1.theory.int128.int128.
Require Export secp256k1.theory.int128.acc.
Require Export secp256k1.theory.scalar.limbs.
Require secp256k1.specification.
Import specification.Math.
Export specification.Math.field.
Export specification.Math.scalar.

(* ================================================================= *)
(** ** rep_lia constant + projector rewrites. *)

(** Normalise the two common alternative spellings of [2^64] that
    arise after VST tactics partially reduce constants.  Registered
    in [rep_lia] so [autorewrite] folds them before [lia] runs. *)
Lemma int64_modulus_eq : Int64.modulus = 2^64.
Proof. reflexivity. Qed.
Lemma pow_pos_2_64_eq : Z.pow_pos 2 64 = 2^64.
Proof. reflexivity. Qed.
#[export] Hint Rewrite int64_modulus_eq pow_pos_2_64_eq : rep_lia.

(** Reduction rules for record projections.
    These let [rep_lia] and VST's internal solvers see through
    [mkUInt64]/[mkAcc] wrappers without manual [simpl]. *)
Lemma u64_val_mk : forall z H, u64_val (mkUInt64 z H) = z.
Proof. reflexivity. Qed.
Lemma acc_val_mk : forall z H, acc_val (mkAcc z H) = z.
Proof. reflexivity. Qed.
#[export] Hint Rewrite u64_val_mk acc_val_mk : rep_lia.

(** Extend VST's [rep_lia_setup2] hook so [rep_lia] auto-introduces
    the carried range fact for every [u64_val ?x] / [u128_val ?x] /
    [acc_val ?x] in the goal -- same mechanism VST uses for
    [Int.unsigned] / [Int64.signed].  This removes the need to
    [pose proof (u64_range x)] manually before [rep_lia] calls. *)
Lemma u128_val_hi_lt : forall x : UInt128, u128_val x / 2^64 < 2^64.
Proof.
  intros. apply Z.div_lt_upper_bound; [lia|].
  pose proof (u128_range x). lia.
Qed.

(** Experiment: register the common divisor/modulus bounds with the
    [rep_lia] hint database.  These fire via [eauto with rep_lia]
    when [rep_lia] cannot close a goal by [lia] alone, letting
    [rep_lia] discharge [0 <= x mod _ < _] / [_ / _ < _] inline. *)
#[export] Hint Resolve Z.mod_pos_bound Z.div_pos Z.div_lt_upper_bound : rep_lia.

(** Make the two moduli known to [rep_lia] by value: pose [c = v] with [v]
    computed from [c]'s definition (never restated), unless the equation is
    already in context.  With it, a goal such as [0 <= v < secp256k1_N] for a
    small literal [v] closes by [rep_lia] with no [unfold secp256k1_N]. *)
Ltac pose_modulus_value c :=
  lazymatch goal with
  | H : c = _ |- _ => idtac
  | _ => let v := eval unfold c in c in pose proof (eq_refl : c = v)
  end.

Ltac rep_lia_setup2 ::=
  pose_modulus_value secp256k1_N;
  pose_modulus_value secp256k1_P;
  pose_lemmas u64_val u64_range;
  pose_lemmas u128_val u128_range;
  pose_lemmas u128_val u128_val_hi_lt;
  pose_lemmas acc_val acc_range;
  pose_lemmas u256_val u256_range;
  (* signed: auto-pose the carried two-sided range for every i64/i128 value *)
  pose_lemmas i64_val i64_range;
  pose_lemmas i128_val i128_range.

(* ================================================================= *)
(** ** Carry-bound lemmas -- [carry_div_ub] / [reduce_u128_div_step].

    These lemmas replace the local [carry_bound] / [reduce_u128_bound]
    Ltac tactics with declarative facts that callers can [apply] and
    discharge side conditions with [rep_lia] or [lia]. *)

(** Monotonicity of division by [2^64] over the integers, packaged for
    direct use after rewriting an accumulator carry as [acc / 2^64].
    Used to discharge [acc_val carry_k <= bound] goals in
    [Verif_scalar_mul_512]. *)
Lemma carry_div_ub : forall a b,
  a <= b -> a / 2^64 <= b / 2^64.
Proof.
  intros. apply Z.div_le_mono; lia.
Qed.

(** Convenience form: [a / 2^64 <= c] from an intermediate numerator
    bound [b] and a lia-friendly slack [b <= 2^64 * c + 2^64 - 1].
    Both side conditions are closed by a single [lia]. *)
Lemma carry_div_ub_eq : forall a b c,
  a <= b -> b <= 2^64 * c + 2^64 - 1 -> a / 2^64 <= c.
Proof.
  intros a b c Hab Hslack.
  enough (a / 2^64 < c + 1) by lia.
  apply Z.div_lt_upper_bound; lia.
Qed.

(** [u128 = carry / 2^64 + lo] fits in [2^128]: after a carry-divide
    step, [x / 2^64 < 2] when [x < 2 * 2^64].  Used to discharge the
    [u128_val + u64_val < 2^128] precondition of
    [secp256k1_u128_accum_u64] in [Verif_scalar_reduce]. *)
Lemma reduce_u128_div_step : forall x y,
  0 <= x -> x < 2 * 2^64 -> 0 <= y < 2^64 ->
  x / 2^64 + y < 2^128.
Proof.
  intros.
  assert (0 <= x / 2^64 < 2)
    by (split; [apply Z.div_pos | apply Z.div_lt_upper_bound]; lia).
  lia.
Qed.

(** Hint database [carry_bounds] collects the carry-bound lemmas.
    Lemmas are typically applied explicitly at call sites for clarity,
    but [eauto with carry_bounds] can dispatch the simpler shapes
    automatically. *)
#[export] Hint Resolve carry_div_ub carry_div_ub_eq
  reduce_u128_div_step : carry_bounds.

(* ================================================================= *)
(** ** Inhabitant instances -- default elements for [deadvars!]. *)

#[export] Instance Inhabitant_UInt64_ : Inhabitant UInt64 := mkUInt64 0 ltac:(lia).
#[export] Instance Inhabitant_UInt128_ : Inhabitant UInt128 := mkUInt128 0 ltac:(lia).
#[export] Instance Inhabitant_Acc_ : Inhabitant Acc := mkAcc 0 ltac:(lia).
#[export] Instance Inhabitant_Int64_ : Inhabitant Int64 := mkInt64 0 ltac:(lia).
#[export] Instance Inhabitant_Int128_ : Inhabitant Int128 := mkInt128 0 ltac:(lia).
#[export] Instance Inhabitant_UInt256_ : Inhabitant UInt256 := mkUInt256 0 ltac:(lia).
#[export] Instance Inhabitant_UInt512_ : Inhabitant UInt512 := mkUInt512 0 ltac:(lia).
#[export] Instance Inhabitant_Scalar_ : Inhabitant Scalar :=
  mkScalar 0 ltac:(unfold secp256k1_N; lia).

(* ================================================================= *)
(** ** Signed wrapper-projection rewrites

    Analogues of [u64_val_mk] / [acc_val_mk]: let [rep_lia] (and the
    [autorewrite with rep_lia] callers) see through [mkInt64] / [mkInt128]
    without a manual [simpl].  The companion [int128_to_val_limb] bridge
    lives with the [to_val_limb] lemmas below. *)
Lemma i64_val_mk : forall z H, i64_val (mkInt64 z H) = z.
Proof. reflexivity. Qed.
Lemma i128_val_mk : forall z H, i128_val (mkInt128 z H) = z.
Proof. reflexivity. Qed.
#[export] Hint Rewrite i64_val_mk i128_val_mk : rep_lia.

(* ================================================================= *)
(** ** Goal normalisation over [theory.bits] -- [refold_div] / [fold_limb]. *)

(** Re-fold [match Z.div_eucl a b with (q,_) => q] back to [a / b].
    [Z.div] sometimes appears in goals as its underlying [match]
    after [simpl]/[entailer!] partially reduce it; the limb fold
    rewrites below need the [/] form to match. *)
Ltac refold_div :=
  repeat match goal with
  | |- context [match Z.div_eucl ?a ?b with (q, _) => q end] =>
      change (match Z.div_eucl a b with (q, _) => q end) with (a / b)
  | H : context [match Z.div_eucl ?a ?b with (q, _) => q end] |- _ =>
      change (match Z.div_eucl a b with (q, _) => q end) with (a / b) in H
  end.

(** Fold inline [(x / 2^k) mod 2^64] occurrences to [limb (2^64) v i].
    Most-specific (largest power) tried first so that
    [(v / 2^64) mod 2^64] resolves to [limb (2^64) v 1] rather than
    [limb (2^64) (v / 2^64) 0]. *)
Ltac fold_limb :=
  refold_div;
  repeat first
    [ progress (rewrite !limb_fold7 in * )
    | progress (rewrite !limb_fold6 in * )
    | progress (rewrite !limb_fold5 in * )
    | progress (rewrite !limb_fold4 in * )
    | progress (rewrite !limb_fold3 in * )
    | progress (rewrite !limb_fold2 in * )
    | progress (rewrite !limb_fold1 in * )
    | progress (rewrite !limb_fold0 in * ) ].

(* ----------------------------------------------------------------- *)
(** *** limb (2^64) properties *)

(** [limb (2^64) x i] is in unsigned 64-bit range. *)
Lemma limb_u64_range : forall x i,
  0 <= limb (2^64) x i <= Int64.max_unsigned.
Proof.
  intros.
  unfold limb.
  pose proof (Z.mod_pos_bound (x / (2^64)^Z.of_nat i) (2^64) ltac:(lia)).
  rep_lia.
Qed.

(** Generic bound for [limb (2^64) x i]: always [0 <= _ < 2^64].
    Used by [rep_lia_setup2] below to auto-pose this fact whenever
    a [limb (2^64) ?x ?i] subterm appears in the goal. *)
Lemma limb_u64_lt : forall x i, 0 <= limb (2^64) x i < 2^64.
Proof. intros. unfold limb. apply Z.mod_pos_bound. lia. Qed.

(* rep_lia_setup2 -- the auto-pose extension was attempted but moved
   to per-call sites for stability across forward_call wrappers. *)

(** For a value in [0, 2^64), limb 0 is the value itself. *)
Lemma limb_u64_val_0 : forall (a : UInt64), limb (2^64) (u64_val a) 0 = u64_val a.
Proof.
  intros.
  unfold limb.
  rewrite Z.pow_0_r, Z.div_1_r.
  apply Z.mod_small. rep_lia.
Qed.

(** For a value in [0, 2^64), limb 1 is 0. *)
Lemma limb_u64_val_1 : forall (a : UInt64), limb (2^64) (u64_val a) 1 = 0.
Proof.
  intros.
  unfold limb.
  rewrite Z.pow_1_r.
  rewrite Z.div_small by rep_lia.
  reflexivity.
Qed.

(** Top limb of a value bounded by [2^(64*(i+1))] is 0. *)
Lemma limb_high_zero : forall x i,
  0 <= x < 2^(64 * Z.of_nat (S i)) ->
  limb (2^64) x (S i) = 0.
Proof.
  intros.
  unfold limb.
  replace ((2^64) ^ Z.of_nat (S i)) with (2^(64 * Z.of_nat (S i))) by
    (rewrite <- Z.pow_mul_r by lia; f_equal; lia).
  rewrite Z.div_small by lia.
  reflexivity.
Qed.

(* ----------------------------------------------------------------- *)
(** *** Multiplication bounds *)

(** The product of two 64-bit unsigned integers is at most [(2^64-1)^2]. *)
Lemma u64_mul_bound : forall (a b : UInt64),
  u64_val a * u64_val b <= (2^64 - 1) * (2^64 - 1).
Proof. intros. apply Z.mul_le_mono_nonneg; rep_lia. Qed.

(** Product of two 32-bit values fits in 64 bits. *)
Lemma mul_u32_range : forall a b,
  0 <= a <= Int.max_unsigned ->
  0 <= b <= Int.max_unsigned ->
  0 <= a * b <= Int64.max_unsigned.
Proof.
  intros.
  unfold Int64.max_unsigned, Int.max_unsigned in *.
  simpl in *.
  split.
  - apply Z.mul_nonneg_nonneg; lia.
  - assert (a * b <= (2^32 - 1) * (2^32 - 1)) by (apply Z.mul_le_mono_nonneg; lia).
    lia.
Qed.

(** The product of two 64-bit unsigned integers fits in 128 bits. *)
Lemma mul_u64_lt_u128 : forall a b,
  0 <= a < 2^64 ->
  0 <= b < 2^64 ->
  a * b < 2^128.
Proof.
  intros a b Ha Hb.
  assert (a * b <= (2^64 - 1) * (2^64 - 1))
    by (apply Z.mul_le_mono_nonneg; lia).
  lia.
Qed.

(** The high half of a 64x64 multiplication fits strictly:
    [(a * b) / 2^64 <= 2^64 - 2]. *)
Lemma mul_u64_hi_le : forall a b,
  0 <= a < 2^64 -> 0 <= b < 2^64 ->
  (a * b) / 2^64 <= 2^64 - 2.
Proof.
  intros.
  enough ((a * b) / 2^64 < 2^64 - 1) by lia.
  apply Z.div_lt_upper_bound; [lia|].
  nia.
Qed.

(* ----------------------------------------------------------------- *)
(** *** eval4 / u256 *)

(** [eval4 (2^64) (u64_val (u256_limb x 0)) ... = u256_val x]. *)
Lemma u256_as_eval4 : forall (x : UInt256),
  eval4 (2^64)
    (u64_val (u256_limb x 0)) (u64_val (u256_limb x 1))
    (u64_val (u256_limb x 2)) (u64_val (u256_limb x 3))
  = u256_val x.
Proof.
  intros.
  unfold u256_limb.
  simpl u64_val.
  change (limb (2^64) (u256_val x) 0) with (limb (2^64) (u256_val x) 0).
  change (limb (2^64) (u256_val x) 1) with (limb (2^64) (u256_val x) 1).
  change (limb (2^64) (u256_val x) 2) with (limb (2^64) (u256_val x) 2).
  change (limb (2^64) (u256_val x) 3) with (limb (2^64) (u256_val x) 3).
  apply eval4_limbs; rep_lia.
Qed.

(* ----------------------------------------------------------------- *)
(** *** Carry arithmetic *)

(**
    These lemmas justify the limb-by-limb addition used across all
    carry-propagating proofs (muladd, sumadd, accum_u64, etc.).
    The core identity is

      [(a + b) / M  =  a/M  +  b/M  +  (a mod M + b mod M) / M]

    where the last term is the carry (0 or 1).  From this we derive
    that each 64-bit limb of [a + b] equals the corresponding limb
    sum plus carry-in, modulo [2^64]. *)

(** Carry decomposition of integer division. *)
Lemma Z_div_add_carry : forall a b M,
  0 < M -> 0 <= a -> 0 <= b ->
  (a + b) / M = a / M + b / M + (a mod M + b mod M) / M.
Proof.
  intros.
  rewrite (Z.div_mod a M) at 1 by lia.
  rewrite (Z.div_mod b M) at 1 by lia.
  replace (M * (a / M) + a mod M + (M * (b / M) + b mod M))
    with ((a / M + b / M) * M + (a mod M + b mod M)) by ring.
  rewrite Z.div_add_l by lia.
  reflexivity.
Qed.

(** The carry from adding two residues is 0 or 1. *)
Lemma carry_value : forall a b M,
  0 < M -> 0 <= a -> 0 <= b ->
  (a mod M + b mod M) / M = if a mod M + b mod M <? M then 0 else 1.
Proof.
  intros.
  destruct (a mod M + b mod M <? M) eqn:Hc.
  - apply Z.ltb_lt in Hc.
    apply Z.div_small.
    split.
    + apply Z.add_nonneg_nonneg; apply Z.mod_pos_bound; lia.
    + assumption.
  - apply Z.ltb_ge in Hc.
    symmetry.
    apply Z.div_unique with (r := a mod M + b mod M - M).
    + assert (a mod M < M) by (apply Z.mod_pos_bound; lia).
      assert (b mod M < M) by (apply Z.mod_pos_bound; lia).
      lia.
    + lia.
Qed.

(* ----------------------------------------------------------------- *)
(** *** Limb-wise addition *)

(** Bridge: [x mod 2^64 = y] implies [Int64.eqm x y]. *)
Lemma eqm_of_mod_eq : forall x y,
  x mod 2^64 = y -> Int64.eqm x y.
Proof.
  intros x y H.
  unfold Int64.eqm.
  change Int64.modulus with (2^64).
  rewrite <- H.
  apply Zbits.eqmod_mod.
  lia.
Qed.

(** Limb 0: sum of low limbs mod 2^64 = low limb of sum.
    No incoming carry for the lowest digit. *)
Lemma limb_add_0 : forall a b,
  0 <= a -> 0 <= b ->
  (limb (2^64) a 0 + limb (2^64) b 0) mod 2^64 = limb (2^64) (a + b) 0.
Proof.
  intros.
  unfold limb.
  simpl Z.of_nat.
  rewrite Z.pow_0_r, !Z.div_1_r.
  rewrite Z.add_mod by lia.
  rewrite Z.mod_mod by lia.
  rewrite Z.mod_mod by lia.
  rewrite <- Z.add_mod by lia.
  reflexivity.
Qed.

(** Limb 1: sum of middle limbs + carry-in mod 2^64 = middle limb of sum. *)
Lemma limb_add_1 : forall a b,
  0 <= a -> 0 <= b ->
  (limb (2^64) a 1 + (limb (2^64) b 1 +
    (if limb (2^64) a 0 + limb (2^64) b 0 <? 2^64 then 0 else 1))) mod 2^64
  = limb (2^64) (a + b) 1.
Proof.
  intros.
  unfold limb.
  simpl Z.of_nat.
  rewrite Z.pow_0_r, !Z.div_1_r, Z.pow_1_r.

  (* Decompose (a+b)/2^64 via carry identity *)
  replace ((a + b) / 2^64)
    with (a / 2^64 + b / 2^64 + (a mod 2^64 + b mod 2^64) / 2^64)
    by (symmetry; apply Z_div_add_carry; lia).
  rewrite carry_value by lia.

  (* Strip inner mods through the outer mod *)
  rewrite Zplus_mod_idemp_l.
  replace (a / 2^64 + ((b / 2^64) mod 2^64 +
    (if a mod 2^64 + b mod 2^64 <? 2^64 then 0 else 1)))
    with ((a / 2^64 +
    (if a mod 2^64 + b mod 2^64 <? 2^64 then 0 else 1)) +
    (b / 2^64) mod 2^64) by lia.
  rewrite Zplus_mod_idemp_r.
  f_equal.
  lia.
Qed.

(** Limb 2: sum of high limbs + carry-in mod 2^64 = high limb of sum.
    Requires [b < 2^128] (i.e. b fits in 2 limbs) so that [b/(M*M) = 0]. *)
Lemma limb_add_2 : forall a b,
  0 <= a -> 0 <= b -> b < 2^128 ->
  (limb (2^64) a 2 + (if limb (2^64) a 1 + limb (2^64) b 1 +
    (if limb (2^64) a 0 + limb (2^64) b 0 <? 2^64 then 0 else 1) <? 2^64 then 0 else 1))
  mod 2^64 = limb (2^64) (a + b) 2.
Proof.
  intros a b Ha Hb Hb128.

  (* Setup: unfold limb, introduce M = 2^64 *)
  unfold limb.
  simpl Z.of_nat.
  rewrite Z.pow_0_r, !Z.div_1_r, Z.pow_1_r.
  change ((2^64)^2) with (2^64 * 2^64).
  set (M := (2^64)%Z).

  (* b < M^2, so b / (M*M) = 0 *)
  assert (Hbdiv : b / (M * M) = 0).
  { apply Z.div_small.
    unfold M in *.
    lia. }

  (* Decompose (a+b)/(M*M) via carry identity, cancel b/(M*M) = 0 *)
  replace ((a + b) / (M * M))
    with (a / (M * M) + b / (M * M) +
          (a mod (M * M) + b mod (M * M)) / (M * M))
    by (symmetry; apply Z_div_add_carry; [unfold M; lia | lia | lia]).
  rewrite Hbdiv, Z.add_0_r.

  (* Name the four half-limbs and establish ranges *)
  set (la0 := a mod M).
  set (lb0 := b mod M).
  set (la1 := a / M mod M).
  set (lb1 := b / M mod M).
  assert (Hla0 : 0 <= la0 < M) by (unfold la0, M; apply Z.mod_pos_bound; lia).
  assert (Hlb0 : 0 <= lb0 < M) by (unfold lb0, M; apply Z.mod_pos_bound; lia).
  assert (Hla1 : 0 <= la1 < M) by (unfold la1, M; apply Z.mod_pos_bound; lia).
  assert (Hlb1 : 0 <= lb1 < M) by (unfold lb1, M; apply Z.mod_pos_bound; lia).

  (* Define the carry from limb 1 -> limb 2 *)
  set (carry2 := if la0 + lb0 <? M
                 then if la1 + lb1 <? M then 0 else 1
                 else if la1 + lb1 + 1 <? M then 0 else 1).

  (* Show the LHS carry expression equals carry2 *)
  assert (Hcarry2_lhs :
    (if la1 + lb1 + (if la0 + lb0 <? M then 0 else 1) <? M
     then 0 else 1) = carry2).
  { unfold carry2.
    destruct (la0 + lb0 <? M) eqn:Ec0.
    all: destruct (la1 + lb1 <? M) eqn:Ec1.
    all: first [ replace (la1 + lb1 + 0) with (la1 + lb1) by lia
               | replace (la1 + lb1 + 1) with (la1 + lb1 + 1) by lia ].
    all: try rewrite Ec1.
    all: try reflexivity.
    all: destruct (la1 + lb1 + 1 <? M); reflexivity. }
  rewrite Hcarry2_lhs.

  (* Recombine a mod (M*M) and b mod (M*M) into two-limb form *)
  replace (a mod (M * M)) with (la0 + la1 * M)
    by (unfold la0, la1, M; rewrite Zmod_recombine by lia; ring).
  replace (b mod (M * M)) with (lb0 + lb1 * M)
    by (unfold lb0, lb1, M; rewrite Zmod_recombine by lia; ring).

  (* Show the combined two-limb sum / (M*M) equals carry2 *)
  assert (Hcarry_val :
    (la0 + la1 * M + (lb0 + lb1 * M)) / (M * M) = carry2).
  { unfold carry2.
    destruct (la0 + lb0 <? M) eqn:Ec0; destruct (la1 + lb1 <? M) eqn:Ec1.
    - (* no carry from limb 0, no carry from limb 1 *)
      apply Z.ltb_lt in Ec0.
      apply Z.ltb_lt in Ec1.
      apply Z.div_small.
      lia.
    - (* no carry from limb 0, carry from limb 1 *)
      apply Z.ltb_lt in Ec0.
      apply Z.ltb_ge in Ec1.
      symmetry.
      apply Z.div_unique with (r := la0 + lb0 + (la1 + lb1 - M) * M); lia.
    - (* carry from limb 0, no carry from limb 1 *)
      apply Z.ltb_ge in Ec0.
      apply Z.ltb_lt in Ec1.
      destruct (la1 + lb1 + 1 <? M) eqn:Ec1'.
      + apply Z.ltb_lt in Ec1'.
        apply Z.div_small.
        lia.
      + apply Z.ltb_ge in Ec1'.
        symmetry.
        apply Z.div_unique
          with (r := la0 + lb0 - M + (la1 + lb1 + 1 - M) * M); lia.
    - (* carry from limb 0, carry from limb 1 *)
      apply Z.ltb_ge in Ec0.
      apply Z.ltb_ge in Ec1.
      destruct (la1 + lb1 + 1 <? M) eqn:Ec1'.
      + apply Z.ltb_lt in Ec1'.
        symmetry.
        apply Z.div_unique
          with (r := la0 + lb0 - M + (la1 + lb1 + 1) * M); lia.
      + apply Z.ltb_ge in Ec1'.
        symmetry.
        apply Z.div_unique
          with (r := la0 + lb0 - M + (la1 + lb1 + 1 - M) * M); lia. }
  rewrite Hcarry_val.

  (* Final step: strip inner mod through outer mod *)
  rewrite Zplus_mod_idemp_l.
  reflexivity.
Qed.

(** Carry detection via [ltu]: [b2z (repr(c0+tl) < repr(tl))] equals
    the arithmetic carry (0 if no wrap, 1 if wrap). *)
Lemma ltu_carry_b2z : forall c0 tl,
  0 <= c0 <= Int64.max_unsigned ->
  0 <= tl <= Int64.max_unsigned ->
  Z.b2z (Int64.ltu (Int64.repr (c0 + tl)) (Int64.repr tl)) =
  (if c0 + tl <? Int64.modulus then 0 else 1).
Proof.
  intros.
  destruct (c0 + tl <? Int64.modulus) eqn:Hcarry.
  - (* no wrap: c0+tl fits, so repr preserves order and ltu = false *)
    apply Z.ltb_lt in Hcarry.
    unfold Int64.ltu.
    rewrite !Int64.unsigned_repr by rep_lia.
    rewrite zlt_false by lia.
    reflexivity.
  - (* wrap: c0+tl overflows, repr wraps around, so ltu is true *)
    apply Z.ltb_ge in Hcarry.
    unfold Int64.ltu.
    rewrite (Int64.unsigned_repr tl) by rep_lia.
    rewrite Int64.unsigned_repr_eq.
    replace ((c0 + tl) mod Int64.modulus)
      with (c0 + tl - Int64.modulus)
      by (symmetry; apply Zmod_unique with 1; rep_lia).
    rewrite zlt_true by rep_lia.
    reflexivity.
Qed.

(* ================================================================= *)
(** ** Int64 shift / division bridges

    Bridges between CompCert's [Int64] shift operations and [Z]
    division / multiplication.  Shared across the [int128] multiply
    helpers ([umul128], [mul128]) and the signed [i128] shifts
    ([i128_rshift], [i128_from_i64]). *)

(** Shift right 32 (logical) on [Int64] equals [Z] division by [2^32]
    ([Int.modulus]), for an unsigned-range argument.  Used for the
    [ll >> 32] / [lh >> 32] / [mid34 >> 32] (all [tulong]) expressions
    in both the unsigned and signed 64x64 multiply helpers. *)
Lemma Int64_shru_32 : forall x,
  0 <= x <= Int64.max_unsigned ->
  Int64.shru (Int64.repr x) (Int64.repr 32) = Int64.repr (x / Int.modulus).
Proof.
  intros.
  rewrite Int64.shru_div_two_p.
  f_equal.
  rewrite Int64.unsigned_repr by assumption.
  rewrite Int64.unsigned_repr by rep_lia.
  reflexivity.
Qed.

(** Shift left 32 on [Int64] equals [Z] multiplication by [2^32]
    ([Int.modulus]), modulo [2^64].  Used for the [mid34 << 32]
    expression in the multiply helpers' return value. *)
Lemma Int64_shl_32 : forall x,
  0 <= x <= Int64.max_unsigned ->
  Int64.shl (Int64.repr x) (Int64.repr 32) = Int64.repr (x * Int.modulus).
Proof.
  intros.
  rewrite Int64.shl_mul_two_p.
  rewrite Int64.unsigned_repr by rep_lia.
  change (two_p 32) with Int.modulus.
  apply Int64.eqm_samerepr.
  apply Int64.eqm_mult;
  apply Int64.eqm_sym;
  apply Int64.eqm_unsigned_repr.
Qed.

(** Arithmetic (signed) right shift by [k] on a signed-range value is
    signed floor division by [2^k] (the [Int64.shr] / [/] bridge),
    valid when [z] fits in a signed word and [0 <= k < 64].  Subsumes
    the [k = 32] shift in [mul128] and the general [k] shift in
    [i128_rshift]; [i128_from_i64] uses it at [k = 63]. *)
Lemma Int64_shr_div : forall z k,
  -2^63 <= z < 2^63 ->
  0 <= k < 64 ->
  Int64.shr (Int64.repr z) (Int64.repr k) = Int64.repr (z / 2^k).
Proof.
  intros z k Hz Hk.
  rewrite Int64.shr_div_two_p.
  rewrite Int64.signed_repr
    by (change Int64.min_signed with (-2^63);
        change Int64.max_signed with (2^63 - 1); lia).
  rewrite Int64.unsigned_repr
    by (change Int64.max_unsigned with (2^64 - 1); lia).
  rewrite two_p_correct.
  reflexivity.
Qed.

(** An [Int64.or] is zero iff both operands are zero (bitwise).  Shared
    by the scalar zero/equality tests [scalar_is_zero], [scalar_is_one],
    [scalar_eq], which OR a tree of limb words and test against zero. *)
Lemma int64_or_eq_zero_iff : forall x y : int64,
  Int64.or x y = Int64.zero <-> x = Int64.zero /\ y = Int64.zero.
Proof.
  intros x y.
  split.
  - intro Hq.
    split;
      apply Int64.same_bits_eq;
      intros i Hi;
      pose proof (Int64.bits_or x y i Hi) as Hb;
      rewrite Hq, Int64.bits_zero in Hb;
      rewrite Int64.bits_zero;
      symmetry in Hb;
      apply orb_false_elim in Hb;
      [apply Hb | apply Hb].
  - intros [Hx Hy].
    subst.
    apply Int64.or_zero.
Qed.

(** An in-range limb word [Int64.repr v] is zero iff its [Z] value is
    zero.  Shared by [scalar_is_zero] / [scalar_is_one]. *)
Lemma int64_repr_eq_zero_iff : forall v : Z,
  0 <= v < 2^64 ->
  (Int64.repr v = Int64.zero <-> v = 0).
Proof.
  intros v Hv.
  split.
  - intro Hq.
    apply (f_equal Int64.unsigned) in Hq.
    rewrite Int64.unsigned_repr in Hq by rep_lia.
    rewrite Int64.unsigned_zero in Hq.
    lia.
  - intro Hq.
    subst v.
    reflexivity.
Qed.

(** [xor (repr x) (repr y)] is zero iff [x = y], for in-range limbs.
    Shared by [scalar_is_one] (at [y = 1]) and [scalar_eq]. *)
Lemma int64_xor_repr_eq_zero_iff : forall x y : Z,
  0 <= x < 2^64 ->
  0 <= y < 2^64 ->
  (Int64.xor (Int64.repr x) (Int64.repr y) = Int64.zero <-> x = y).
Proof.
  intros x y Hx Hy.
  split.
  - intro Hq.
    apply Int64.xor_zero_equal in Hq.
    apply (f_equal Int64.unsigned) in Hq.
    rewrite !Int64.unsigned_repr in Hq by rep_lia.
    exact Hq.
  - intro Hq.
    subst y.
    apply Int64.xor_idem.
Qed.

(* ================================================================= *)
(** ** Reduce helper lemmas

    General-purpose lemmas factored out of [Verif_scalar_reduce] and
    [Verif_scalar_reduce_512]; reusable across any reduction proof. *)

(** [Int64.mul (repr a) (repr b) = repr (a * b)] when all values
    fit in unsigned 64-bit range. *)
Lemma Int64_mul_repr : forall a b,
  0 <= a <= Int64.max_unsigned ->
  0 <= b <= Int64.max_unsigned ->
  0 <= a * b <= Int64.max_unsigned ->
  Int64.mul (Int64.repr a) (Int64.repr b) = Int64.repr (a * b).
Proof.
  intros.
  unfold Int64.mul.
  rewrite !Int64.unsigned_repr by lia.
  reflexivity.
Qed.

(** Each carry is [< 2] because the intermediate sum is [< 2*2^64]. *)
Lemma reduce_carry_lt_2 : forall a,
  0 <= a -> a < 2 * 2^64 ->
  0 <= a / 2^64 < 2.
Proof.
  intros.
  split.
  - apply Z.div_pos; lia.
  - apply Z.div_lt_upper_bound; lia.
Qed.

(** Accumulator round identity: [lo + carry * 2^64 = acc_val acc].
    Used to telescope the carry chain in reduction proofs. *)
Lemma round_identity : forall (acc : Acc) (lo : UInt64) (carry : Acc),
  lo = acc_lo acc ->
  acc_val carry = acc_val acc / 2^64 ->
  u64_val lo + acc_val carry * 2^64 = acc_val acc.
Proof.
  intros.
  rewrite H.
  unfold acc_lo.
  simpl u64_val.
  rewrite ?limb_at_0.
  rewrite H0.
  pose proof (Z_div_mod_eq_full (acc_val acc) (2^64)).
  lia.
Qed.

(** Low half of a [UInt128]: [u64_val (u128_lo x) = u128_val x mod 2^64]. *)
Lemma u128_lo_val : forall x : UInt128,
  u64_val (u128_lo x) = u128_val x mod 2^64.
Proof.
  intros.
  unfold u128_lo.
  simpl u64_val.
  rewrite ?limb_at_0.
  reflexivity.
Qed.

(** High half of a [UInt128]: [u64_val (u128_hi x) = u128_val x / 2^64]. *)
Lemma u128_hi_val : forall x : UInt128,
  u64_val (u128_hi x) = u128_val x / 2^64.
Proof.
  intros.
  unfold u128_hi.
  simpl u64_val.
  unfold limb.
  simpl Z.of_nat.
  simpl Z.mul.
  change (64 * 1) with 64.
  rewrite Zmod_small; [reflexivity|].
  pose proof (u128_range x).
  split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia].
Qed.


(* ================================================================= *)
(** ** Accumulator carry bridges -- [muladd_limb*] / [sumadd_limb*]
    (shared by [u128_accum_mul] and the scalar muladd/sumadd impl bodies).

    The C code propagates carries through 64-bit limbs using
    [c0 < tl] as a carry-detect idiom.  After VST symbolic execution,
    the postcondition contains nested [Int64.ltu] / [Int.signed] /
    [Int.repr] expressions.

    These bridge lemmas translate each limb's C-level expression
    into the pure-math [limb_add_N] form in a single step, keeping
    the body proofs to one [apply] per limb. *)

(** Bridge for limb 1: normalize [ltu]/[signed]/[repr] into the
    carry form that [limb_add_1] uses. *)
Lemma muladd_limb1 : forall acc_v prod,
  0 <= acc_v -> 0 <= prod ->
  Int64.eqm
    (limb (2^64) acc_v 1 + (limb (2^64) prod 1 +
      Int.signed (Int.repr
        (Z.b2z (Int64.ltu
          (Int64.repr (limb (2^64) acc_v 0 + limb (2^64) prod 0))
          (Int64.repr (limb (2^64) prod 0)))))))
    (limb (2^64) (acc_v + prod) 1).
Proof.
  intros acc_v prod Hacc Hprod.

  (* Limb ranges *)
  pose proof (limb_u64_range acc_v 0) as Hla0.
  pose proof (limb_u64_range prod 0) as Hlb0.

  (* Normalize ltu/b2z to the if-then-else carry *)
  rewrite (ltu_carry_b2z (limb (2^64) acc_v 0) (limb (2^64) prod 0)) by assumption.

  (* Int.signed (Int.repr (0 or 1)) = (0 or 1) *)
  assert (Hinner :
    Int.signed (Int.repr
      (if limb (2^64) acc_v 0 + limb (2^64) prod 0 <? Int64.modulus then 0 else 1))
    = (if limb (2^64) acc_v 0 + limb (2^64) prod 0 <? Int64.modulus then 0 else 1)).
  { destruct (limb (2^64) acc_v 0 + limb (2^64) prod 0 <? Int64.modulus); reflexivity. }
  rewrite Hinner.

  (* Conclude via limb_add_1 *)
  change Int64.modulus with (2^64).
  apply eqm_of_mod_eq.
  apply limb_add_1; lia.
Qed.

(** Bridge for limb 2: normalize two levels of [ltu]/[signed]/[repr]
    into the carry form that [limb_add_2] uses.

    Takes [av] and [bv] as separate u64 factors (not just their
    product) because we need [(av * bv) / 2^64 <= 2^64 - 2] to
    prove the intermediate carry fits in a u64. *)
Lemma muladd_limb2 : forall acc_v av bv,
  0 <= acc_v ->
  0 <= av < 2^64 -> 0 <= bv < 2^64 ->
  let prod := av * bv in
  let c0_carry :=
    Z.b2z (Int64.ltu
      (Int64.repr (limb (2^64) acc_v 0 + limb (2^64) prod 0))
      (Int64.repr (limb (2^64) prod 0))) in
  let th := limb (2^64) prod 1 + Int.signed (Int.repr c0_carry) in
  Int64.eqm
    (limb (2^64) acc_v 2 +
      Int.signed (Int.repr
        (Z.b2z (Int64.ltu
          (Int64.repr (limb (2^64) acc_v 1 + th))
          (Int64.repr th)))))
    (limb (2^64) (acc_v + prod) 2).
Proof.
  intros acc_v av bv Hacc Hav Hbv prod c0_carry th.

  (* Limb ranges *)
  pose proof (limb_u64_range acc_v 0) as Hla0.
  pose proof (limb_u64_range prod 0) as Hlb0.
  pose proof (limb_u64_range acc_v 1) as Hla1.
  pose proof (limb_u64_range prod 1) as Hlb1.

  (* Inline the let-bindings *)
  subst c0_carry th.

  (* ===== Normalize the inner (limb 0) carry ===== *)

  (* ltu/b2z -> if-then-else carry *)
  rewrite (ltu_carry_b2z (limb (2^64) acc_v 0) (limb (2^64) prod 0)) by assumption.

  (* Int.signed (Int.repr (0 or 1)) = (0 or 1) *)
  assert (Hinner :
    Int.signed (Int.repr
      (if limb (2^64) acc_v 0 + limb (2^64) prod 0 <? Int64.modulus then 0 else 1))
    = (if limb (2^64) acc_v 0 + limb (2^64) prod 0 <? Int64.modulus then 0 else 1)).
  { destruct (limb (2^64) acc_v 0 + limb (2^64) prod 0 <? Int64.modulus); reflexivity. }
  rewrite Hinner.
  clear Hinner.

  (* Name the carry and bound it *)
  set (c0' := if limb (2^64) acc_v 0 + limb (2^64) prod 0 <? Int64.modulus then 0 else 1).
  assert (Hc0' : 0 <= c0' <= 1)
    by (subst c0'; destruct (limb (2^64) acc_v 0 + limb (2^64) prod 0 <? Int64.modulus); lia).

  (* prod high limb <= 2^64 - 2, so th = prod_hi + c0' fits in u64 *)
  assert (Hlb1' : limb (2^64) prod 1 <= Int64.max_unsigned - 1).
  { unfold limb.
    rewrite Z.pow_1_r.
    subst prod.
    change (2^64) with Int64.modulus.
    pose proof (mul_u64_hi_le av bv Hav Hbv).
    change (2^64) with Int64.modulus in H.
    rewrite Z.mod_small by (split; [apply Z.div_pos; rep_lia | rep_lia]).
    rep_lia. }
  assert (Hth : 0 <= limb (2^64) prod 1 + c0' <= Int64.max_unsigned)
    by (subst c0'; destruct (limb (2^64) acc_v 0 + limb (2^64) prod 0 <? Int64.modulus); lia).

  (* ===== Normalize the outer (limb 1) carry ===== *)

  (* ltu/b2z -> if-then-else carry *)
  rewrite (ltu_carry_b2z (limb (2^64) acc_v 1) (limb (2^64) prod 1 + c0'))
    by (try assumption; lia).

  (* Int.signed (Int.repr (0 or 1)) = (0 or 1) *)
  assert (Houter :
    Int.signed (Int.repr
      (if limb (2^64) acc_v 1 + (limb (2^64) prod 1 + c0') <? Int64.modulus
       then 0 else 1))
    = (if limb (2^64) acc_v 1 + (limb (2^64) prod 1 + c0') <? Int64.modulus
       then 0 else 1)).
  { destruct (limb (2^64) acc_v 1 + (limb (2^64) prod 1 + c0') <? Int64.modulus);
    reflexivity. }
  rewrite Houter.
  clear Houter.

  (* Re-associate addition for limb_add_2 *)
  replace (limb (2^64) acc_v 1 + (limb (2^64) prod 1 + c0'))
    with (limb (2^64) acc_v 1 + limb (2^64) prod 1 + c0') by lia.
  change Int64.modulus with (2^64).

  (* Conclude via limb_add_2 *)
  subst c0'.
  apply eqm_of_mod_eq.
  apply limb_add_2; nia.
Qed.

(* ----------------------------------------------------------------- *)
(** *** sumadd carry bridge lemmas

    Same idea as [muladd_limb1] / [muladd_limb2], but for adding a
    plain u64 value [av] (rather than a product) to an accumulator.
    Since [av < 2^64], its high limbs are 0, which simplifies the
    carry chain.

    Stated as [Int64.repr] equalities so that callers can [apply]
    directly after [f_equal], without an intermediate [eqm] step. *)

(** Bridge for sumadd limb 0. *)
Lemma sumadd_limb0 : forall acc_v av,
  0 <= acc_v -> 0 <= av < 2^64 ->
  Int64.eqm (limb (2^64) acc_v 0 + av) (limb (2^64) (acc_v + av) 0).
Proof.
  intros.
  apply eqm_of_mod_eq.
  unfold limb; simpl Z.of_nat;
    rewrite Z.pow_0_r, !Z.div_1_r.
  apply Zplus_mod_idemp_l.
Qed.

(** Bridge for sumadd limb 1: normalize [ltu] / [b2z] into
    [limb_add_1] form.  The caller strips [Int.unsigned] or
    [Int.signed] (one rewrite) before applying this lemma. *)
Lemma sumadd_limb1 : forall acc_v av,
  0 <= acc_v -> 0 <= av < 2^64 ->
  Int64.eqm
    (limb (2^64) acc_v 1 +
      Z.b2z (Int64.ltu
        (Int64.repr (limb (2^64) acc_v 0 + av))
        (Int64.repr av)))
    (limb (2^64) (acc_v + av) 1).
Proof.
  intros acc_v av Hacc Hav.
  pose proof (limb_u64_range acc_v 0).

  rewrite (ltu_carry_b2z (limb (2^64) acc_v 0) av) by rep_lia.
  change Int64.modulus with (2^64).

  apply eqm_of_mod_eq.
  assert (Hav0 : limb (2^64) av 0 = av).
  { unfold limb. simpl Z.of_nat.
    rewrite Z.pow_0_r, Z.div_1_r.
    apply Z.mod_small. lia. }
  assert (Hav1 : limb (2^64) av 1 = 0)
    by (apply limb_high_zero; simpl Z.of_nat; lia).
  transitivity ((limb (2^64) acc_v 1 + (limb (2^64) av 1 +
    (if limb (2^64) acc_v 0 + limb (2^64) av 0 <? 2^64 then 0 else 1))) mod 2^64).
  - f_equal. rewrite Hav0, Hav1. lia.
  - apply limb_add_1; lia.
Qed.

(** Bridge for sumadd limb 2: normalize two levels of carry
    (unsigned inner, signed outer) into [limb_add_2_u64] form. *)
Lemma sumadd_limb2 : forall acc_v av,
  0 <= acc_v -> 0 <= av < 2^64 ->
  let c0_carry :=
    Z.b2z (Int64.ltu
      (Int64.repr (limb (2^64) acc_v 0 + av))
      (Int64.repr av)) in
  let over := Int.unsigned (Int.repr c0_carry) in
  Int64.eqm
    (limb (2^64) acc_v 2 +
      Int.signed (Int.repr
        (Z.b2z (Int64.ltu
          (Int64.repr (limb (2^64) acc_v 1 + over))
          (Int64.repr over)))))
    (limb (2^64) (acc_v + av) 2).
Proof.
  intros acc_v av Hacc Hav c0_carry over.
  pose proof (limb_u64_range acc_v 0) as Hla0.
  pose proof (limb_u64_range acc_v 1) as Hla1.

  subst c0_carry over.

  (* Normalize inner (limb 0) carry *)
  rewrite (ltu_carry_b2z (limb (2^64) acc_v 0) av) by rep_lia.
  set (c0' := if limb (2^64) acc_v 0 + av <? Int64.modulus then 0 else 1).
  assert (Hc0' : 0 <= c0' <= 1)
    by (subst c0'; destruct (limb (2^64) acc_v 0 + av <? Int64.modulus); lia).
  assert (Hcu : Int.unsigned (Int.repr c0') = c0')
    by (subst c0'; destruct (limb (2^64) acc_v 0 + av <? Int64.modulus); reflexivity).
  rewrite Hcu.

  (* Normalize outer (limb 1) carry *)
  rewrite (ltu_carry_b2z (limb (2^64) acc_v 1) c0') by rep_lia.
  assert (Hcs :
    Int.signed (Int.repr
      (if limb (2^64) acc_v 1 + c0' <? Int64.modulus then 0 else 1))
    = (if limb (2^64) acc_v 1 + c0' <? Int64.modulus then 0 else 1))
    by (destruct (limb (2^64) acc_v 1 + c0' <? Int64.modulus); reflexivity).
  rewrite Hcs.
  change Int64.modulus with (2^64).

  (* Derive from limb_add_2: substitute limb (2^64) av 0 = av, limb (2^64) av 1 = 0 *)
  subst c0'.
  apply eqm_of_mod_eq.
  pose proof (limb_add_2 acc_v av Hacc ltac:(lia) ltac:(lia)) as H.
  rewrite (limb_high_zero av 0) in H by (simpl Z.of_nat; lia).
  replace (limb (2^64) av 0) with av in H
    by (unfold limb; simpl Z.of_nat;
        rewrite Z.pow_0_r, Z.div_1_r;
        symmetry; apply Z.mod_small; lia).
  replace (limb (2^64) acc_v 1 + 0 +
    (if limb (2^64) acc_v 0 + av <? 2 ^ 64 then 0 else 1))
    with (limb (2^64) acc_v 1 +
    (if limb (2^64) acc_v 0 + av <? 2 ^ 64 then 0 else 1)) in H by lia.
  exact H.
Qed.

