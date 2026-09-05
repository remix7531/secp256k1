(** * model.group_ell: coqprime's elliptic group law, instantiated at [Fe]. *)
(** Copyright (C) 2026 remix7531
    SPDX-License-Identifier: MIT *)

(** The machinery behind [model.group_law]'s [padd_comm] and [padd_assoc]:
    coqprime's [Coqprime.elliptic.SMain] proves the Weierstrass group law once,
    over an abstract field packaged as an [ell_theory] record.  This file builds
    that record at [K := model.types.Fe] -- the model's OWN field type, with the
    model's OWN operations -- and transports the resulting law onto
    [model.group]'s [Point].

    WHY [Fe] AND NOT [Coqprime.elliptic.GZnZ].  The obvious route is to build
    the field as coqprime's [znz secp256k1_P] and then transport [znz -> Fe].
    That is unnecessary: [Fe] IS a [znz] in a different skin (a [Z] paired with
    its range invariant, quotiented by [model.types]'s [Z_range_irrel] the way
    [znz] is quotiented by [zirr]), so instantiating [ell_theory] directly at
    [Fe] removes an entire representation change and lets coqprime's [add]
    compute with [fe_add] / [fe_mul] / [fe_inv] themselves.  [GZnZ] is not
    required here at all.

    THE TWO OBLIGATIONS THAT ARE REAL WORK.
      - [Fe_field_theory]'s [Finv_l]: [fe_inv] is [a^(p-2) mod p], so its
        correctness IS Fermat's little theorem.  Discharged from
        [Coqprime.PrimalityTest.Zp]'s [phi_power_is_1] and
        [Coqprime.PrimalityTest.Euler]'s [prime_phi_n_minus_1] over
        [model.field]'s [secp256k1_P_prime], itself a [Qed] lemma over the
        Pocklington certificate in [theory.primality.p] -- not a project
        [Axiom], but see the TRUST NOTE below.
      - [padd_transport]: [padd] on the images of two [elt]s IS coqprime's
        [add] on the sources.  Proved with [SMain]'s own [add_case], which
        hands out exactly the five branches [padd] distinguishes.
    The remaining [ell_theory] fields ([NonSingular], [one_not_zero],
    [two_not_zero], [is_zero_correct]) are ground computations.

    WHAT THIS FILE DOES NOT DELIVER.  [padd_comm] does NOT follow from
    [SMain]'s [add_comm]: coqprime's [elt] carries its on-curve proof in the
    constructor, while [model.group_law] states [padd_comm] for ARBITRARY
    [Point]s with no [on_curve] hypothesis.  So the transport yields only the
    on-curve instance, and the registered statement needs a direct argument --
    which is why [fe_sub_nonzero] / [fe_inv_negate] / [fe_inv_l] are exported
    below rather than a commutativity lemma.

    CLOSURE ([padd_on_curve]) is proved here and stays here: [model.group_law]
    deliberately does not state it (see that file's header), and nothing in the
    tree registers it as a scaffolded gap.

    LICENCE, RECORDED AND NOT RULED ON.  The three files of coqprime's
    elliptic development are GNU LGPL-2.1, while this tree is MIT (the root COPYING).
    This file needs coqprime only as an EXTERNAL LIBRARY -- a flake dependency,
    [Require]d, exactly as [theory.primality.n] and [theory.primality.p]
    already use it for their Pocklington certificates.  Nothing is vendored,
    adapted, or copied, so STYLE.md's "Unported vendoring" and ported-file
    header rules do not apply.  No compatibility ruling is attempted here.

    TRUST NOTE.  Everything below closes over the coqprime Pocklington
    certificate's own trust base -- Rocq's primitive 63-bit integer axioms
    ([PrimInt63.*] / [Uint63Axioms.*]), plus [functional_extensionality_dep]
    from [model.types]'s [Z_range_irrel].  Every one of those names is already
    on [audit/AXIOM_WHITELIST] and already reachable from
    [model.field]'s [secp256k1_P_prime]; this file introduces no new one.

    PURITY.  No VST / CompCert / AST import, as the [make axioms] gate over
    [model/] and [theory/] requires.  It lives under [model/] rather than
    [theory/] because it mentions model definitions -- the same layering
    ruling that placed [model.group_law] and [model.jacobi_rules]. *)

Require Import ZArith.
Require Import Lia.
Require Import Znumtheory.
Require Import Ring.
Require Import Field.

Require Import Coqprime.PrimalityTest.Euler.
Require Import Coqprime.PrimalityTest.Zp.
Require Import Coqprime.elliptic.SMain.

(** IMPORT ORDER IS LOAD-BEARING.  [SMain] declares its own [on_curve],
    [padd], [pdouble] and [pow] over its abstract [pelt], so it must be
    [Require]d BEFORE [model.group], or those names shadow the model's and
    every statement below silently changes meaning (it does not typecheck, but
    the error is far from the cause).  This is the one place in the tree where
    the external group comes before the project group. *)
Require Import secp256k1.theory.field.field_bits.
Require Import secp256k1.model.group.

(** [SMain] leaks a global [Set Implicit Arguments] (it is not [Local] there),
    which would otherwise change the calling convention of everything declared
    below and in every file that requires this one.  Undo it. *)
Unset Implicit Arguments.

Open Scope Z_scope.

(* ================================================================= *)
(** ** Mod-normalisation -- turning an [Fe] equation into a [Z] identity.

    Every [Fe] operation is "the [Z] operation, then [mod p]".  The lemmas
    below are the rewrite set that pushes those inner [mod]s outwards until
    both sides of a goal are mod-free polynomials, at which point [ring]
    closes it.  [fe_negate]'s [(p - a)] shape is turned into [-a] first, which
    is what makes the two polynomials genuinely ring-equal rather than merely
    congruent mod [p]. *)

(** The field modulus is positive -- the side condition of every [Z.*_mod_*]. *)
Lemma P_pos : 0 < secp256k1_P.
Proof.
  pose proof secp256k1_P_range.
  lia.
Qed.

(** ... and nonzero, the form [Z.add_mod_idemp_l] and friends ask for. *)
Lemma P_nz : secp256k1_P <> 0.
Proof.
  pose proof P_pos.
  lia.
Qed.

(** [fe_negate]'s [(p - a) mod p] is [(- a) mod p]. *)
Lemma sub_P_mod : forall a : Z,
  (secp256k1_P - a) mod secp256k1_P = (- a) mod secp256k1_P.
Proof.
  intros a.
  replace (secp256k1_P - a) with (- a + 1 * secp256k1_P) by ring.
  apply Z_mod_plus_full.
Qed.

(** Negation absorbs an inner reduction. *)
Lemma opp_mod_idemp : forall a : Z,
  (- (a mod secp256k1_P)) mod secp256k1_P = (- a) mod secp256k1_P.
Proof.
  intros a.
  rewrite <- (Z.sub_0_l (a mod secp256k1_P)).
  rewrite Zminus_mod_idemp_r.
  rewrite Z.sub_0_l.
  reflexivity.
Qed.

(** The four unconditional idempotence rewrites (the stdlib forms carry an
    [n <> 0] side condition that a [repeat rewrite] cannot discharge inline). *)
Lemma addl_mod : forall a b : Z,
  (a mod secp256k1_P + b) mod secp256k1_P = (a + b) mod secp256k1_P.
Proof.
  intros a b.
  apply Z.add_mod_idemp_l.
  apply P_nz.
Qed.

Lemma addr_mod : forall a b : Z,
  (a + b mod secp256k1_P) mod secp256k1_P = (a + b) mod secp256k1_P.
Proof.
  intros a b.
  apply Z.add_mod_idemp_r.
  apply P_nz.
Qed.

Lemma mull_mod : forall a b : Z,
  (a mod secp256k1_P * b) mod secp256k1_P = (a * b) mod secp256k1_P.
Proof.
  intros a b.
  apply Z.mul_mod_idemp_l.
  apply P_nz.
Qed.

Lemma mulr_mod : forall a b : Z,
  (a * (b mod secp256k1_P)) mod secp256k1_P = (a * b) mod secp256k1_P.
Proof.
  intros a b.
  apply Z.mul_mod_idemp_r.
  apply P_nz.
Qed.

(** Two more shapes: a left-nested sum ([(a + b) + c] under one [mod]) is not
    reachable from [addl_mod] / [addr_mod] alone, and the curve equation is
    exactly that shape. *)
Lemma addl3_mod : forall a b c : Z,
  (a mod secp256k1_P + b + c) mod secp256k1_P = (a + b + c) mod secp256k1_P.
Proof.
  intros a b c.
  rewrite <- !Z.add_assoc.
  apply addl_mod.
Qed.

Lemma addm3_mod : forall a b c : Z,
  (a + b mod secp256k1_P + c) mod secp256k1_P = (a + b + c) mod secp256k1_P.
Proof.
  intros a b c.
  rewrite <- !Z.add_assoc.
  rewrite <- Z.add_mod_idemp_r by apply P_nz.
  rewrite addl_mod.
  rewrite Z.add_mod_idemp_r by apply P_nz.
  reflexivity.
Qed.

(** Normalise a [Z] goal to a single outer [mod].  PRODUCTS FIRST, THEN SUMS:
    the sum rules strip a [mod] that the product rules still need to fire on,
    so applied in the other order [on_curve_iff] below dies with "not a valid
    ring equation".  The order here is load-bearing. *)
Ltac fe_mod_norm :=
  repeat (rewrite ?sub_P_mod, ?opp_mod_idemp, ?mull_mod, ?mulr_mod, ?Zmod_mod);
  repeat (rewrite ?addl_mod, ?addr_mod, ?addl3_mod, ?addm3_mod, ?Zmod_mod);
  repeat (rewrite ?sub_P_mod, ?opp_mod_idemp, ?mull_mod, ?mulr_mod,
                  ?addl_mod, ?addr_mod, ?addl3_mod, ?addm3_mod, ?Zmod_mod).

(** The same, in a hypothesis. *)
Ltac fe_mod_norm_in H :=
  repeat (rewrite ?sub_P_mod, ?opp_mod_idemp, ?mull_mod, ?mulr_mod,
                  ?Zmod_mod in H);
  repeat (rewrite ?addl_mod, ?addr_mod, ?addl3_mod, ?addm3_mod,
                  ?Zmod_mod in H);
  repeat (rewrite ?sub_P_mod, ?opp_mod_idemp, ?mull_mod, ?mulr_mod,
                  ?addl_mod, ?addr_mod, ?addl3_mod, ?addm3_mod,
                  ?Zmod_mod in H).

(** The workhorse: reduce an [Fe] equation to a mod-free [Z] identity.
    [fe_eq_ext] drops the range proofs, [cbn] exposes the [fe_val]s, the
    rewrite set normalises, and the [Z] [ring] finishes. *)
Ltac fe_ring :=
  apply fe_eq_ext;
  cbn [fe_val fe_add fe_mul fe_sqr fe_negate fe_mul_int fe_add_int
       fe_zero fe_one];
  fe_mod_norm;
  f_equal;
  ring.

(* ================================================================= *)
(** ** [Fe] as a coqprime field -- [fe_sub] / [fe_div] / [Fe_ring_theory].

    [field_theory] wants subtraction and division as primitive operations;
    [model.field] has neither, so both are defined here in the shape the
    record asks for. *)

(** Field subtraction. *)
Definition fe_sub (a b : Fe) : Fe := fe_add a (fe_negate b).

(** Field division. *)
Definition fe_div (a b : Fe) : Fe := fe_mul a (fe_inv b).

(** [Fe] is a commutative ring.  Nine obligations, seven of them the same
    mod-normalisation. *)
Lemma Fe_ring_theory :
  ring_theory fe_zero fe_one fe_add fe_mul fe_sub fe_negate (@eq Fe).
Proof.
  split.
  - (* 0 + a = a *)
    intros a.
    apply fe_eq_ext.
    cbn [fe_val fe_add fe_zero].
    rewrite Z.add_0_l.
    apply Zmod_small.
    apply fe_range.
  - (* a + b = b + a *)
    intros a b.
    fe_ring.
  - (* (a + b) + c = a + (b + c) *)
    intros a b c.
    fe_ring.
  - (* 1 * a = a *)
    intros a.
    apply fe_eq_ext.
    cbn [fe_val fe_mul fe_one].
    rewrite Z.mul_1_l.
    apply Zmod_small.
    apply fe_range.
  - (* a * b = b * a *)
    intros a b.
    fe_ring.
  - (* (a * b) * c = a * (b * c) *)
    intros a b c.
    fe_ring.
  - (* (a + b) * c = a * c + b * c *)
    intros a b c.
    fe_ring.
  - (* a - b = a + (- b), definitionally *)
    intros a b.
    reflexivity.
  - (* a + (- a) = 0 *)
    intros a.
    apply fe_eq_ext.
    cbn [fe_val fe_add fe_negate fe_zero].
    rewrite sub_P_mod.
    rewrite addr_mod.
    rewrite Z.add_opp_diag_r.
    apply Zmod_0_l.
Qed.

(** Registering the ring makes [ring] work on [Fe] goals directly, here and in
    [model.group_law]. *)
Add Ring Fe_ring : Fe_ring_theory.

(* ================================================================= *)
(** ** Fermat's little theorem -- what makes [fe_inv] an inverse. *)

(** [pow_mod] really is [Z.pow] followed by one reduction, at any nonnegative
    exponent ([theory.field.field_bits] proves the [Zpos] case only). *)
Lemma pow_mod_spec : forall a e m : Z, 0 <= e -> pow_mod a e m = a ^ e mod m.
Proof.
  intros a e m He.
  destruct e as [|q|q].
  - reflexivity.
  - apply pow_mod_pos_spec.
  - lia.
Qed.

(** A nonzero residue is prime to [p]. *)
Lemma fe_rel_prime : forall a : Fe,
  a <> fe_zero -> rel_prime (fe_val a) secp256k1_P.
Proof.
  intros a Ha.
  apply rel_prime_le_prime.
  - apply secp256k1_P_prime.
  - pose proof (fe_range a) as Hr.
    assert (Hnz : fe_val a <> 0).
    { intros Hz.
      apply Ha.
      apply fe_eq_ext.
      cbn.
      exact Hz. }
    lia.
Qed.

(** Fermat's little theorem at [p], over [Z]: coqprime's Euler-totient group
    theorem specialised by [prime_phi_n_minus_1]. *)
Lemma fermat_P : forall a : Z,
  rel_prime a secp256k1_P -> a ^ (secp256k1_P - 1) mod secp256k1_P = 1.
Proof.
  intros a Ha.
  assert (Hphi : phi secp256k1_P = secp256k1_P - 1).
  { apply prime_phi_n_minus_1.
    apply secp256k1_P_prime. }
  rewrite <- Hphi.
  apply phi_power_is_1.
  - unfold secp256k1_P.
    lia.
  - exact Ha.
Qed.

(** [fe_inv] is a left inverse -- the [Finv_l] field obligation, and the one
    fact [model.group_law]'s [padd_comm] really rests on. *)
Lemma fe_inv_l : forall a : Fe, a <> fe_zero -> fe_mul (fe_inv a) a = fe_one.
Proof.
  intros a Ha.
  apply fe_eq_ext.
  cbn [fe_val fe_mul fe_inv fe_pow fe_one].
  rewrite pow_mod_spec by (unfold secp256k1_P; lia).
  rewrite mull_mod.
  rewrite Z.mul_comm.
  rewrite <- Z.pow_succ_r by (unfold secp256k1_P; lia).
  replace (Z.succ (secp256k1_P - 2)) with (secp256k1_P - 1) by lia.
  rewrite fermat_P by (apply fe_rel_prime; exact Ha).
  reflexivity.
Qed.

(** [Fe] is a field. *)
Lemma Fe_field_theory :
  field_theory fe_zero fe_one fe_add fe_mul fe_sub fe_negate fe_div fe_inv
               (@eq Fe).
Proof.
  split.
  - (* the underlying ring *)
    apply Fe_ring_theory.
  - (* 1 <> 0 *)
    intros Hc.
    apply (f_equal fe_val) in Hc.
    cbn in Hc.
    discriminate.
  - (* a / b = a * (/ b), definitionally *)
    intros a b.
    reflexivity.
  - (* (/ a) * a = 1 *)
    intros a Ha.
    apply fe_inv_l.
    exact Ha.
Qed.

(* ================================================================= *)
(** ** The curve parameters and the [ell_theory] instance. *)

(** The curve's [a] coefficient: zero, as in [model.group]. *)
Definition fe_a : Fe := fe_zero.

(** [7] is a residue -- the range proof [fe_b] carries. *)
Lemma fe_b_range : 0 <= secp256k1_B < secp256k1_P.
Proof.
  unfold secp256k1_B, secp256k1_P.
  lia.
Qed.

(** The curve's [b] coefficient: [model.group]'s [secp256k1_B = 7]. *)
Definition fe_b : Fe := mkFe secp256k1_B fe_b_range.

(** coqprime's zero test, at [Fe]: the model's own [fe_is_zero]. *)
Definition fe_zerop (a : Fe) : bool := fe_is_zero a.

(** The [ell_theory] record: the field, non-singularity, the characteristic
    conditions and the zero test.  This is the whole of [SMain]'s
    [Section ELLIPTIC] interface. *)
Lemma Fe_ell_theory :
  ell_theory fe_zero fe_one fe_add fe_mul fe_sub fe_negate fe_inv fe_div
             fe_a fe_b fe_zerop.
Proof.
  split.
  - (* Kfth *)
    apply Fe_field_theory.
  - (* NonSingular: 4*0^3 + 27*7^2 = 1323 <> 0 in F_p *)
    intros Hc.
    apply (f_equal fe_val) in Hc.
    vm_compute in Hc.
    discriminate.
  - (* one_not_zero *)
    intros Hc.
    apply (f_equal fe_val) in Hc.
    cbn in Hc.
    discriminate.
  - (* two_not_zero: p is odd, so 2 <> 0 *)
    intros Hc.
    apply (f_equal fe_val) in Hc.
    vm_compute in Hc.
    discriminate.
  - (* is_zero_correct *)
    intros k.
    unfold fe_zerop, fe_is_zero.
    split.
    + intros Hk.
      apply Z.eqb_eq in Hk.
      apply fe_eq_ext.
      cbn.
      exact Hk.
    + intros Hk.
      apply Z.eqb_eq.
      subst k.
      reflexivity.
Qed.

(* ================================================================= *)
(** ** Ring-shaping the model's derived operations.

    [fe_sqr] / [fe_mul_int] are not ring operations, so [ring] cannot see
    through them.  These three rewrites put every occurrence the group law
    produces into [fe_add] / [fe_mul] form. *)

(** Squaring is multiplication. *)
Lemma fe_sqr_eq : forall a : Fe, fe_sqr a = fe_mul a a.
Proof.
  intros a.
  fe_ring.
Qed.

(** Doubling by [fe_mul_int _ 2] is addition. *)
Lemma fe_mul_int_2 : forall a : Fe, fe_mul_int a 2 = fe_add a a.
Proof.
  intros a.
  fe_ring.
Qed.

(** Tripling by [fe_mul_int _ 3] is repeated addition. *)
Lemma fe_mul_int_3 : forall a : Fe, fe_mul_int a 3 = fe_add (fe_add a a) a.
Proof.
  intros a.
  fe_ring.
Qed.

(** Inverses are unique, so any two left inverses of the same element agree.
    This is what makes [fe_inv] interchangeable with coqprime's [kinv]
    wherever both are applied to equal arguments. *)
Lemma fe_inv_unique : forall a b c : Fe,
  fe_mul a c = fe_one -> fe_mul b c = fe_one -> a = b.
Proof.
  intros a b c Ha Hb.
  replace a with (fe_mul a fe_one) by ring.
  rewrite <- Hb.
  replace (fe_mul a (fe_mul b c)) with (fe_mul (fe_mul a c) b) by ring.
  rewrite Ha.
  ring.
Qed.

(** A residue is zero exactly when its value is. *)
Lemma fe_val_zero_iff : forall a : Fe, a = fe_zero <-> fe_val a = 0.
Proof.
  intros a.
  split.
  - intros Ha.
    subst a.
    reflexivity.
  - intros Ha.
    apply fe_eq_ext.
    cbn [fe_val fe_zero].
    exact Ha.
Qed.

(** [p] is odd -- the characteristic fact behind "y = -y implies y = 0". *)
Lemma P_odd : secp256k1_P mod 2 = 1.
Proof.
  vm_compute.
  reflexivity.
Qed.

(** A residue equal to its own negation is zero. *)
Lemma fe_self_negate_zero : forall y : Fe, y = fe_negate y -> fe_val y = 0.
Proof.
  intros y Hy.
  apply (f_equal fe_val) in Hy.
  cbn [fe_val fe_negate] in Hy.
  pose proof (fe_range y) as Hr.
  pose proof P_odd as Hodd.
  destruct (Z.eq_dec (fe_val y) 0) as [Hz|Hz].
  - exact Hz.
  - rewrite Zmod_small in Hy by lia.
    assert (Hcontra : 2 * fe_val y = secp256k1_P) by lia.
    rewrite <- Hcontra in Hodd.
    rewrite Z.mul_comm in Hodd.
    rewrite Z_mod_mult in Hodd.
    discriminate.
Qed.

(* ================================================================= *)
(** ** The two maps between [elt] and [Point].

    coqprime's [elt] CARRIES its on-curve proof in the constructor;
    [model.group]'s [Point] does not, and [on_curve] is a separate predicate.
    So the two maps are asymmetric: [elt_to_point] is total, [point_to_elt]
    needs [on_curve a] as an argument.  That asymmetry is exactly why
    [padd_assoc] carries three [on_curve] hypotheses and [padd_comm] carries
    none. *)

(** The curve-point type of the instance. *)
Definition ECurve : Set := elt fe_one fe_add fe_mul fe_a fe_b.

(** coqprime's group operation at the instance. *)
Definition eadd (p q : ECurve) : ECurve := add Fe_ell_theory p q.

(** The curve equation in coqprime's shape. *)
Definition curve_eq (x y : Fe) : Prop :=
  pow fe_one fe_mul y 2
    = fe_add (fe_add (pow fe_one fe_mul x 3) (fe_mul fe_a x)) fe_b.

(** The model's [on_curve] and coqprime's constructor obligation are the same
    statement.  This is the only place the two curve equations meet. *)
Lemma on_curve_iff : forall x y : Fe, on_curve (PAff x y) <-> curve_eq x y.
Proof.
  intros x y.
  unfold on_curve, curve_eq, fe_a.
  cbn [pow].
  split.
  - intros H.
    apply fe_eq_ext.
    cbn [fe_val fe_add fe_mul fe_zero fe_b].
    fe_mod_norm.
    rewrite H.
    f_equal.
    ring.
  - intros H.
    apply (f_equal fe_val) in H.
    cbn [fe_val fe_add fe_mul fe_zero fe_b] in H.
    fe_mod_norm_in H.
    rewrite H.
    f_equal.
    ring.
Qed.

(** [elt -> Point]: forget the on-curve proof. *)
Definition elt_to_point (p : ECurve) : Point :=
  match p with
  | inf_elt _ _ _ _ _ => PInf
  | curve_elt _ _ _ _ _ x y _ => PAff x y
  end.

(** Its image is always on the curve -- the proof the constructor carries. *)
Lemma elt_on_curve : forall p : ECurve, on_curve (elt_to_point p).
Proof.
  intros p.
  destruct p as [|x y H].
  - exact I.
  - apply on_curve_iff.
    exact H.
Qed.

(** [Point -> elt], partial: [on_curve] is the missing proof. *)
Definition point_to_elt (a : Point) : on_curve a -> ECurve :=
  match a return on_curve a -> ECurve with
  | PInf => fun _ => inf_elt fe_one fe_add fe_mul fe_a fe_b
  | PAff x y =>
      fun H => curve_elt fe_one fe_add fe_mul fe_a fe_b x y
                         (proj1 (on_curve_iff x y) H)
  end.

(** The two maps are inverse in the direction that matters. *)
Lemma elt_to_point_to_elt : forall (a : Point) (H : on_curve a),
  elt_to_point (point_to_elt a H) = a.
Proof.
  intros a H.
  destruct a as [|x y].
  - reflexivity.
  - reflexivity.
Qed.

(* ================================================================= *)
(** ** The model's group law, branch by branch.

    Three shape lemmas exposing [padd] / [pdouble] on the cases [add_case]
    hands out. *)

(** [padd] on a repeated point is [pdouble]. *)
Lemma padd_same : forall x y : Fe,
  padd (PAff x y) (PAff x y) = pdouble (PAff x y).
Proof.
  intros x y.
  unfold padd.
  rewrite Z.eqb_refl.
  rewrite Z.eqb_refl.
  reflexivity.
Qed.

(** [pdouble] away from [y = 0]: the tangent formulas, in ring shape. *)
Lemma pdouble_aff : forall x y : Fe, fe_val y <> 0 ->
  pdouble (PAff x y) =
    (let lam := fe_mul (fe_add (fe_add (fe_mul x x) (fe_mul x x)) (fe_mul x x))
                       (fe_inv (fe_add y y)) in
     let x3 := fe_add (fe_mul lam lam) (fe_negate (fe_add x x)) in
     PAff x3 (fe_add (fe_mul lam (fe_add x (fe_negate x3))) (fe_negate y))).
Proof.
  intros x y Hy.
  unfold pdouble, fe_is_zero.
  rewrite <- Z.eqb_neq in Hy.
  rewrite Hy.
  rewrite fe_sqr_eq.
  rewrite !fe_mul_int_2.
  rewrite fe_mul_int_3.
  rewrite fe_sqr_eq.
  reflexivity.
Qed.

(** [padd] on two points with different x: the chord formulas, in ring shape. *)
Lemma padd_gen : forall x1 y1 x2 y2 : Fe, fe_val x1 <> fe_val x2 ->
  padd (PAff x1 y1) (PAff x2 y2) =
    (let lam := fe_mul (fe_add y2 (fe_negate y1))
                       (fe_inv (fe_add x2 (fe_negate x1))) in
     let x3 := fe_add (fe_mul lam lam) (fe_negate (fe_add x1 x2)) in
     PAff x3 (fe_add (fe_mul lam (fe_add x1 (fe_negate x3))) (fe_negate y1))).
Proof.
  intros x1 y1 x2 y2 Hx.
  unfold padd.
  rewrite <- Z.eqb_neq in Hx.
  rewrite Hx.
  rewrite fe_sqr_eq.
  reflexivity.
Qed.

(* ================================================================= *)
(** ** The transport theorem -- [padd_transport] / [eadd_assoc].

    [padd] on the images IS coqprime's [add] on the sources.  Proved with
    [SMain]'s own [add_case], which hands out exactly the five branches the
    model's [padd] distinguishes, with the curve hypotheses already in
    scope. *)

Lemma padd_transport : forall p q : ECurve,
  padd (elt_to_point p) (elt_to_point q) = elt_to_point (eadd p q).
Proof.
  intros p q.
  unfold eadd.
  pattern p, q, (add Fe_ell_theory p q).
  apply add_case.
  - (* branch: PInf on the left *)
    intros r.
    reflexivity.
  - (* branch: PInf on the right *)
    intros r.
    destruct r as [|x y H].
    + reflexivity.
    + reflexivity.
  - (* branch: p + (-p) = PInf *)
    intros r.
    destruct r as [|x y H].
    + reflexivity.
    + cbn [elt_to_point opp].
      unfold padd.
      rewrite Z.eqb_refl.
      destruct (Z.eqb_spec (fe_val y) (fe_val (fe_negate y))) as [Hy|Hy].
      * (* y = -y forces y = 0, and then [pdouble] is [PInf] too *)
        assert (Hz : fe_val y = 0).
        { apply fe_self_negate_zero.
          apply fe_eq_ext.
          exact Hy. }
        unfold pdouble, fe_is_zero.
        rewrite Hz.
        reflexivity.
      * reflexivity.
  - (* branch: the tangent *)
    intros p1 x1 y1 H1 p2 x2 y2 H2 l Hp1 Hp2 Hdbl Hy1 Hl Hx2 Hy2.
    subst p1 p2.
    cbn [elt_to_point].
    rewrite padd_same.
    assert (Hy1v : fe_val y1 <> 0).
    { intros Hc.
      apply Hy1.
      apply fe_val_zero_iff.
      exact Hc. }
    rewrite pdouble_aff by exact Hy1v.
    cbn zeta.
    (* the two slopes agree: same numerator, same denominator *)
    assert (Hlam : l = fe_mul (fe_add (fe_add (fe_mul x1 x1) (fe_mul x1 x1))
                                      (fe_mul x1 x1))
                              (fe_inv (fe_add y1 y1))).
    { rewrite Hl.
      unfold fe_div, fe_a.
      f_equal.
      - ring.
      - f_equal.
        ring. }
    rewrite Hlam in Hx2, Hy2.
    subst x2 y2.
    unfold fe_sub, fe_a.
    cbn [pow].
    f_equal.
    + ring.
    + ring.
  - (* branch: the generic chord *)
    intros p1 x1 y1 H1 p2 x2 y2 H2 p3 x3 y3 H3 l Hp1 Hp2 Hp3 Hsum Hx Hl Hx3 Hy3.
    subst p1 p2 p3.
    cbn [elt_to_point].
    assert (Hxv : fe_val x1 <> fe_val x2).
    { intros Hc.
      apply Hx.
      apply fe_eq_ext.
      exact Hc. }
    rewrite padd_gen by exact Hxv.
    cbn zeta.
    assert (Hlam : l = fe_mul (fe_add y2 (fe_negate y1))
                              (fe_inv (fe_add x2 (fe_negate x1)))).
    { rewrite Hl.
      unfold fe_div, fe_sub.
      reflexivity. }
    rewrite Hlam in Hx3, Hy3.
    subst x3 y3.
    unfold fe_sub.
    cbn [pow].
    f_equal.
    + ring.
    + ring.
Qed.

(** Associativity on the source side, in the orientation [padd_assoc] wants
    (coqprime's [add_assoc] is stated the other way round).  Stating it here
    is what keeps [Coqprime.elliptic.SMain] out of [model.group_law]'s import
    list. *)
Lemma eadd_assoc : forall p q r : ECurve,
  eadd (eadd p q) r = eadd p (eadd q r).
Proof.
  intros p q r.
  unfold eadd.
  rewrite add_assoc.
  reflexivity.
Qed.

(* ================================================================= *)
(** ** Closure -- a free corollary of the transport.

    [model.group_law]'s header records closure as DELIBERATELY NOT STATED
    there ("it is part of the same port and would be a sixth admitted fact
    today").  It is not extra work here: [elt] carries its on-curve proof, so
    the image of [eadd] is on the curve by construction.  It stays in this
    file -- it is not one of the registered scaffolded statements. *)

Lemma padd_on_curve : forall a b : Point,
  on_curve a -> on_curve b -> on_curve (padd a b).
Proof.
  intros a b Ha Hb.
  rewrite <- (elt_to_point_to_elt a Ha).
  rewrite <- (elt_to_point_to_elt b Hb).
  rewrite padd_transport.
  apply elt_on_curve.
Qed.

(* ================================================================= *)
(** ** What [padd_comm] needs -- the direct-argument ingredients.

    [padd_comm] is NOT delivered by the transport (see the file header), so
    [model.group_law] proves it directly.  The only real content of that proof
    is that [fe_inv] is a genuine inverse away from zero; these three lemmas
    plus [fe_inv_l] and the [Fe] ring are everything it uses. *)

(** A difference of residues vanishes only when the values agree. *)
Lemma fe_sub_zero : forall a b : Fe,
  fe_add a (fe_negate b) = fe_zero -> fe_val a = fe_val b.
Proof.
  intros a b H.
  apply (f_equal fe_val) in H.
  cbn [fe_val fe_add fe_negate fe_zero] in H.
  rewrite sub_P_mod in H.
  rewrite addr_mod in H.
  pose proof (fe_range a) as Ha.
  pose proof (fe_range b) as Hb.
  apply Z.mod_divide in H.
  - destruct H as [k Hk].
    destruct (Z.lt_trichotomy k 0) as [Hk0|[Hk0|Hk0]].
    + nia.
    + subst k.
      lia.
    + nia.
  - apply P_nz.
Qed.

(** ... so distinct x coordinates give a nonzero chord denominator. *)
Lemma fe_sub_nonzero : forall a b : Fe,
  fe_val a <> fe_val b -> fe_add a (fe_negate b) <> fe_zero.
Proof.
  intros a b Hab Hc.
  apply Hab.
  apply fe_sub_zero.
  exact Hc.
Qed.

(** Inversion anticommutes with negation. *)
Lemma fe_inv_negate : forall u : Fe,
  u <> fe_zero -> fe_inv (fe_negate u) = fe_negate (fe_inv u).
Proof.
  intros u Hu.
  assert (Hnu : fe_negate u <> fe_zero).
  { intros Hc.
    apply Hu.
    apply (f_equal fe_negate) in Hc.
    replace (fe_negate (fe_negate u)) with u in Hc by ring.
    replace (fe_negate fe_zero) with fe_zero in Hc by ring.
    exact Hc. }
  apply (fe_inv_unique _ _ (fe_negate u)).
  - apply fe_inv_l.
    exact Hnu.
  - replace (fe_mul (fe_negate (fe_inv u)) (fe_negate u))
       with (fe_mul (fe_inv u) u) by ring.
    apply fe_inv_l.
    exact Hu.
Qed.
