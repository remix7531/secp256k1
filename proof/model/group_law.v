(** * model.group_law: the abelian-group properties of [model.group]'s [padd]. *)
(** Copyright (C) 2026 remix7531
    SPDX-License-Identifier: MIT *)

(** [model.group] defines the chord-and-tangent law as a computation; this file
    says what that computation IS -- an abelian group operation, compatible with
    [smul], on which the GLV endomorphism acts as multiplication by
    [secp256k1_lambda].

    STATUS.  The four identity/small-argument facts at the top are proved, and
    so are the two group axioms [padd_comm] and [padd_assoc].  The three
    remaining headline lemmas ([smul_add], [smul_mul], [lambda_endo]) are
    STATED AND [Admitted]: they are classical elliptic-curve facts whose only
    honest machine proof is a port of an existing development rather than a
    fresh case analysis over [fe_inv].

    DISCHARGE ROUTE (the same for all five): coqprime's [Coqprime/elliptic]
    development, which builds the Weierstrass group law over an arbitrary field
    and proves associativity there; the port is a field instance at [F_p] plus
    a transport of that law along this file's [Point] / [padd].  That port
    LANDED for the two group axioms -- it is [model.group_ell], which
    instantiates coqprime's [ell_theory] at [model.field]'s own [Fe] and proves
    [padd_transport] with [SMain]'s [add_case].  [padd_assoc] falls straight
    out of it; [padd_comm] does NOT (coqprime's points carry their on-curve
    proof, this statement has no [on_curve] hypothesis), so it is proved
    directly below from the same instance's [fe_inv_l].  The three lemmas still
    [Admitted] appear in [audit/scaffold.txt] and so in the audit's assumption
    accounting; the two proved ones no longer do.

    NOT STATED here, deliberately: closure ([on_curve] preservation under [padd]
    / [pdouble] / [smul]).  It is part of the same port and would be a sixth
    admitted fact today; the phase-C funspecs are written so that they do not
    need it, carrying [on_curve] as a hypothesis where they need it at all.

    This file sits under [model/] rather than [theory/] because it mentions
    model definitions -- the same layering ruling that placed
    [model.jacobi_rules]. *)

Require Import ZArith.
Require Import Lia.
Require Import secp256k1.model.group.
Require Import secp256k1.model.group_ell.

Open Scope Z_scope.

(* ================================================================= *)
(** ** The identity and the smallest multiples -- proved by computation. *)

(** The point at infinity is a left identity.
    See https://wuille.net/posts/secp256k1-tutorial/#221-the-group-operation *)
Lemma padd_PInf_l : forall a : Point, padd PInf a = a.
Proof.
  intros a.
  reflexivity.
Qed.

(** The point at infinity is a right identity.
    See https://wuille.net/posts/secp256k1-tutorial/#221-the-group-operation *)
Lemma padd_PInf_r : forall a : Point, padd a PInf = a.
Proof.
  intros a.
  destruct a.
  - reflexivity.
  - reflexivity.
Qed.

(** [0 * a] is the identity.
    See https://wuille.net/posts/secp256k1-tutorial/#222-scalar-multiplication *)
Lemma smul_0 : forall a : Point, smul 0 a = PInf.
Proof.
  intros a.
  reflexivity.
Qed.

(** [1 * a] is [a].
    See https://wuille.net/posts/secp256k1-tutorial/#222-scalar-multiplication *)
Lemma smul_1 : forall a : Point, smul 1 a = a.
Proof.
  intros a.
  reflexivity.
Qed.

(* ================================================================= *)
(** ** The group axioms -- [padd_comm] / [padd_assoc] (PROVED, via
    [model.group_ell]). *)

(** Addition is commutative.  Unconditional: the chord slope is unchanged by
    swapping the two points, and the [x1 = x2] branches are symmetric by
    construction, so no [on_curve] hypothesis is needed.
    That unconditionality is also why coqprime's [add_comm] does not deliver
    this statement -- its points carry an on-curve proof -- so the argument is
    direct, over [model.group_ell]'s field instance.  Its only real content is
    that [fe_inv] is a genuine inverse away from zero ([fe_inv_l]).
    See https://wuille.net/posts/secp256k1-tutorial/#221-the-group-operation *)
Lemma padd_comm : forall a b : Point, padd a b = padd b a.
Proof.
  intros a b.
  destruct a as [|x1 y1].
  - (* case: a = PInf -- both sides are b *)
    destruct b as [|x2 y2].
    + reflexivity.
    + reflexivity.
  - destruct b as [|x2 y2].
    + (* case: b = PInf -- both sides are a *)
      reflexivity.
    + destruct (Z.eqb_spec (fe_val x1) (fe_val x2)) as [Hx|Hx].
      * (* case: equal x -- both sides take the same branch, and [pdouble]
           only fires when the points are literally equal *)
        assert (Hxe : x1 = x2) by (apply fe_eq_ext; exact Hx).
        subst x2.
        unfold padd.
        rewrite Z.eqb_refl.
        destruct (Z.eqb_spec (fe_val y1) (fe_val y2)) as [Hy|Hy].
        { assert (Hye : y1 = y2) by (apply fe_eq_ext; exact Hy).
          subst y2.
          rewrite Z.eqb_refl.
          reflexivity. }
        { assert (Hy' : fe_val y2 <> fe_val y1) by congruence.
          rewrite <- Z.eqb_neq in Hy'.
          rewrite Hy'.
          reflexivity. }
      * (* case: different x -- the two chord slopes coincide *)
        assert (Hx' : fe_val x2 <> fe_val x1) by congruence.
        rewrite (padd_gen x1 y1 x2 y2 Hx).
        rewrite (padd_gen x2 y2 x1 y1 Hx').
        cbn zeta.
        assert (Hu : fe_add x2 (fe_negate x1) <> fe_zero)
          by (apply fe_sub_nonzero; exact Hx').
        assert (Hnu : fe_add x1 (fe_negate x2)
                      = fe_negate (fe_add x2 (fe_negate x1))) by ring.
        rewrite Hnu.
        rewrite fe_inv_negate by exact Hu.
        set (lam := fe_mul (fe_add y2 (fe_negate y1))
                           (fe_inv (fe_add x2 (fe_negate x1)))).
        assert (Hlam2 : fe_mul (fe_add y1 (fe_negate y2))
                               (fe_negate (fe_inv (fe_add x2 (fe_negate x1))))
                        = lam) by (unfold lam; ring).
        rewrite Hlam2.
        assert (Hslope : fe_mul lam (fe_add x2 (fe_negate x1))
                         = fe_add y2 (fe_negate y1)).
        { unfold lam.
          replace (fe_mul (fe_mul (fe_add y2 (fe_negate y1))
                                  (fe_inv (fe_add x2 (fe_negate x1))))
                          (fe_add x2 (fe_negate x1)))
             with (fe_mul (fe_add y2 (fe_negate y1))
                          (fe_mul (fe_inv (fe_add x2 (fe_negate x1)))
                                  (fe_add x2 (fe_negate x1)))) by ring.
          rewrite fe_inv_l by exact Hu.
          ring. }
        (* [lam] must lose its body before [ring] can treat it as an atom *)
        clearbody lam.
        assert (Hy1 : y1 = fe_add y2
                             (fe_negate (fe_mul lam
                                                (fe_add x2 (fe_negate x1)))))
          by (rewrite Hslope; ring).
        rewrite Hy1.
        f_equal.
        { ring. }
        { ring. }
Qed.

(** Addition is associative on curve points.  This is THE hard one -- the
    classical case explosion over the chord/tangent/vertical branches -- and the
    reason the whole file routes through an existing development rather than a
    hand-rolled case analysis.  [on_curve] is required: associativity is false
    for arbitrary [Fe] pairs.
    Discharged by [model.group_ell]: carry all three points across
    [elt_to_point_to_elt], push [padd] through [padd_transport], and apply
    coqprime's own associativity ([eadd_assoc]).
    See https://wuille.net/posts/secp256k1-tutorial/#221-the-group-operation *)
Lemma padd_assoc : forall a b c : Point,
  on_curve a -> on_curve b -> on_curve c ->
  padd (padd a b) c = padd a (padd b c).
Proof.
  intros a b c Ha Hb Hc.
  rewrite <- (elt_to_point_to_elt a Ha).
  rewrite <- (elt_to_point_to_elt b Hb).
  rewrite <- (elt_to_point_to_elt c Hc).
  rewrite !padd_transport.
  rewrite eadd_assoc.
  reflexivity.
Qed.

(* ================================================================= *)
(** ** Scalar multiplication is a group action -- [smul_add] / [smul_mul]
    (STATED, [Admitted]). *)

(** [smul] is additive in the scalar: [(m + n) * a = m*a + n*a].  Together with
    [smul_mul] this is what lets [model.ecmult] / [model.ecmult_gen] recombine a
    recoded scalar (a wNAF, or a signed-digit comb) into a single multiple.
    Discharge route: coqprime [Coqprime/elliptic] (see the file header).
    See https://wuille.net/posts/secp256k1-tutorial/#222-scalar-multiplication *)
Lemma smul_add : forall (m n : Z) (a : Point),
  on_curve a -> smul (m + n) a = padd (smul m a) (smul n a).
Proof.
  (* OUTSTANDING: awaits the Coqprime/elliptic port (see the file header). *)
Admitted.

(** [smul] is multiplicative in the scalar: [(m * n) * a = m * (n * a)].
    Discharge route: coqprime [Coqprime/elliptic] (see the file header).
    See https://wuille.net/posts/secp256k1-tutorial/#222-scalar-multiplication *)
Lemma smul_mul : forall (m n : Z) (a : Point),
  on_curve a -> smul (m * n) a = smul m (smul n a).
Proof.
  (* OUTSTANDING: awaits the Coqprime/elliptic port (see the file header). *)
Admitted.

(* ================================================================= *)
(** ** The GLV endomorphism -- [lambda_endo] (STATED, [Admitted]). *)

(** Multiplying the x coordinate by [beta] is multiplying the point by
    [secp256k1_lambda].  This is the identity that makes
    [secp256k1_scalar_split_lambda] sound: splitting [k] as [k1 + k2*lambda]
    is only a speedup because [k*P] can then be recovered as
    [k1*P + k2*(beta*x, y)].  It holds for every curve point because secp256k1
    has cofactor one ([model.group_order]'s [cofactor_one]), so [on_curve] is
    the only hypothesis needed.  The field-side half, that [beta] is a cube root
    of unity, is proved by computation in [model.group]'s
    [beta_cube_root_unity].
    Discharge route: coqprime [Coqprime/elliptic] (see the file header).
    See https://wuille.net/posts/secp256k1-tutorial/#24-the-glv-endomorphism *)
Lemma lambda_endo : forall a : Point,
  on_curve a -> pmul_lambda a = smul secp256k1_lambda a.
Proof.
  (* OUTSTANDING: awaits the Coqprime/elliptic port (see the file header). *)
Admitted.
