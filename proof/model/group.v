(** * model.group: the secp256k1 curve group, in affine coordinates only. *)
(** Copyright (C) 2026 remix7531
    SPDX-License-Identifier: MIT *)

(** The trust boundary for the group subsystem.  There is exactly ONE point
    type here -- [Point], either the point at infinity or an affine [(x, y)]
    pair of [model.field] residues -- and every group operation is stated on
    it, as the textbook chord-and-tangent law over [Fe].

    JACOBIAN COORDINATES ARE A REPRESENTATION CONCERN AND NEVER A MODEL TYPE.
    The C's [secp256k1_gej] (carrying [x/z^2], [y/z^3], [z] and an [infinity]
    flag) is bridged in [contract/group] by [gej_repr mx my mz P], exactly as
    the 5x52 limbs of a [secp256k1_fe] are bridged to an [Fe] there.  There is
    no [Jacobian] inductive in this file and there should never be one: a
    Jacobian triple is one of infinitely many encodings of a single [Point], so
    a model that carried [z] would state a weaker theorem than the C deserves.
    The same goes for the C's [secp256k1_ge_storage] byte layout, which is
    documented as platform-dependent and is likewise a [contract/] matter.
    See https://wuille.net/posts/secp256k1-tutorial/#25-jacobian-coordinates

    Properties OF the definitions below -- commutativity, associativity, the
    GLV identity, the order of [G] -- live in [model.group_law] and
    [model.group_order].  They sit under [model/] rather than [theory/] because
    they mention model definitions and so are part of the specification, not
    generic [Z] math (the same ruling that put [model.jacobi_rules] here).

    Everything in this file is [vm_compute]-executable: [padd] and [smul] run
    on concrete points, which is what the known-answer tests need and what
    [on_curve_G] and [beta_cube_root_unity] below already exercise. *)

Require Import ZArith.
Require Import Bool.
Require Import Lia.
Require Export secp256k1.model.field.

Open Scope Z_scope.

(** Deterministic obligation preprocessing, as in [model.field]: just [intros].
    The default [program_simpl] auto-solver spins on the [(p - a) mod p]
    obligation shapes now that floyd is no longer loaded down here. *)
Local Obligation Tactic := intros.

(* ================================================================= *)
(** ** Points and the curve equation -- [Point] / [secp256k1_B] / [on_curve]. *)

(** A point of the secp256k1 group: the identity [PInf], or an affine pair.
    Models the C's [secp256k1_ge] (whose [infinity] flag selects between the
    two constructors) and, through [contract/group]'s [gej_repr], the value
    denoted by a [secp256k1_gej] ([src/group.h:11-32]).
    See https://wuille.net/posts/secp256k1-tutorial/#22-the-curve-group *)
Inductive Point := PInf | PAff (x y : Fe).

(** The curve coefficient [b] of [y^2 = x^3 + b].  Mirrors the C's
    [SECP256K1_B] ([src/group_impl.h:73]) in its non-exhaustive-test setting;
    the coefficient [a] is [0] and so never appears below.
    See https://wuille.net/posts/secp256k1-tutorial/#22-the-curve-group *)
Definition secp256k1_B : Z := 7.

(** [a] satisfies the curve equation [y^2 = x^3 + 7] over [F_p] (the identity
    trivially does).  This is the invariant every [secp256k1_ge] / [gej]
    funspec carries, and the property [secp256k1_ge_set_xo_var]
    ([src/group_impl.h:346-364]) establishes for its output.
    See https://wuille.net/posts/secp256k1-tutorial/#22-the-curve-group *)
Definition on_curve (a : Point) : Prop :=
  match a with
  | PInf => True
  | PAff x y =>
      (fe_val y * fe_val y) mod secp256k1_P
        = (fe_val x * fe_val x * fe_val x + secp256k1_B) mod secp256k1_P
  end.

(* ================================================================= *)
(** ** Observing a point -- [point_coords] / [point_eqb].

    A [Point] carries [Fe] records, and an [Fe] record carries its range PROOF,
    so two points with the same coordinates are only propositionally equal (via
    [model.types]'s [fe_eq_ext]), never convertible.  Ground checks therefore
    compare VALUES: [point_coords] projects the coordinates out to [Z], and
    [point_eqb] decides equality on those values -- both reduce under
    [vm_compute] without ever touching a proof term. *)

(** The coordinates of [a] as plain integers, or [None] at infinity.  This is
    the shape every known-answer test compares against.
    See https://wuille.net/posts/secp256k1-tutorial/#22-the-curve-group *)
Definition point_coords (a : Point) : option (Z * Z) :=
  match a with
  | PInf => None
  | PAff x y => Some (fe_val x, fe_val y)
  end.

(** Decidable point equality.  Specifies the C's [secp256k1_ge_eq_var] (not
    reached by this extraction -- see [schnorr-manifest-excluded.tsv] -- but the
    same comparison the [gej] equality helpers perform after normalisation).
    See https://wuille.net/posts/secp256k1-tutorial/#22-the-curve-group *)
Definition point_eqb (a b : Point) : bool :=
  match a, b with
  | PInf, PInf => true
  | PAff x1 y1, PAff x2 y2 =>
      andb (Z.eqb (fe_val x1) (fe_val x2)) (Z.eqb (fe_val y1) (fe_val y2))
  | _, _ => false
  end.

(** [point_eqb] really decides equality: the range proofs inside the [Fe]s are
    irrelevant ([model.types]'s [fe_eq_ext]).
    See https://wuille.net/posts/secp256k1-tutorial/#22-the-curve-group *)
Lemma point_eqb_eq : forall a b : Point, point_eqb a b = true <-> a = b.
Proof.
  intros a b.
  split.
  - intros Heq.
    destruct a as [|x1 y1], b as [|x2 y2]; try discriminate.
    + reflexivity.
    + simpl in Heq.
      apply andb_true_iff in Heq.
      destruct Heq as [Hx Hy].
      apply Z.eqb_eq in Hx.
      apply Z.eqb_eq in Hy.
      rewrite (fe_eq_ext x1 x2 Hx).
      rewrite (fe_eq_ext y1 y2 Hy).
      reflexivity.
  - intros Heq.
    subst b.
    destruct a as [|x1 y1].
    + reflexivity.
    + simpl.
      apply andb_true_iff.
      split.
      * apply Z.eqb_refl.
      * apply Z.eqb_refl.
Qed.

(* ================================================================= *)
(** ** The group law -- [pneg] / [pdouble] / [padd].

    The chord-and-tangent law written out in full, with [fe_inv] doing the
    field division.  Every C addition routine ([gej_add_ge], [gej_add_ge_var],
    [gej_add_zinv_var], [gej_double], [gej_double_var]) computes this same
    function on a different Jacobian encoding of the same points, which is why
    the model has one [padd] and one [pdouble] rather than five. *)

(** Negation: mirror the point in the x-axis.  Specifies [secp256k1_ge_neg]
    ([src/group_impl.h:148-156]) and the C's [secp256k1_gej_neg].
    See https://wuille.net/posts/secp256k1-tutorial/#221-the-group-operation *)
Definition pneg (a : Point) : Point :=
  match a with
  | PInf => PInf
  | PAff x y => PAff x (fe_negate y)
  end.

(** Doubling by the tangent line, slope [lam = 3x^2 / 2y] (the curve's [a] is
    [0]).  A point with [y = 0] is its own negative, so it doubles to the
    identity -- on secp256k1 no such affine point exists, but the model is
    total anyway.  Specifies [secp256k1_gej_double]
    ([src/group_impl.h:459-492]) and [secp256k1_gej_double_var] ([:494-523]).
    See https://wuille.net/posts/secp256k1-tutorial/#221-the-group-operation *)
Definition pdouble (a : Point) : Point :=
  match a with
  | PInf => PInf
  | PAff x y =>
      if fe_is_zero y then PInf
      else
        let lam := fe_mul (fe_mul_int (fe_sqr x) 3) (fe_inv (fe_mul_int y 2)) in
        let x3 := fe_add (fe_sqr lam) (fe_negate (fe_mul_int x 2)) in
        let y3 := fe_add (fe_mul lam (fe_add x (fe_negate x3))) (fe_negate y) in
        PAff x3 y3
  end.

(** The full affine group law, all five cases: identity on the left, identity
    on the right, equal [x] with equal [y] (tangent -- delegate to [pdouble]),
    equal [x] with opposite [y] (vertical chord -- the identity), and the
    generic chord with slope [lam = (y2 - y1) / (x2 - x1)].  Specifies
    [secp256k1_gej_add_ge] ([src/group_impl.h:723-858]),
    [secp256k1_gej_add_ge_var] ([:589-650]) and [secp256k1_gej_add_zinv_var]
    ([:652-720]), each of which computes this function in Jacobian form.
    See https://wuille.net/posts/secp256k1-tutorial/#221-the-group-operation *)
Definition padd (a b : Point) : Point :=
  match a, b with
  | PInf, _ => b
  | _, PInf => a
  | PAff x1 y1, PAff x2 y2 =>
      if Z.eqb (fe_val x1) (fe_val x2) then
        (if Z.eqb (fe_val y1) (fe_val y2) then pdouble a else PInf)
      else
        let lam := fe_mul (fe_add y2 (fe_negate y1))
                          (fe_inv (fe_add x2 (fe_negate x1))) in
        let x3 := fe_add (fe_sqr lam) (fe_negate (fe_add x1 x2)) in
        let y3 := fe_add (fe_mul lam (fe_add x1 (fe_negate x3))) (fe_negate y1) in
        PAff x3 y3
  end.

(* ================================================================= *)
(** ** Scalar multiplication -- [smul_pos] / [smul]. *)

(** Double-and-add over the exponent's binary digits, most-significant first.
    Structural on [positive], hence total and [vm_compute]-fast: a 256-bit
    multiple costs about 380 [padd] / [pdouble] steps rather than [n] of them.
    See https://wuille.net/posts/secp256k1-tutorial/#222-scalar-multiplication *)
Fixpoint smul_pos (n : positive) (a : Point) : Point :=
  match n with
  | xH => a
  | xO m => pdouble (smul_pos m a)
  | xI m => padd a (pdouble (smul_pos m a))
  end.

(** [n * a] for any integer [n]: the identity at [0], double-and-add for a
    positive [n], and the negation of [(-n) * a] for a negative one.  Not one C
    function -- it is the value every scalar multiplication in the library is
    specified against ([model.ecmult]'s [strauss], [model.ecmult_gen]'s
    [ecmult_gen_model], and BIP-340 key generation in [model.bip340]).
    See https://wuille.net/posts/secp256k1-tutorial/#222-scalar-multiplication *)
Definition smul (n : Z) (a : Point) : Point :=
  match n with
  | Z0 => PInf
  | Zpos m => smul_pos m a
  | Zneg m => pneg (smul_pos m a)
  end.

(* ================================================================= *)
(** ** The generator -- [G_x] / [G_y] / [G].

    The SEC2 2.7.1 generator, transcribed limb-for-limb from the C's
    [SECP256K1_G] macro ([src/group_impl.h:36-41]), which initialises
    [secp256k1_ge_const_g] ([:71]).  [on_curve_G] below re-derives the curve
    equation from these digits, so a transcription typo cannot pass silently. *)

(** The generator's x coordinate.
    See https://wuille.net/posts/secp256k1-tutorial/#231-the-secp256k1-generator *)
Definition G_x : Z :=
  0x79BE667EF9DCBBAC55A06295CE870B07029BFCDB2DCE28D959F2815B16F81798.

(** The generator's y coordinate.
    See https://wuille.net/posts/secp256k1-tutorial/#231-the-secp256k1-generator *)
Definition G_y : Z :=
  0x483ADA7726A3C4655DA4FBFC0E1108A8FD17B448A68554199C47D08FFB10D4B8.

(** [G_x] as a field element.
    See https://wuille.net/posts/secp256k1-tutorial/#231-the-secp256k1-generator *)
Program Definition fe_G_x : Fe := mkFe G_x _.
Next Obligation.
  unfold G_x, secp256k1_P.
  lia.
Qed.

(** [G_y] as a field element.
    See https://wuille.net/posts/secp256k1-tutorial/#231-the-secp256k1-generator *)
Program Definition fe_G_y : Fe := mkFe G_y _.
Next Obligation.
  unfold G_y, secp256k1_P.
  lia.
Qed.

(** The secp256k1 generator [G].  Specifies the C's [secp256k1_ge_const_g].
    See https://wuille.net/posts/secp256k1-tutorial/#231-the-secp256k1-generator *)
Definition G : Point := PAff fe_G_x fe_G_y.

(** [G] really is on the curve -- a ground check of the two literals above.
    See https://wuille.net/posts/secp256k1-tutorial/#231-the-secp256k1-generator *)
Lemma on_curve_G : on_curve G.
Proof.
  vm_compute.
  reflexivity.
Qed.

(* ================================================================= *)
(** ** The GLV endomorphism -- [secp256k1_beta] / [beta] / [pmul_lambda]. *)

(** [beta]: the nontrivial cube root of [1] modulo [p], transcribed from the
    C's [secp256k1_const_beta] ([src/field.h:69-72]).  It lives here rather
    than in [model.constants] because it is only ever used by the curve-level
    endomorphism below; its scalar counterpart [secp256k1_lambda] (a cube root
    of [1] modulo [n]) is in [model.constants].
    See https://wuille.net/posts/secp256k1-tutorial/#24-the-glv-endomorphism *)
Definition secp256k1_beta : Z :=
  0x7AE96A2B657C07106E64479EAC3434E99CF0497512F58995C1396C28719501EE.

(** [beta] as a field element.
    See https://wuille.net/posts/secp256k1-tutorial/#24-the-glv-endomorphism *)
Program Definition beta : Fe := mkFe secp256k1_beta _.
Next Obligation.
  unfold secp256k1_beta, secp256k1_P.
  lia.
Qed.

(** [beta] is a nontrivial cube root of unity mod [p] -- a ground check of the
    literal above, mirroring [on_curve_G] for the generator.  This is the
    field-side half of the GLV setup; the curve-side half is
    [model.group_law]'s [lambda_endo].
    See https://wuille.net/posts/secp256k1-tutorial/#24-the-glv-endomorphism *)
Lemma beta_cube_root_unity :
  secp256k1_beta ^ 3 mod secp256k1_P = 1 /\ secp256k1_beta <> 1.
Proof.
  split.
  - vm_compute.
    reflexivity.
  - unfold secp256k1_beta.
    discriminate.
Qed.

(** The GLV endomorphism [(x, y) |-> (beta*x, y)].  Specifies
    [secp256k1_ge_mul_lambda] ([src/group_impl.h:917-923], whose body is one
    [secp256k1_fe_mul] against [secp256k1_const_beta]).  That C function is
    NOT reached by this extraction (only [ecmult_const] and the pippenger-only
    [secp256k1_ecmult_endo_split] call it, both excluded -- see
    [schnorr-manifest-excluded.tsv]); the model is kept anyway because the
    identity it carries ([lambda_endo]) is what gives
    [secp256k1_scalar_split_lambda]'s scalar decomposition its meaning.
    See https://wuille.net/posts/secp256k1-tutorial/#24-the-glv-endomorphism *)
Definition pmul_lambda (a : Point) : Point :=
  match a with
  | PInf => PInf
  | PAff x y => PAff (fe_mul x beta) y
  end.

(* ================================================================= *)
(** ** X-only points -- [lift_x_even] / [has_even_y].

    BIP-340 identifies a public key with the x coordinate of a point whose y
    is even.  [lift_x_even] is the decoder and [has_even_y] the parity test the
    encoder uses; [model.bip340]'s [xonly_parse] / [xonly_serialize] are built
    from exactly this pair. *)

(** Lift an x coordinate to the curve point with EVEN y, or [None] when
    [x^3 + 7] is not a square.  Specifies BIP-340's [lift_x] and, together with
    the caller's oddness argument, [secp256k1_ge_set_xo_var]
    ([src/group_impl.h:346-364]): that C function computes the same
    [secp256k1_fe_sqrt] of [x^3 + 7], returns whether the square root existed,
    and negates y when its parity differs from the requested one.  This model
    fixes the requested parity to even (the only case BIP-340 uses) and folds
    the C's [int] return into the [option].
    See https://wuille.net/posts/secp256k1-tutorial/#326-group-group-operations-on-the-secp256k1-curve-group *)
Definition lift_x_even (x : Fe) : option Point :=
  match fe_sqrt (fe_add_int (fe_mul x (fe_sqr x)) secp256k1_B) with
  | None => None
  | Some y => Some (PAff x (if fe_is_odd y then fe_negate y else y))
  end.

(** Does [a] have an even y coordinate?  The identity has none, so it is
    [false] there.  Specifies the [secp256k1_fe_is_odd] parity tests that
    BIP-340 signing and [secp256k1_xonly_pubkey_*] perform on a point's y
    ([src/modules/extrakeys/main_impl.h:22-57]).
    See https://wuille.net/posts/secp256k1-tutorial/#326-group-group-operations-on-the-secp256k1-curve-group *)
Definition has_even_y (a : Point) : bool :=
  match a with
  | PInf => false
  | PAff _ y => negb (fe_is_odd y)
  end.
