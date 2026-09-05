(** * model.ecmult_gen: the signed-digit multi-comb model of [R = n*G]. *)
(** Copyright (C) 2026 remix7531
    SPDX-License-Identifier: MIT *)

(** The trust boundary for generator multiplication.  [src/ecmult_gen_impl.h]
    computes [n*G] by a blinded signed-digit multi-comb (Section 3.3 of Mike
    Hamburg's "Fast and compact elliptic-curve cryptography",
    https://eprint.iacr.org/2012/309).  This file says what that computation
    IS, in terms of [model.group]'s [Point] / [padd] / [smul] and nothing else.

    GEOMETRY.  The extraction is pinned at [COMB_BLOCKS = 11] and
    [COMB_TEETH = 6] over [COMB_RANGE = 256] ([src/ecmult_gen.h:62-87]), so
    [COMB_SPACING = CEIL_DIV(256, 66) = 4], [COMB_BITS = 11*6*4 = 264] and
    [COMB_POINTS = 2^(6-1) = 32].  [comb_spacing_eq] / [comb_bits_eq] /
    [comb_points_eq] below pin all three BY COMPUTATION rather than by
    assertion.  Note that [COMB_BITS] is 264 and NOT 256: the comb covers more
    bits than a scalar has, and the top eight digits are always the [-2^i]
    ones.  The geometry-dependent definitions come in pairs: an [_of] form
    that takes the geometry as arguments -- and, for [ecmult_gen_model_of],
    the group order, the halved generator and the two blinding offsets too --
    and a pinned instance that is one application of it, so the
    [EXHAUSTIVE_TEST_ORDER] geometries stay expressible.  [G_half],
    [ecmult_gen_scalar_diff], [comb_table] and [gb_wf] have no [_of] form:
    they name [secp256k1_N] and [G] directly, and a toy-order instance passes
    its own values to [ecmult_gen_model_of] instead.

    WHAT IS DELIBERATELY NOT HERE.
    - [secp256k1_ecmult_gen_context.proj_blind] ([src/ecmult_gen.h:131-133]):
      it rescales the Jacobian Z coordinate of the first table lookup, so it
      changes the REPRESENTATION of an intermediate point and never its value
      -- provided it is non-zero, which [secp256k1_ecmult_gen_blind] enforces
      by a cmov ([src/ecmult_gen_impl.h:326]) and [secp256k1_gej_rescale]
      requires ([src/group_impl.h:865]); that side condition is an obligation
      on [contract/ecmult_gen]'s representation predicate.  Jacobian
      coordinates are a [contract/] concern (see [model.group]'s header),
      hence [GenBlind] has no [proj_blind] field.
    - [secp256k1_ecmult_gen_context.built], and with it
      [secp256k1_ecmult_gen_context_is_built] ([src/ecmult_gen_impl.h:22-24]):
      an initialisation flag with no value-level meaning, which belongs to
      [contract/ecmult_gen]'s representation predicate.
    - The precomputed table's storage words ([secp256k1_ecmult_gen_prec_table],
      [src/precomputed_ecmult_gen.h:21]): those live in [model.tables]; the
      POINTS they encode are [comb_table] below.

    ONE IDENTITY [contract/ecmult_gen] MUST SUPPLY.  The C stores only half
    the tooth patterns of each block and recovers the other half by looking
    up the bit-flipped index and negating the entry
    ([src/ecmult_gen_impl.h:181-186], implemented as the [sign] / [abs]
    conditional negation at [:230-254]).  In this file's terms that is
    [comb_table b (Z.lxor m (comb_mask b)) = pneg (comb_table b m)] for a
    submask [m] (one with [Z.land m (comb_mask b) = m]), and it is TRUE:
    there [Z.lxor m (comb_mask b) = comb_mask b - m], so
    [2*(mask - m) - mask = - (2*m - mask)].  It is deliberately NOT stated
    here and deliberately does NOT become a fourth [Admitted]: closing it
    needs [smul (- k) p = pneg (smul k p)] in BOTH sign directions, and the
    [k < 0] direction is [pneg]'s involutivity, which [model.group] has only
    propositionally (through [model.types]'s [fe_eq_ext], never by
    conversion) and which [model.group_law] does not state at all.
    [verif/ecmult_gen] cannot avoid the step, so [contract/ecmult_gen] is
    where it must be supplied -- recorded here, the way
    [comb_block_decomposition] was, rather than left for phase C to discover.

    COST.  Everything here is executable, but not everything is executable
    CHEAPLY: [model.group]'s affine [padd] / [pdouble] each perform one
    [fe_inv], about six seconds under [vm_compute] (see
    [model/tests_group.v]'s header).  So the geometry lemmas below
    ([comb_spacing_eq] / [comb_bits_eq] / [comb_points_eq]) and
    [ecmult_gen_scalar_diff] are ground-checkable in milliseconds, while
    [G_half] (about 380 point operations), [comb] at the pinned
    [COMB_BITS = 264] (about 530) and therefore [ecmult_gen_model] are hours
    of [vm_compute] and are NOT to be attempted as known-answer tests at the
    pinned geometry.  A small [nbits] with a small [p] is the way to exercise
    [comb] by computation.
    See https://wuille.net/posts/secp256k1-tutorial/#327-scalar-multiplications-ecmult-ecmult_gen-ecmult_const *)

From Stdlib Require Import ZArith.
From Stdlib Require Import Lia.
From Stdlib Require Import List.
Import ListNotations.

Require Import secp256k1.model.group.
Require Import secp256k1.model.scalar.

Open Scope Z_scope.

(** Deterministic obligation preprocessing, as in [model.field] / [model.group]:
    just [intros].  The default [program_simpl] auto-solver spins on the
    [(a - b) mod N] obligation shapes now that floyd is not loaded down here. *)
Local Obligation Tactic := intros.

(* ================================================================= *)
(** ** Comb geometry -- the [_of] family and the pinned [(11, 6)] instance.

    Transcribed from [src/ecmult_gen.h:79-87], where [COMB_SPACING] is
    [CEIL_DIV(COMB_RANGE, COMB_BLOCKS * COMB_TEETH)] and [util.h:195] defines
    [CEIL_DIV(x, y)] as [1 + (x - 1) / y]. *)

(** The comb's tooth spacing for a given geometry: [ceil(range / (blocks *
    teeth))].  Mirrors [COMB_SPACING] ([src/ecmult_gen.h:79]).
    See https://wuille.net/posts/secp256k1-tutorial/#327-scalar-multiplications-ecmult-ecmult_gen-ecmult_const *)
Definition comb_spacing_of (range blocks teeth : Z) : Z :=
  1 + (range - 1) / (blocks * teeth).

(** The number of scalar bits a comb of this geometry covers.  Mirrors
    [COMB_BITS] ([src/ecmult_gen.h:85]).
    See https://wuille.net/posts/secp256k1-tutorial/#327-scalar-multiplications-ecmult-ecmult_gen-ecmult_const *)
Definition comb_bits_of (blocks teeth spacing : Z) : Z := blocks * teeth * spacing.

(** The number of stored points per block: half the [2^teeth] tooth patterns,
    the other half being recovered by negation.  Mirrors [COMB_POINTS]
    ([src/ecmult_gen.h:87]).
    See https://wuille.net/posts/secp256k1-tutorial/#327-scalar-multiplications-ecmult-ecmult_gen-ecmult_const *)
Definition comb_points_of (teeth : Z) : Z := 2 ^ (teeth - 1).

(** The bit mask selecting block [b]'s teeth: [sum(2^((b*teeth + t)*spacing))]
    over [t] in [[0, teeth)].  This is the [mask(b)] of the derivation in
    [src/ecmult_gen_impl.h:121-128].
    See https://wuille.net/posts/secp256k1-tutorial/#327-scalar-multiplications-ecmult-ecmult_gen-ecmult_const *)
Definition comb_mask_of (teeth spacing b : Z) : Z :=
  fold_right Z.add 0
    (map (fun t => 2 ^ ((b * teeth + Z.of_nat t) * spacing))
         (seq 0 (Z.to_nat teeth))).

(** [COMB_RANGE]: the number of scalar bits the comb must support.
    See https://wuille.net/posts/secp256k1-tutorial/#327-scalar-multiplications-ecmult-ecmult_gen-ecmult_const *)
Definition comb_range : Z := 256.

(** [COMB_BLOCKS]: the number of blocks, one precomputed table each.
    See https://wuille.net/posts/secp256k1-tutorial/#327-scalar-multiplications-ecmult-ecmult_gen-ecmult_const *)
Definition comb_blocks : Z := 11.

(** [COMB_TEETH]: the number of bits one table lookup covers.
    See https://wuille.net/posts/secp256k1-tutorial/#327-scalar-multiplications-ecmult-ecmult_gen-ecmult_const *)
Definition comb_teeth : Z := 6.

(** [COMB_SPACING] at the pinned geometry.
    See https://wuille.net/posts/secp256k1-tutorial/#327-scalar-multiplications-ecmult-ecmult_gen-ecmult_const *)
Definition comb_spacing : Z := comb_spacing_of comb_range comb_blocks comb_teeth.

(** [COMB_BITS] at the pinned geometry.
    See https://wuille.net/posts/secp256k1-tutorial/#327-scalar-multiplications-ecmult-ecmult_gen-ecmult_const *)
Definition comb_bits : Z := comb_bits_of comb_blocks comb_teeth comb_spacing.

(** [COMB_POINTS] at the pinned geometry.
    See https://wuille.net/posts/secp256k1-tutorial/#327-scalar-multiplications-ecmult-ecmult_gen-ecmult_const *)
Definition comb_points : Z := comb_points_of comb_teeth.

(** [mask(b)] at the pinned geometry.
    See https://wuille.net/posts/secp256k1-tutorial/#327-scalar-multiplications-ecmult-ecmult_gen-ecmult_const *)
Definition comb_mask (b : Z) : Z := comb_mask_of comb_teeth comb_spacing b.

(** The pinned spacing is 4 -- a ground check of the [CEIL_DIV] transcription.
    See https://wuille.net/posts/secp256k1-tutorial/#327-scalar-multiplications-ecmult-ecmult_gen-ecmult_const *)
Lemma comb_spacing_eq : comb_spacing = 4.
Proof.
  vm_compute.
  reflexivity.
Qed.

(** The pinned comb covers 264 bits, eight more than a scalar has.
    See https://wuille.net/posts/secp256k1-tutorial/#327-scalar-multiplications-ecmult-ecmult_gen-ecmult_const *)
Lemma comb_bits_eq : comb_bits = 264.
Proof.
  vm_compute.
  reflexivity.
Qed.

(** The pinned tables hold 32 points each.
    See https://wuille.net/posts/secp256k1-tutorial/#327-scalar-multiplications-ecmult-ecmult_gen-ecmult_const *)
Lemma comb_points_eq : comb_points = 32.
Proof.
  vm_compute.
  reflexivity.
Qed.

(* ================================================================= *)
(** ** Half the generator -- [G_half].

    The comb is evaluated at [G/2] rather than at [G], which is what lets the
    C avoid a modular division by two when it forms the recoded scalar
    ([src/ecmult_gen_impl.h:93-103]).  There is deliberately no ground check
    that [pdouble G_half = G]: it is TRUE but out of [vm_compute] reach (see
    the COST note in the file header), and asserting it as a lemma would mean
    a fourth [Admitted] (the file has three: [comb_correct],
    [comb_block_decomposition] and [ecmult_gen_correct]). *)

(** The point [G/2]: the unique multiple of [G] that doubles to [G], namely
    [inv2 * G] with [inv2 = (n+1)/2 = 1/2 mod n] (the same [inv2] as
    [model.scalar]'s [scalar_half]).  It is a MODEL value only -- the C never
    forms it, having the [comb_table] entries precomputed instead.
    See https://wuille.net/posts/secp256k1-tutorial/#231-the-secp256k1-generator *)
Definition G_half : Point := smul ((secp256k1_N + 1) / 2) G.

(* ================================================================= *)
(** ** The comb value -- [comb_signs] / [comb_fold] / [comb] / [comb_table].

    [comb nbits s P] is the C's [comb(s, P) = sum((2*s[i]-1) * 2^i * P)] over
    [i] in [[0, nbits)] ([src/ecmult_gen_impl.h:77-81]): every bit of [s]
    contributes [+2^i * P] when set and [-2^i * P] when clear, so the result is
    a signed-digit expansion with no zero digit.  It is written here in Horner
    form (one [padd] and one [pdouble] per digit) rather than as a literal sum
    of [smul]s, so that its cost is linear in [nbits] and not quadratic -- see
    the COST note in the file header for what that still does and does not put
    within [vm_compute] reach. *)

(** The [nbits] signed digits of [s], least significant first: [1] where the
    bit is set, [-1] where it is clear.
    See https://wuille.net/posts/secp256k1-tutorial/#222-scalar-multiplication *)
Definition comb_signs (nbits s : Z) : list Z :=
  map (fun i => if Z.testbit s (Z.of_nat i) then 1 else -1)
      (seq 0 (Z.to_nat nbits)).

(** Horner evaluation of a signed-digit list (least significant first) at [p]:
    [d0 * p + 2 * (d1 * p + 2 * (...))].
    See https://wuille.net/posts/secp256k1-tutorial/#222-scalar-multiplication *)
Fixpoint comb_fold (ds : list Z) (p : Point) : Point :=
  match ds with
  | [] => PInf
  | d :: ds' => padd (smul d p) (pdouble (comb_fold ds' p))
  end.

(** The comb value [comb(s, p)] over [nbits] digits.  This is exactly what the
    two nested loops of [secp256k1_ecmult_gen_gej] accumulate into [r]
    ([src/ecmult_gen_impl.h:191-271]), before the final [ge_offset] addition.
    See https://wuille.net/posts/secp256k1-tutorial/#327-scalar-multiplications-ecmult-ecmult_gen-ecmult_const *)
Definition comb (nbits s : Z) (p : Point) : Point :=
  comb_fold (comb_signs nbits s) p.

(** The closed form of the comb: summing [(2*s[i]-1)*2^i] over [i < nbits]
    gives [2 * (s mod 2^nbits) - (2^nbits - 1)], so the comb is a single scalar
    multiple.  This is the algebraic step the C spells out at
    [src/ecmult_gen_impl.h:82-85].
    STATED AND [Admitted].  Intended discharge route: induction on [nbits],
    turning the [padd] / [pdouble] Horner step into scalar arithmetic with
    [model.group_law]'s [smul_add] and [smul_mul] -- which are themselves
    awaiting the coqprime [Coqprime/elliptic] port, so this lemma cannot be
    closed before they are.
    See https://wuille.net/posts/secp256k1-tutorial/#222-scalar-multiplication *)
Lemma comb_correct : forall (nbits s : Z) (p : Point),
  0 <= nbits ->
  0 <= s ->
  comb nbits s p = smul (2 * (s mod 2 ^ nbits) - (2 ^ nbits - 1)) p.
Proof.
  (* OUTSTANDING: awaits model.group_law's smul_add / smul_mul. *)
Admitted.

(** The point stored at block [b], tooth pattern [m]: the C's
    [table(b, m) = (m - mask(b)/2) * G], written over the integers as
    [(2*m - mask(b)) * (G/2)] so that no halving is needed
    ([src/ecmult_gen_impl.h:138-144]).  This is the value
    [secp256k1_ecmult_gen_prec_table[b][index]] denotes; the words themselves
    are [model.tables]'s business.
    See https://wuille.net/posts/secp256k1-tutorial/#327-scalar-multiplications-ecmult-ecmult_gen-ecmult_const *)
Definition comb_table (b m : Z) : Point := smul (2 * m - comb_mask b) G_half.

(** One line of the C's rewrite of the comb ([src/ecmult_gen_impl.h:146-156]):
    the sum over every block [b] of the entry that block's mask selects from
    [d >> i].  This is the inner loop of [secp256k1_ecmult_gen_gej].
    See https://wuille.net/posts/secp256k1-tutorial/#327-scalar-multiplications-ecmult-ecmult_gen-ecmult_const *)
Definition comb_block_row (d i : Z) : Point :=
  fold_right
    (fun b acc =>
       padd (comb_table (Z.of_nat b)
               (Z.land (Z.shiftr d i) (comb_mask (Z.of_nat b)))) acc)
    PInf (seq 0 (Z.to_nat comb_blocks)).

(** The [COMB_SPACING] lines of that rewrite, least significant first.
    See https://wuille.net/posts/secp256k1-tutorial/#327-scalar-multiplications-ecmult-ecmult_gen-ecmult_const *)
Definition comb_block_rows (d : Z) : list Point :=
  map (fun i => comb_block_row d (Z.of_nat i)) (seq 0 (Z.to_nat comb_spacing)).

(** Horner evaluation of those lines, weighting line [i] by [2^i] -- the outer
    loop of [secp256k1_ecmult_gen_gej], which doubles the accumulator between
    lines ([src/ecmult_gen_impl.h:158-169]).  Same shape as [comb_fold], one
    level up.
    See https://wuille.net/posts/secp256k1-tutorial/#222-scalar-multiplication *)
Fixpoint comb_row_fold (ps : list Point) : Point :=
  match ps with
  | [] => PInf
  | p :: ps' => padd p (pdouble (comb_row_fold ps'))
  end.

(** The identity that reorganises the comb into the C's per-block table
    lookups: [comb(d, G/2) = sum(2^i * sum(table(b, (d >> i) & mask(b))))]
    over [i < COMB_SPACING] and [b < COMB_BLOCKS], the derivation spelled out
    at [src/ecmult_gen_impl.h:146-169].  It is what [verif/ecmult_gen]'s body
    proof turns on, so it is stated here rather than left implicit.
    STATED AND [Admitted].  Intended discharge route: both sides expand to the
    same signed sum over the [COMB_BITS] bit positions, since [(b, t, i) |->
    (b*COMB_TEETH + t)*COMB_SPACING + i] enumerates [[0, COMB_BITS)] exactly
    once; turning the [padd] / [pdouble] nests into that sum needs
    [model.group_law]'s [smul_add] and [smul_mul], so this lemma cannot be
    closed before they are.
    See https://wuille.net/posts/secp256k1-tutorial/#327-scalar-multiplications-ecmult-ecmult_gen-ecmult_const *)
Lemma comb_block_decomposition : forall d : Z,
  0 <= d ->
  comb comb_bits d G_half = comb_row_fold (comb_block_rows d).
Proof.
  (* OUTSTANDING: awaits model.group_law's smul_add / smul_mul. *)
Admitted.

(* ================================================================= *)
(** ** The blinding state -- [GenBlind] / [ecmult_gen_scalar_diff] / [gb_wf].

    The C context holds values chosen so that
    [n*G == comb(n + scalar_offset, G/2) + ge_offset] ([src/ecmult_gen.h:122-127]),
    which is exactly [gb_wf] below with the blinding value [b] existentially
    quantified. *)

(** The scalar [(2^COMB_BITS - 1)/2 (mod n)] -- the difference between the
    caller's [gn] and the scalar whose bits the comb reads.  Specifies
    [secp256k1_ecmult_gen_scalar_diff] ([src/ecmult_gen_impl.h:36-52]), which
    reaches the same residue by doubling [1] a total of [COMB_BITS - 1] times
    and adding [-1/2]: [2^(COMB_BITS-1) - inv2 = inv2 * (2^COMB_BITS - 1)].
    See https://wuille.net/posts/secp256k1-tutorial/#232-the-scalar-field *)
Program Definition ecmult_gen_scalar_diff : Scalar :=
  mkScalar (((2 ^ comb_bits - 1) * ((secp256k1_N + 1) / 2)) mod secp256k1_N) _.
Next Obligation.
  apply Z.mod_pos_bound.
  pose proof secp256k1_N_range.
  lia.
Qed.

(** The blinding state of an [secp256k1_ecmult_gen_context]
    ([src/ecmult_gen.h:118-134]), stripped to the two fields that carry a
    value: the scalar offset added to the caller's scalar, and the point offset
    added to the comb result.  [built] and [proj_blind] are representation-only
    and deliberately absent -- see the file header.  The CamelCase [GenBlind] /
    [mkGenBlind] is a deliberate deviation from [STYLE.md]'s no-CamelCase rule,
    kept because it follows [model.types]'s [UInt64] / [mkUInt64] and
    [Int128] / [mkInt128] precedent and because the [contract/] and [verif/]
    files are written against these exact spellings: do not "correct" it.
    See https://wuille.net/posts/secp256k1-tutorial/#327-scalar-multiplications-ecmult-ecmult_gen-ecmult_const *)
Record GenBlind := mkGenBlind {
  gb_scalar_offset : Scalar;
  gb_ge_offset : Point
}.

(** The context invariant: for SOME blinding value [b], the scalar offset is
    [(2^COMB_BITS - 1)/2 - b] and the point offset is [b*G].  This is the C's
    own stated invariant ([src/ecmult_gen.h:122-127] and
    [src/ecmult_gen_impl.h:100-103]); [ecmult_gen_correct] below is exactly the
    claim that it is enough.  The leading conjunct is the C's own additional
    requirement: [secp256k1_ecmult_gen_blind] cmovs a zero blinding value to
    one because "the blinding value cannot be zero, as that would mean
    ge_offset = infinity, which secp256k1_gej_add_ge cannot handle"
    ([src/ecmult_gen_impl.h:332-334]), and that [gej_add_ge] -- the one
    [secp256k1_ecmult_gen_gej] performs on [ge_offset]
    ([src/ecmult_gen_impl.h:275]) -- does indeed [VERIFY_CHECK] it
    ([src/group_impl.h:730]).  It is phrased over the POINT rather than as
    [b mod n <> 0] so that it does not depend on [model.group_order]'s
    Admitted [G_order].
    See https://wuille.net/posts/secp256k1-tutorial/#23-isomorphism-between-scalars-and-points *)
Definition gb_wf (gb : GenBlind) : Prop :=
  gb_ge_offset gb <> PInf /\
  exists b : Z,
    scalar_val (gb_scalar_offset gb)
      = (scalar_val ecmult_gen_scalar_diff - b) mod secp256k1_N /\
    gb_ge_offset gb = smul b G.

(** The state built from a blinding value [b].  Specifies
    [secp256k1_ecmult_gen_blind] ([src/ecmult_gen_impl.h:294-345]) at the value
    level: how [b] is drawn (an RFC 6979 HMAC-DRBG over the previous offset and
    the caller's [seed32], see [model.hash]) is a separate concern, and this
    model claims nothing about its distribution -- only that whatever [b] comes
    out, the resulting state satisfies [gb_wf].  Note that the C does not
    compute [b*G] independently: it calls
    [secp256k1_ecmult_gen_ge(ctx, &ctx->ge_offset, &b)]
    ([src/ecmult_gen_impl.h:336]) THROUGH the context it is about to
    overwrite, so [gb_wf] is an INDUCTIVE invariant -- [contract/ecmult_gen]'s
    funspec for [secp256k1_ecmult_gen_blind] must require [gb_wf] of the
    incoming state, and [secp256k1_ecmult_gen_context_build] ([:17-20]) is
    what establishes the base case, via [gen_blind_default].
    See https://wuille.net/posts/secp256k1-tutorial/#327-scalar-multiplications-ecmult-ecmult_gen-ecmult_const *)
Program Definition gen_blind (b : Z) : GenBlind :=
  mkGenBlind
    (mkScalar ((scalar_val ecmult_gen_scalar_diff - b) mod secp256k1_N) _)
    (smul b G).
Next Obligation.
  apply Z.mod_pos_bound.
  pose proof secp256k1_N_range.
  lia.
Qed.

(** The unseeded state: [secp256k1_ecmult_gen_blind]'s [seed32 == NULL] branch
    ([src/ecmult_gen_impl.h:305-311]), which is also what
    [secp256k1_ecmult_gen_context_build] installs.  That branch sets
    [ge_offset = -G] and [scalar_offset = 1 + diff], i.e. it is [gen_blind] at
    the blinding value [-1] -- see [gen_blind_default_offsets].
    See https://wuille.net/posts/secp256k1-tutorial/#327-scalar-multiplications-ecmult-ecmult_gen-ecmult_const *)
Definition gen_blind_default : GenBlind := gen_blind (-1).

(** Every [gen_blind b] with a non-infinite point offset satisfies the context
    invariant, by construction.  The hypothesis is exactly what the C's cmov
    at [src/ecmult_gen_impl.h:334] establishes.
    See https://wuille.net/posts/secp256k1-tutorial/#327-scalar-multiplications-ecmult-ecmult_gen-ecmult_const *)
Lemma gen_blind_wf : forall b : Z,
  smul b G <> PInf ->
  gb_wf (gen_blind b).
Proof.
  intros b Hb.
  split.
  - exact Hb.
  - exists b.
    split.
    + reflexivity.
    + reflexivity.
Qed.

(** [gen_blind_default] really is the C's NULL branch: its point offset is
    [-G] and its scalar offset is [1 + diff], the two assignments at
    [src/ecmult_gen_impl.h:307-308].
    See https://wuille.net/posts/secp256k1-tutorial/#327-scalar-multiplications-ecmult-ecmult_gen-ecmult_const *)
Lemma gen_blind_default_offsets :
  gb_ge_offset gen_blind_default = pneg G /\
  scalar_val (gb_scalar_offset gen_blind_default)
    = scalar_val (scalar_add scalar_one ecmult_gen_scalar_diff).
Proof.
  split.
  - reflexivity.
  - cbn [gen_blind_default gen_blind scalar_add scalar_one
         gb_scalar_offset scalar_val].
    replace (scalar_val ecmult_gen_scalar_diff - -1)
      with (1 + scalar_val ecmult_gen_scalar_diff) by lia.
    reflexivity.
Qed.

(** The unseeded state satisfies the context invariant.
    See https://wuille.net/posts/secp256k1-tutorial/#327-scalar-multiplications-ecmult-ecmult_gen-ecmult_const *)
Lemma gen_blind_default_wf : gb_wf gen_blind_default.
Proof.
  apply gen_blind_wf.
  cbn [smul smul_pos pneg].
  discriminate.
Qed.

(* ================================================================= *)
(** ** The specification of generator multiplication -- [ecmult_gen_model]. *)

(** [n*G], the way the C computes it: form [d = n + scalar_offset (mod n)],
    take the comb of [d] at [G/2], and add the point offset.  Specifies BOTH
    [secp256k1_ecmult_gen_gej] ([src/ecmult_gen_impl.h:54-282]) and
    [secp256k1_ecmult_gen_ge] ([:284-291]) -- they differ only in whether the
    result is handed back in Jacobian or affine coordinates, which is a
    [contract/] distinction and not a model one.  Written at an arbitrary
    geometry, so that a toy order stays expressible: [order] is the group
    order the offsets are reduced modulo, [h] the halved generator the comb is
    evaluated at, and [off] / [geoff] the two blinding offsets.  They are
    taken as a scalar and a point rather than as a [GenBlind] because
    [GenBlind]'s [Scalar] field carries a [mod secp256k1_N] invariant that a
    toy order cannot satisfy.
    See https://wuille.net/posts/secp256k1-tutorial/#327-scalar-multiplications-ecmult-ecmult_gen-ecmult_const *)
Definition ecmult_gen_model_of (nbits order : Z) (h : Point)
                               (off : Z) (geoff : Point) (n : Z) : Point :=
  padd (comb nbits ((n + off) mod order) h) geoff.

(** [n*G] at the pinned geometry: [ecmult_gen_model_of] at [COMB_BITS],
    [secp256k1_N] and [G/2], reading the two offsets out of the context.  This
    is the specification [contract/ecmult_gen] and [verif/ecmult_gen] are
    written against.
    See https://wuille.net/posts/secp256k1-tutorial/#327-scalar-multiplications-ecmult-ecmult_gen-ecmult_const *)
Definition ecmult_gen_model (gb : GenBlind) (n : Z) : Point :=
  ecmult_gen_model_of comb_bits secp256k1_N G_half
    (scalar_val (gb_scalar_offset gb)) (gb_ge_offset gb) n.

(** The headline: on any well-formed blinding state the comb computes [n*G],
    so the blinding is value-transparent.
    STATED AND [Admitted].  Intended discharge route: [comb_correct] rewrites
    the comb to [smul (2*d - (2^COMB_BITS - 1)) G_half]; [model.group_law]'s
    [smul_mul] pushes the [G_half = inv2 * G] through to
    [smul (d - diff) G]; [gb_wf] replaces [d - diff] by [n - b]; and
    [model.group_law]'s [smul_add] plus [model.group_order]'s [G_order] (for
    the reduction mod [n]) close it against [gb_ge_offset gb = smul b G].
    Every one of those inputs is itself awaiting the coqprime
    [Coqprime/elliptic] port.
    See https://wuille.net/posts/secp256k1-tutorial/#327-scalar-multiplications-ecmult-ecmult_gen-ecmult_const *)
Lemma ecmult_gen_correct : forall (gb : GenBlind) (n : Z),
  gb_wf gb ->
  ecmult_gen_model gb n = smul n G.
Proof.
  (* OUTSTANDING: awaits comb_correct and the model.group_law facts. *)
Admitted.
