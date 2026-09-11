(** * theory.ecmult.ecmult_gen: the signed-digit multi-comb model of [R = n*G]. *)
(** Copyright (C) 2026 remix7531
    SPDX-License-Identifier: MIT *)

(** [src/ecmult_gen_impl.h] computes [n*G] with a blinded signed-digit
    multi-comb, following Section 3.3 of Mike Hamburg's
    "Fast and compact elliptic-curve cryptography",
    https://eprint.iacr.org/2012/309.

    The production geometry uses 11 blocks and 6 teeth over 256 scalar bits.
    Spacing is 4, the comb covers 264 bits, and each block stores 32 points.
    The top eight digits contribute negative powers of two. The [_of]
    definitions accept other geometries and, for [ecmult_gen_model_of],
    other group orders and blinding values.

    [GenBlind] models scalar and point offsets. Projective blinding rescales
    Jacobian coordinates without changing their point value when the scale
    is nonzero. The context's [built] flag is also a representation property.
    [theory/ecmult/tables.v] decodes storage words, while [comb_table] gives
    the mathematical table entries.

    The C stores half the tooth patterns and obtains the other half by
    negation. For a submask [m], [Z.lxor m (comb_mask b) = comb_mask b - m],
    and [2*(mask - m) - mask = -(2*m - mask)].

    Affine addition and doubling use field inversion. Evaluating [G_half]
    and the full comb with [vm_compute] is consequently expensive. *)

From Stdlib Require Import ZArith.
From Stdlib Require Import Lia.
From Stdlib Require Import List.
Import ListNotations.

Require secp256k1.specification.
Import specification.Math.
Import specification.Math.raw.
Require Import secp256k1.theory.scalar.limbs.
Import specification.Math.residues.
Export specification.Math.generator_context.

Open Scope Z_scope.

(** Explicit [intros] keeps obligation preprocessing independent of tactics
    loaded through [specification]. The modular range obligations below
    are discharged explicitly. *)
Local Obligation Tactic := intros.

(* ================================================================= *)
(** ** Comb geometry -- the [_of] family and the pinned [(11, 6)] instance.

    Transcribed from [src/ecmult_gen.h:79-87], where [COMB_SPACING] is
    [CEIL_DIV(COMB_RANGE, COMB_BLOCKS * COMB_TEETH)] and [util.h:195] defines
    [CEIL_DIV(x, y)] as [1 + (x - 1) / y]. *)

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
(** ** Half the generator: [G_half].

    The comb uses [G/2] so that forming the recoded scalar requires no
    modular division by two, as in [src/ecmult_gen_impl.h:93-103]. *)

(** The point [G/2]: the unique multiple of [G] that doubles to [G], namely
    [inv2 * G] with [inv2 = (n+1)/2 = 1/2 mod n] (the same [inv2] as
    [Math.scalar]'s [scalar_half]).  It is a MODEL value only -- the C never
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
    of [smul]s, giving linear rather than quadratic cost in [nbits]. *)

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
    See https://wuille.net/posts/secp256k1-tutorial/#222-scalar-multiplication *)
Lemma comb_correct : forall (nbits s : Z) (p : Point),
  0 <= nbits ->
  0 <= s ->
  comb nbits s p = smul (2 * (s mod 2 ^ nbits) - (2 ^ nbits - 1)) p.
Proof.
Admitted.

(** The point stored at block [b], tooth pattern [m]: the C's
    [table(b, m) = (m - mask(b)/2) * G], written over the integers as
    [(2*m - mask(b)) * (G/2)] so that no halving is needed
    ([src/ecmult_gen_impl.h:138-144]).  This is the value
    [secp256k1_ecmult_gen_prec_table[b][index]] denotes; the words themselves
    are [theory/ecmult/tables.v]'s business.
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
    at [src/ecmult_gen_impl.h:146-169].
    See https://wuille.net/posts/secp256k1-tutorial/#327-scalar-multiplications-ecmult-ecmult_gen-ecmult_const *)
Lemma comb_block_decomposition : forall d : Z,
  0 <= d ->
  comb comb_bits d G_half = comb_row_fold (comb_block_rows d).
Proof.
Admitted.

(* ================================================================= *)
(** ** The blinding state -- [GenBlind] / [ecmult_gen_scalar_diff] / [gb_wf].

    The C context holds values chosen so that
    [n*G == comb(n + scalar_offset, G/2) + ge_offset] ([src/ecmult_gen.h:122-127]),
    which is exactly [gb_wf] with the blinding value [b] existentially
    quantified. *)

(** The state built from a blinding value [b].  Specifies
    [secp256k1_ecmult_gen_blind] ([src/ecmult_gen_impl.h:294-345]) at the value
    level: how [b] is drawn (an RFC 6979 HMAC-DRBG over the previous offset and
    the caller's [seed32], see [Math.sha256]) is a separate concern, and this
    model claims nothing about its distribution -- only that whatever [b] comes
    out, the resulting state satisfies [gb_wf].  Note that the C does not
    compute [b*G] independently: it calls
    [secp256k1_ecmult_gen_ge(ctx, &ctx->ge_offset, &b)]
    ([src/ecmult_gen_impl.h:336]) through the context it is about to
    overwrite, so [gb_wf] is an invariant of the incoming state.
    [secp256k1_ecmult_gen_context_build] establishes the base case through
    [gen_blind_default].
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
         gb_scalar_offset scalar_val scalar_reduce].
    replace (scalar_val ecmult_gen_scalar_diff - -1)
      with (1 + scalar_val ecmult_gen_scalar_diff) by lia.
    reflexivity.
Qed.

(** The unseeded state satisfies the context invariant.
    See https://wuille.net/posts/secp256k1-tutorial/#327-scalar-multiplications-ecmult-ecmult_gen-ecmult_const *)
Lemma gen_blind_default_wf : gb_wf gen_blind_default.
Proof.
  apply gen_blind_wf.
  cbn [smul repeat_addition' pneg].
  discriminate.
Qed.

(* ================================================================= *)
(** ** The specification of generator multiplication -- [ecmult_gen_model]. *)

(** [n*G], the way the C computes it: form [d = n + scalar_offset (mod n)],
    take the comb of [d] at [G/2], and add the point offset.  Specifies BOTH
    [secp256k1_ecmult_gen_gej] ([src/ecmult_gen_impl.h:54-282]) and
    [secp256k1_ecmult_gen_ge] ([:284-291]) -- they differ only in whether the
    result is handed back in Jacobian or affine coordinates, which is a
    representation distinction.  Written at an arbitrary
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
    is the specification [vst/ecmult/contract.v] and [vst/ecmult/verif] are
    written against.
    See https://wuille.net/posts/secp256k1-tutorial/#327-scalar-multiplications-ecmult-ecmult_gen-ecmult_const *)
Definition ecmult_gen_model (gb : GenBlind) (n : Z) : Point :=
  ecmult_gen_model_of comb_bits secp256k1_N G_half
    (scalar_val (gb_scalar_offset gb)) (gb_ge_offset gb) n.

(** On a well-formed blinding state, generator multiplication computes
    [n*G].
    See https://wuille.net/posts/secp256k1-tutorial/#327-scalar-multiplications-ecmult-ecmult_gen-ecmult_const *)
Lemma ecmult_gen_correct : forall (gb : GenBlind) (n : Z),
  gb_wf gb ->
  ecmult_gen_model gb n = smul n G.
Proof.
Admitted.
