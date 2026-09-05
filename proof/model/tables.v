(** * model.tables: the precomputed point tables, as opaque word data. *)
(** Copyright (C) 2026 remix7531
    SPDX-License-Identifier: MIT *)

(** The library ships three precomputed tables as multi-megabyte static
    initialisers ([secp256k1_pre_g] and [secp256k1_pre_g_128],
    [src/precomputed_ecmult.h:28-33]; [secp256k1_ecmult_gen_prec_table],
    [src/precomputed_ecmult_gen.h:19-21]).  They are NEVER #included into the
    extraction unit -- see the extern-tables convention spelled out in
    [proof/extraction.c:15-23] -- so the proof sees them as bare globals with a
    type and no contents.  This file is the model side of that convention: each
    table is a [Parameter] holding its words, and what those words MEAN is
    stated by an axiom.

    THIS IS THE ONE FILE UNDER [model/] AND [theory/] THAT DECLARES
    [Parameter]s AND [Axiom]s.  It is on the audit gate's AXIOMS-SRC allowlist
    for exactly that reason, and every name it declares appears in
    [audit/AXIOM_WHITELIST].

    Funspecs must mention ONLY the three [Parameter]s, never the right-hand
    side of an axiom below.  That is what keeps the contents replaceable: a
    second extraction unit (the tables.c -> clight/tables.v pair the Makefile's
    EXTRACT_SRCS already anticipates) can reify the real initialisers and turn
    each [_spec] axiom into a reflection proof over [model.group]'s [smul],
    without a single funspec changing.

    [gest_denote] -- the decoding of one [secp256k1_ge_storage] -- is defined
    here rather than in [model.group] because it exists only to state the three
    characterisation axioms, and because [model.group] deliberately keeps the
    storage type out of the group model.  It decodes WORDS (the [uint64_t n[4]]
    of each coordinate, little-endian, x then y, [src/field_5x52.h:45-47] and
    [src/group.h:38-41]; it is [secp256k1_fe_impl_to_storage]
    ([src/field_5x52_impl.h:430-435]) that makes word 0 the low one); the C
    struct's byte layout stays a [contract/] concern.

    Everything here is [vm_compute]-executable except the three tables
    themselves, which are [Parameter]s and reduce to nothing. *)

From Stdlib Require Import ZArith.
From Stdlib Require Import Lia.
From Stdlib Require Import List.

Require Import secp256k1.theory.arithmetic.
Require Export secp256k1.model.group.

Import ListNotations.
Open Scope Z_scope.

(** Deterministic obligation preprocessing, as in [model.field] and
    [model.group]: just [intros]. *)
Local Obligation Tactic := intros.

(* ================================================================= *)
(** ** Pinned geometry -- [pre_g_table_len] / [gen_table_blocks] / [gen_table_teeth].

    The window parameters this extraction is built with, transcribed from
    [src/ecmult.h:14-41] and [src/ecmult_gen.h:64-88].  They are the C's
    default (and only supported production) configuration, and the table
    lengths axiomatised further down are exactly what they imply.

    [model.ecmult] and [model.ecmult_gen] pin the SAME geometry for their own
    recodings, parametrically ([comb_spacing_of], [comb_points_of], ...).  The
    names here are deliberately disjoint from theirs -- [gen_table_teeth] not
    [COMB_TEETH]'s [comb_teeth] -- so that a [contract/] or [verif/] file
    importing this file alongside those is never ambiguous about which
    constant it means.  The values agree by construction and a downstream
    proof closes the identification with [vm_compute]. *)

(** [ECMULT_TABLE_SIZE(WINDOW_G)] at [ECMULT_WINDOW_SIZE = 15]
    ([src/ecmult.h:15,41]): [2^(w-2)] = 8192 entries, the number of odd
    multiples one [secp256k1_pre_g]-style table holds.
    See https://wuille.net/posts/secp256k1-tutorial/#327-scalar-multiplications-ecmult-ecmult_gen-ecmult_const *)
Definition pre_g_table_len : Z := 2 ^ (15 - 2).

(** [COMB_BLOCKS]: the number of blocks the signed-digit comb splits a scalar
    into, one table per block ([src/ecmult_gen.h:67]).
    See https://wuille.net/posts/secp256k1-tutorial/#327-scalar-multiplications-ecmult-ecmult_gen-ecmult_const *)
Definition gen_table_blocks : Z := 11.

(** [COMB_TEETH]: the number of bits one block's table covers simultaneously
    ([src/ecmult_gen.h:73]).
    See https://wuille.net/posts/secp256k1-tutorial/#327-scalar-multiplications-ecmult-ecmult_gen-ecmult_const *)
Definition gen_table_teeth : Z := 6.

(** [COMB_SPACING = CEIL_DIV(COMB_RANGE, COMB_BLOCKS * COMB_TEETH)]
    = [ceil(256 / 66)] = 4, the bit distance between two teeth of one block
    ([src/ecmult_gen.h:79]).
    See https://wuille.net/posts/secp256k1-tutorial/#327-scalar-multiplications-ecmult-ecmult_gen-ecmult_const *)
Definition gen_table_spacing : Z := 4.

(** [COMB_POINTS = 1 << (COMB_TEETH - 1)] = 32, the number of entries in one
    block's table ([src/ecmult_gen.h:87]).
    See https://wuille.net/posts/secp256k1-tutorial/#327-scalar-multiplications-ecmult-ecmult_gen-ecmult_const *)
Definition gen_table_points : Z := 2 ^ (gen_table_teeth - 1).

(* ================================================================= *)
(** ** Decoding a stored point -- [fe_of_words] / [gest_denote].

    A [secp256k1_ge_storage] is two [secp256k1_fe_storage]s, each four
    little-endian 64-bit words holding a fully normalised residue
    ([secp256k1_ge_to_storage] normalises both coordinates,
    [src/group_impl.h:876-887]).  The type cannot represent infinity, so a
    well-shaped entry always denotes an affine point. *)

(** The field element denoted by four little-endian 64-bit words.  The [mod p]
    is the identity on real table data (the words are a normalised residue) and
    is there only to make the function total.
    See https://wuille.net/posts/secp256k1-tutorial/#324-field-finite-field-element-representation *)
Program Definition fe_of_words (w0 w1 w2 w3 : Z) : Fe :=
  mkFe (eval4 (2 ^ 64) w0 w1 w2 w3 mod secp256k1_P) _.
Next Obligation.
  apply Z.mod_pos_bound.
  pose proof secp256k1_P_range.
  lia.
Qed.

(** The point denoted by the eight words of one [secp256k1_ge_storage]: x's
    four words first, then y's.  This is the model of the read side of
    [secp256k1_ge_from_storage] ([src/group_impl.h:889-895]), which the ecmult
    paths apply to every table entry they select.  An entry of any other length
    is not a stored point; the fallback keeps the function total and is never
    reached, since the shape axioms below pin every entry to eight words.
    See https://wuille.net/posts/secp256k1-tutorial/#326-group-group-operations-on-the-secp256k1-curve-group *)
Definition gest_denote (e : list Z) : Point :=
  match e with
  | [x0; x1; x2; x3; y0; y1; y2; y3] =>
      PAff (fe_of_words x0 x1 x2 x3) (fe_of_words y0 y1 y2 y3)
  | _ => PInf
  end.

(** Entry [i] of a one-dimensional table.  Spelled with Rocq's [nth] because
    [model/] is VST-free; for [0 <= i] it equals the [Znth] a [contract/]
    proof will use ([Znth]'s guard [Z_lt_dec i 0] is discharged by that
    hypothesis, and its default at [list Z] is [nil], so the two defaults
    agree).  The agreement is propositional, not definitional -- with [i] a
    variable the guard does not reduce -- so the bridge lemma
    [forall t i, 0 <= i -> gest_znth t i = Znth i t] is a [contract/tables]
    obligation; it cannot live here, where [Znth] is not in scope.
    See https://wuille.net/posts/secp256k1-tutorial/#327-scalar-multiplications-ecmult-ecmult_gen-ecmult_const *)
Definition gest_znth (t : list (list Z)) (i : Z) : list Z :=
  nth (Z.to_nat i) t nil.

(** Block [b] of the two-dimensional comb table, same convention.
    See https://wuille.net/posts/secp256k1-tutorial/#327-scalar-multiplications-ecmult-ecmult_gen-ecmult_const *)
Definition block_znth (t : list (list (list Z))) (b : Z) : list (list Z) :=
  nth (Z.to_nat b) t nil.

(** A well-shaped [secp256k1_ge_storage]: eight words, each a [uint64_t], and
    each coordinate already REDUCED.  The reduction is what the C guarantees
    and not merely what [fe_of_words] papers over with its totality [mod p]:
    [secp256k1_ge_to_storage] normalises both coordinates before storing them
    ([src/group_impl.h:876-887]), so every stored coordinate is [< p].
    Recording it here is what lets a [contract/] proof that needs a table
    entry to be a NORMALISED field element (magnitude 1 AND value [< p], say
    for a storage round trip) read that off the shape axioms below, instead
    of having to strengthen a trusted axiom later.
    See https://wuille.net/posts/secp256k1-tutorial/#326-group-group-operations-on-the-secp256k1-curve-group *)
Definition gest_wf (e : list Z) : Prop :=
  Zlength e = 8 /\
  Forall (fun w => 0 <= w < 2 ^ 64) e /\
  eval4 (2 ^ 64) (nth 0 e 0) (nth 1 e 0) (nth 2 e 0) (nth 3 e 0) < secp256k1_P /\
  eval4 (2 ^ 64) (nth 4 e 0) (nth 5 e 0) (nth 6 e 0) (nth 7 e 0) < secp256k1_P.

(** A well-shaped comb block: [COMB_POINTS] well-shaped entries.
    See https://wuille.net/posts/secp256k1-tutorial/#327-scalar-multiplications-ecmult-ecmult_gen-ecmult_const *)
Definition gen_block_wf (blk : list (list Z)) : Prop :=
  Zlength blk = gen_table_points /\ Forall gest_wf blk.

(* ================================================================= *)
(** ** What one comb entry is a multiple of -- [gen_half] / [gen_entry_offset].

    [model.ecmult_gen] states the same value from the algorithm's side, as
    [comb_table b m = smul (2*m - comb_mask b) G_half] over a tooth PATTERN
    [m]; the two agree when [m] is the pattern the array index [i] selects.
    This file indexes by [i], because that is what a [Znth] into the C array
    yields.

    [secp256k1_ecmult_gen_compute_table] ([src/ecmult_gen_compute_table_impl.h:17-105])
    builds block [b]'s entries out of [u = G/2] doubled along the block's
    teeth: entry [i] is the signed sum of the teeth's powers of two times
    [G/2], where tooth [t] enters positively exactly when bit [t] of [i] is
    set, and the top tooth always enters negatively (the algorithm recovers its
    sign by conditionally negating the whole selected entry). *)

(** The scalar [1/2 mod n], i.e. [secp256k1_scalar_half(&half,
    &secp256k1_scalar_one)] ([src/ecmult_gen_compute_table_impl.h:31]).  It is
    [(n+1)/2 = n_h + 1] for [model.constants]'s [secp256k1_N_H], so
    [2 * gen_half = n + 1 = 1] in the scalar field.
    See https://wuille.net/posts/secp256k1-tutorial/#232-the-scalar-field *)
Definition gen_half : Z := secp256k1_N_H + 1.

(** The sign tooth [t] contributes to entry [i]: [+1] when [t] is one of the
    low [COMB_TEETH - 1] teeth and bit [t] of [i] is set, [-1] otherwise.
    See https://wuille.net/posts/secp256k1-tutorial/#327-scalar-multiplications-ecmult-ecmult_gen-ecmult_const *)
Definition gen_tooth_sign (i t : Z) : Z :=
  if andb (Z.ltb t (gen_table_teeth - 1)) (Z.testbit i t) then 1 else -1.

(** The signed power-of-two sum over the first [k] teeth of block [b] for entry
    [i]: tooth [t] sits at bit [(b * COMB_TEETH + t) * COMB_SPACING].
    See https://wuille.net/posts/secp256k1-tutorial/#222-scalar-multiplication *)
Fixpoint gen_tooth_sum (b i : Z) (k : nat) : Z :=
  match k with
  | O => 0
  | S t =>
      gen_tooth_sum b i t
      + gen_tooth_sign i (Z.of_nat t) * 2 ^ ((b * gen_table_teeth + Z.of_nat t) * gen_table_spacing)
  end.

(** The multiplier of [G/2] that entry [i] of block [b] holds: the signed sum
    over all [COMB_TEETH] teeth.
    See https://wuille.net/posts/secp256k1-tutorial/#222-scalar-multiplication *)
Definition gen_entry_offset (b i : Z) : Z := gen_tooth_sum b i (Z.to_nat gen_table_teeth).

(* ================================================================= *)
(** ** The tables themselves -- [pre_g_words] / [pre_g_128_words] /
    [gen_prec_words].

    Opaque word data: one [list Z] of eight words per [secp256k1_ge_storage],
    in C array order.  Nothing below reduces -- these are the only [Parameter]s
    in the model, and the axioms that follow are the only thing said about
    them. *)

(** The words of [secp256k1_pre_g], the odd multiples of [G]
    ([src/precomputed_ecmult.h:32]).
    See https://wuille.net/posts/secp256k1-tutorial/#231-the-secp256k1-generator *)
Parameter pre_g_words : list (list Z).

(** The words of [secp256k1_pre_g_128], the odd multiples of [2^128 * G]
    ([src/precomputed_ecmult.h:33]).
    See https://wuille.net/posts/secp256k1-tutorial/#231-the-secp256k1-generator *)
Parameter pre_g_128_words : list (list Z).

(** The words of [secp256k1_ecmult_gen_prec_table], the comb table, as
    [COMB_BLOCKS] blocks of [COMB_POINTS] entries
    ([src/precomputed_ecmult_gen.h:21]).
    See https://wuille.net/posts/secp256k1-tutorial/#327-scalar-multiplications-ecmult-ecmult_gen-ecmult_const *)
Parameter gen_prec_words : list (list (list Z)).

(* ================================================================= *)
(** ** Shape axioms -- the lengths and word ranges the geometry implies.

    Discharged by reflection once the tables.c extraction unit exists; until
    then they record what the C declarations already say about the arrays'
    dimensions. *)

(** [secp256k1_pre_g] has [ECMULT_TABLE_SIZE(WINDOW_G)] entries.
    See https://wuille.net/posts/secp256k1-tutorial/#327-scalar-multiplications-ecmult-ecmult_gen-ecmult_const *)
Axiom pre_g_words_length : Zlength pre_g_words = pre_g_table_len.

(** Every [secp256k1_pre_g] entry is eight [uint64_t]s.
    See https://wuille.net/posts/secp256k1-tutorial/#326-group-group-operations-on-the-secp256k1-curve-group *)
Axiom pre_g_words_shape : Forall gest_wf pre_g_words.

(** [secp256k1_pre_g_128] has the same length as [secp256k1_pre_g].
    See https://wuille.net/posts/secp256k1-tutorial/#327-scalar-multiplications-ecmult-ecmult_gen-ecmult_const *)
Axiom pre_g_128_words_length : Zlength pre_g_128_words = pre_g_table_len.

(** Every [secp256k1_pre_g_128] entry is eight [uint64_t]s.
    See https://wuille.net/posts/secp256k1-tutorial/#326-group-group-operations-on-the-secp256k1-curve-group *)
Axiom pre_g_128_words_shape : Forall gest_wf pre_g_128_words.

(** The comb table has one block per [COMB_BLOCKS].
    See https://wuille.net/posts/secp256k1-tutorial/#327-scalar-multiplications-ecmult-ecmult_gen-ecmult_const *)
Axiom gen_prec_words_length : Zlength gen_prec_words = gen_table_blocks.

(** Every comb block holds [COMB_POINTS] entries of eight [uint64_t]s.
    See https://wuille.net/posts/secp256k1-tutorial/#327-scalar-multiplications-ecmult-ecmult_gen-ecmult_const *)
Axiom gen_prec_words_shape : Forall gen_block_wf gen_prec_words.

(* ================================================================= *)
(** ** Characterisation axioms -- what the three tables hold.

    These are the trusted statements this file exists for.  Each was checked
    against the generated C data ([src/precomputed_ecmult.c],
    [src/precomputed_ecmult_gen.c]) at several indices before being written
    down, and each is exactly the reflection goal a future [tables.c]
    extraction unit would discharge. *)

(** Entry [i] of [secp256k1_pre_g] is [(2i+1) * G] -- the table is built by
    starting at [G] and repeatedly adding [2G]
    ([src/ecmult_compute_table_impl.h:16-33]).
    See https://wuille.net/posts/secp256k1-tutorial/#231-the-secp256k1-generator *)
Axiom pre_g_words_spec : forall i : Z,
  0 <= i < pre_g_table_len ->
  gest_denote (gest_znth pre_g_words i) = smul (2 * i + 1) G.

(** Entry [i] of [secp256k1_pre_g_128] is [(2i+1) * 2^128 * G] -- the same
    construction started from [G] doubled 128 times
    ([src/ecmult_compute_table_impl.h:36-46]).
    See https://wuille.net/posts/secp256k1-tutorial/#231-the-secp256k1-generator *)
Axiom pre_g_128_words_spec : forall i : Z,
  0 <= i < pre_g_table_len ->
  gest_denote (gest_znth pre_g_128_words i) = smul ((2 * i + 1) * 2 ^ 128) G.

(** Entry [i] of comb block [b] is [gen_entry_offset b i] times [G/2]
    ([src/ecmult_gen_compute_table_impl.h:49-89]).
    See https://wuille.net/posts/secp256k1-tutorial/#327-scalar-multiplications-ecmult-ecmult_gen-ecmult_const *)
Axiom gen_prec_words_spec : forall b i : Z,
  0 <= b < gen_table_blocks ->
  0 <= i < gen_table_points ->
  gest_denote (gest_znth (block_znth gen_prec_words b) i)
    = smul (gen_entry_offset b i * gen_half) G.
