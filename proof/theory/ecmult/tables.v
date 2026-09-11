(** * theory.ecmult.tables: the extracted precomputed point tables. *)
(** Copyright (C) 2026 remix7531
    SPDX-License-Identifier: MIT *)

(** The extraction includes the three production precomputed tables.
    This file decodes their CompCert initializers into unsigned 64-bit words.
    Decoding returns [None] for a wrong constructor, entry width or trailing
    data. The predicates below describe table shape and point values.

    [gest_denote] decodes eight words, four per coordinate, x before y and
    least significant word first. The C byte layout belongs to the VST
    representation predicates. *)

From Stdlib Require Import ZArith.
From Stdlib Require Import Lia.
From Stdlib Require Import List.
From compcert Require Import AST Integers.

Require Import secp256k1.theory.integers.arithmetic.
Require Import secp256k1.theory.scalar.limbs.
Require Import secp256k1.clight.extraction.
Require secp256k1.specification.
Import specification.Math.
Export specification.Math.raw.
Import specification.Math.residues.

Import ListNotations.
Open Scope Z_scope.

(** Explicit [intros] keeps obligation preprocessing independent of tactics
    loaded through [specification]. The range proofs remain explicit. *)
Local Obligation Tactic := intros.

(* ================================================================= *)
(** ** Table geometry.

    These dimensions match the production configuration in [src/ecmult.h]
    and [src/ecmult_gen.h]. The [gen_table_] prefix distinguishes storage
    dimensions from the comb model's parameters. *)

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
    is not a stored point; the fallback keeps the function total.
    See https://wuille.net/posts/secp256k1-tutorial/#326-group-group-operations-on-the-secp256k1-curve-group *)
Definition gest_denote (e : list Z) : Point :=
  match e with
  | [x0; x1; x2; x3; y0; y1; y2; y3] =>
      PAff (fe_of_words x0 x1 x2 x3) (fe_of_words y0 y1 y2 y3)
  | _ => PInf
  end.

(** Entry [i] of a one-dimensional table, using Rocq's [nth]. For
    [0 <= i] it equals the [Znth] used by a representation proof.
    That hypothesis discharges the [Z_lt_dec i 0] guard, and both
    functions use [nil] as their default at [list Z]. The agreement is
    propositional because a variable index does not reduce the guard.
    See https://wuille.net/posts/secp256k1-tutorial/#327-scalar-multiplications-ecmult-ecmult_gen-ecmult_const *)
Definition gest_znth (t : list (list Z)) (i : Z) : list Z :=
  nth (Z.to_nat i) t nil.

(** Block [b] of the two-dimensional comb table, same convention.
    See https://wuille.net/posts/secp256k1-tutorial/#327-scalar-multiplications-ecmult-ecmult_gen-ecmult_const *)
Definition block_znth (t : list (list (list Z))) (b : Z) : list (list Z) :=
  nth (Z.to_nat b) t nil.

(** A stored point has eight unsigned 64-bit words and reduced coordinates.
    [secp256k1_ge_to_storage] normalises both coordinates before storage.
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

    [theory/ecmult/ecmult_gen.v] states the same value from the algorithm's side, as
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
    [(n+1)/2 = n_h + 1] for [limbs.secp256k1_N_H], so
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
(** ** Decoding the extracted table initialisers. *)

(** Decode only 64-bit integer initialisers.  [Int64.unsigned] recovers the C
    [uint64_t] value even when clightgen printed a signed representative. *)
Fixpoint decode_int64s (data : list init_data) : option (list Z) :=
  match data with
  | nil => Some nil
  | Init_int64 word :: rest =>
      match decode_int64s rest with
      | Some words => Some (Int64.unsigned word :: words)
      | None => None
      end
  | _ => None
  end.

(** Take exactly [count] elements, failing if the input is too short. *)
Fixpoint take_exact {A : Type} (count : nat) (values : list A)
    : option (list A * list A) :=
  match count, values with
  | O, _ => Some (nil, values)
  | S count', value :: rest =>
      match take_exact count' rest with
      | Some (front, tail) => Some (value :: front, tail)
      | None => None
      end
  | S _, nil => None
  end.

(** Split into exactly [row_count] rows and reject trailing input. *)
Fixpoint rows_exact_aux {A : Type} (row_count row_width : nat)
    (values : list A) : option (list (list A) * list A) :=
  match row_count with
  | O => Some (nil, values)
  | S row_count' =>
      match take_exact row_width values with
      | Some (row, rest) =>
          match rows_exact_aux row_count' row_width rest with
          | Some (rows, tail) => Some (row :: rows, tail)
          | None => None
          end
      | None => None
      end
  end.

Definition rows_exact {A : Type} (row_count row_width : nat)
    (values : list A) : option (list (list A)) :=
  match rows_exact_aux row_count row_width values with
  | Some (rows, nil) => Some rows
  | _ => None
  end.

Definition decode_storage_table (entry_count : nat) (data : list init_data)
    : option (list (list Z)) :=
  match decode_int64s data with
  | Some words => rows_exact entry_count 8 words
  | None => None
  end.

(** The words of [secp256k1_pre_g], the odd multiples of [G]
    ([src/precomputed_ecmult.h:32]).
    See https://wuille.net/posts/secp256k1-tutorial/#231-the-secp256k1-generator *)
Definition pre_g_words : option (list (list Z)) :=
  decode_storage_table (Z.to_nat pre_g_table_len)
    (gvar_init v_secp256k1_pre_g).

(** The words of [secp256k1_pre_g_128], the odd multiples of [2^128 * G]
    ([src/precomputed_ecmult.h:33]).
    See https://wuille.net/posts/secp256k1-tutorial/#231-the-secp256k1-generator *)
Definition pre_g_128_words : option (list (list Z)) :=
  decode_storage_table (Z.to_nat pre_g_table_len)
    (gvar_init v_secp256k1_pre_g_128).

(** The words of [secp256k1_ecmult_gen_prec_table], the comb table, as
    [COMB_BLOCKS] blocks of [COMB_POINTS] entries
    ([src/precomputed_ecmult_gen.h:21]).
    See https://wuille.net/posts/secp256k1-tutorial/#327-scalar-multiplications-ecmult-ecmult_gen-ecmult_const *)
Definition gen_prec_words : option (list (list (list Z))) :=
  match decode_storage_table
      (Z.to_nat (gen_table_blocks * gen_table_points))
      (gvar_init v_secp256k1_ecmult_gen_prec_table) with
  | Some entries =>
      rows_exact (Z.to_nat gen_table_blocks) (Z.to_nat gen_table_points) entries
  | None => None
  end.

(* ================================================================= *)
(** ** Shape proof targets. *)

(** [secp256k1_pre_g] has [ECMULT_TABLE_SIZE(WINDOW_G)] entries.
    See https://wuille.net/posts/secp256k1-tutorial/#327-scalar-multiplications-ecmult-ecmult_gen-ecmult_const *)
Definition pre_g_words_length : Prop :=
  match pre_g_words with
  | Some words => Zlength words = pre_g_table_len
  | None => False
  end.

(** Every [secp256k1_pre_g] entry is eight [uint64_t]s.
    See https://wuille.net/posts/secp256k1-tutorial/#326-group-group-operations-on-the-secp256k1-curve-group *)
Definition pre_g_words_shape : Prop :=
  match pre_g_words with
  | Some words => Forall gest_wf words
  | None => False
  end.

(** [secp256k1_pre_g_128] has the same length as [secp256k1_pre_g].
    See https://wuille.net/posts/secp256k1-tutorial/#327-scalar-multiplications-ecmult-ecmult_gen-ecmult_const *)
Definition pre_g_128_words_length : Prop :=
  match pre_g_128_words with
  | Some words => Zlength words = pre_g_table_len
  | None => False
  end.

(** Every [secp256k1_pre_g_128] entry is eight [uint64_t]s.
    See https://wuille.net/posts/secp256k1-tutorial/#326-group-group-operations-on-the-secp256k1-curve-group *)
Definition pre_g_128_words_shape : Prop :=
  match pre_g_128_words with
  | Some words => Forall gest_wf words
  | None => False
  end.

(** The comb table has one block per [COMB_BLOCKS].
    See https://wuille.net/posts/secp256k1-tutorial/#327-scalar-multiplications-ecmult-ecmult_gen-ecmult_const *)
Definition gen_prec_words_length : Prop :=
  match gen_prec_words with
  | Some blocks => Zlength blocks = gen_table_blocks
  | None => False
  end.

(** Every comb block holds [COMB_POINTS] entries of eight [uint64_t]s.
    See https://wuille.net/posts/secp256k1-tutorial/#327-scalar-multiplications-ecmult-ecmult_gen-ecmult_const *)
Definition gen_prec_words_shape : Prop :=
  match gen_prec_words with
  | Some blocks => Forall gen_block_wf blocks
  | None => False
  end.

(* ================================================================= *)
(** ** Mathematical characterisation proof targets. *)

(** Entry [i] of [secp256k1_pre_g] is [(2i+1) * G] -- the table is built by
    starting at [G] and repeatedly adding [2G]
    ([src/ecmult_compute_table_impl.h:16-33]).
    See https://wuille.net/posts/secp256k1-tutorial/#231-the-secp256k1-generator *)
Definition pre_g_words_spec : Prop :=
  match pre_g_words with
  | Some words => forall i : Z,
      0 <= i < pre_g_table_len ->
      gest_denote (gest_znth words i) = smul (2 * i + 1) G
  | None => False
  end.

(** Entry [i] of [secp256k1_pre_g_128] is [(2i+1) * 2^128 * G] -- the same
    construction started from [G] doubled 128 times
    ([src/ecmult_compute_table_impl.h:36-46]).
    See https://wuille.net/posts/secp256k1-tutorial/#231-the-secp256k1-generator *)
Definition pre_g_128_words_spec : Prop :=
  match pre_g_128_words with
  | Some words => forall i : Z,
      0 <= i < pre_g_table_len ->
      gest_denote (gest_znth words i) = smul ((2 * i + 1) * 2 ^ 128) G
  | None => False
  end.

(** Entry [i] of comb block [b] is [gen_entry_offset b i] times [G/2]
    ([src/ecmult_gen_compute_table_impl.h:49-89]).
    See https://wuille.net/posts/secp256k1-tutorial/#327-scalar-multiplications-ecmult-ecmult_gen-ecmult_const *)
Definition gen_prec_words_spec : Prop :=
  match gen_prec_words with
  | Some blocks => forall b i : Z,
      0 <= b < gen_table_blocks ->
      0 <= i < gen_table_points ->
      gest_denote (gest_znth (block_znth blocks b) i)
        = smul (gen_entry_offset b i * gen_half) G
  | None => False
  end.
