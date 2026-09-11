(** * theory.ecmult.ecmult: wNAF recoding and the single-point Strauss double multiply. *)
(** Copyright (C) 2026 remix7531
    SPDX-License-Identifier: MIT *)

(** This model covers the single-point Strauss path of
    [secp256k1_ecmult], which passes [num = 1] to
    [secp256k1_ecmult_strauss_wnaf].

    Odd-multiple table lookups denote scalar multiplication through
    [table_get_odd_multiples]. [theory/ecmult/tables.v] decodes the production
    tables for [G] and [G_128]. Jacobian coordinates and shared denominators
    belong to the C representation, while this model uses affine points.

    Each affine addition or doubling performs field inversion. Under
    call-by-value evaluation, a nonempty [strauss] also evaluates [G_128].
    [strauss_gen] accepts the generator points as arguments.

    Skipping a zero scalar or an infinite input point drops the corresponding
    digit stream. A null [ng] pointer denotes a zero generator scalar.
    [scalar_signed] selects the signed representative used by the C wNAF
    prologue, which tests bit 255 and negates the scalar when that bit is set. *)

From Stdlib Require Import ZArith.
From Stdlib Require Import Lia.
From Stdlib Require Import List.
Import ListNotations.

Require secp256k1.specification.
Import specification.Math.
Import specification.Math.raw.

Open Scope Z_scope.

(* ================================================================= *)
(** ** Window geometry: [window_a], [window_g] and [ecmult_table_size].
    Table lengths are derived from the production window parameters. *)

(** The window used for the variable point [A] (the C's [WINDOW_A],
    [src/ecmult_impl.h:31]).
    See https://wuille.net/posts/secp256k1-tutorial/#327-scalar-multiplications-ecmult-ecmult_gen-ecmult_const *)
Definition window_a : Z := 5.

(** The window used for the generator [G] (the C's [WINDOW_G], which is
    [ECMULT_WINDOW_SIZE], defaulted to 15 at [src/ecmult.h:14-19] and not
    overridden by this build, and bound to [WINDOW_G] at
    [src/precomputed_ecmult.h:31]).
    See https://wuille.net/posts/secp256k1-tutorial/#327-scalar-multiplications-ecmult-ecmult_gen-ecmult_const *)
Definition window_g : Z := 15.

(** Entries in a window-[w] table of odd multiples: [2^(w-2)], the C's
    [ECMULT_TABLE_SIZE(w)] ([src/ecmult.h:41]).
    See https://wuille.net/posts/secp256k1-tutorial/#327-scalar-multiplications-ecmult-ecmult_gen-ecmult_const *)
Definition ecmult_table_size (w : Z) : nat := Z.to_nat (2 ^ (w - 2)).

(* ================================================================= *)
(** ** Odd-multiples tables and the window lookup -- [odd_multiples] /
    [table_index_wf] / [table_get] / [table_get_lambda]. *)

(** The odd multiples [[1*a, 3*a, ..., (2*k-1)*a]].  Specifies the VALUES
    [secp256k1_ecmult_odd_multiples_table] ([src/ecmult_impl.h:72-114]) leaves
    in [pre_a]; that C function additionally records the omitted [z]
    coordinates as the ratio array [zr], which is a representation concern
    ([vst/ecmult/contract.v]) and not part of this list.
    See https://wuille.net/posts/secp256k1-tutorial/#327-scalar-multiplications-ecmult-ecmult_gen-ecmult_const *)
Definition odd_multiples (k : nat) (a : Point) : list Point :=
  map (fun i => smul (2 * Z.of_nat i + 1) a) (seq 0 k).

(** The precondition a window-[w] table index must satisfy: odd, and within
    [+/- (2^(w-1) - 1)].  Specifies [secp256k1_ecmult_table_verify]
    ([src/ecmult_impl.h:116-122]), whose whole body is those two
    [VERIFY_CHECK]s -- so under the VERIFY-off extraction it is a no-op whose
    contract is exactly this predicate, carried by its callers.
    See https://wuille.net/posts/secp256k1-tutorial/#327-scalar-multiplications-ecmult-ecmult_gen-ecmult_const *)
Definition table_index_wf (w n : Z) : Prop :=
  Z.odd n = true /\ - (2 ^ (w - 1) - 1) <= n <= 2 ^ (w - 1) - 1.

(** Signed window lookup: entry [(n-1)/2] for a positive [n], and the negation
    of entry [(-n-1)/2] for a negative one.  Specifies
    [secp256k1_ecmult_table_get_ge] ([src/ecmult_impl.h:124-132]) and, on a
    table read out of [secp256k1_ge_storage], [_table_get_ge_storage]
    ([:144-152]) -- the storage decoding itself is [theory/ecmult/tables.v]' [gest_denote].
    See https://wuille.net/posts/secp256k1-tutorial/#327-scalar-multiplications-ecmult-ecmult_gen-ecmult_const *)
Definition table_get (pre : list Point) (n : Z) : Point :=
  if 0 <? n
  then nth (Z.to_nat ((n - 1) / 2)) pre PInf
  else pneg (nth (Z.to_nat ((- n - 1) / 2)) pre PInf).

(** The same lookup through the GLV endomorphism.  Specifies
    [secp256k1_ecmult_table_get_ge_lambda] ([src/ecmult_impl.h:134-142]), which
    pairs the [beta]-multiplied x coordinate the caller precomputed in [aux]
    with the table's own y -- i.e. [pmul_lambda] of the ordinary lookup.
    See https://wuille.net/posts/secp256k1-tutorial/#24-the-glv-endomorphism *)
Definition table_get_lambda (pre : list Point) (n : Z) : Point :=
  pmul_lambda (table_get pre n).

(** Reading entry [i] of an odd-multiples table.
    See https://wuille.net/posts/secp256k1-tutorial/#327-scalar-multiplications-ecmult-ecmult_gen-ecmult_const *)
Lemma nth_odd_multiples : forall (k i : nat) (a : Point),
  (i < k)%nat ->
  nth i (odd_multiples k a) PInf = smul (2 * Z.of_nat i + 1) a.
Proof.
  intros k i a Hi.
  unfold odd_multiples.
  transitivity ((fun j : nat => smul (2 * Z.of_nat j + 1) a) (nth i (seq 0 k) 0%nat)).
  - (* the default is irrelevant: i is below the table length *)
    rewrite <- (map_nth (fun j : nat => smul (2 * Z.of_nat j + 1) a)
                        (seq 0 k) 0%nat i).
    apply nth_indep.
    rewrite length_map, length_seq.
    exact Hi.
  - (* entry i of [seq 0 k] is i itself *)
    rewrite seq_nth by exact Hi.
    reflexivity.
Qed.

(** Negating a negative multiple is negating the scalar.  Definitional: [smul]
    of a negative integer is already [pneg] of the positive one (there is no
    appeal to [pneg] being an involution, which holds only propositionally).
    See https://wuille.net/posts/secp256k1-tutorial/#222-scalar-multiplication *)
Lemma smul_neg_pneg : forall (k : Z) (a : Point),
  k < 0 -> pneg (smul (- k) a) = smul k a.
Proof.
  intros k a Hk.
  destruct k as [| p | p]; try lia.
  reflexivity.
Qed.

(** The window lookup on an odd-multiples table IS scalar multiplication: for
    any index the C's [VERIFY_CHECK]s admit, [table_get] returns [n*a].  This
    lets [strauss] use [smul] for a C lookup from [pre_a].
    See https://wuille.net/posts/secp256k1-tutorial/#327-scalar-multiplications-ecmult-ecmult_gen-ecmult_const *)
Lemma table_get_odd_multiples : forall (w n : Z) (a : Point),
  2 <= w ->
  table_index_wf w n ->
  table_get (odd_multiples (ecmult_table_size w) a) n = smul n a.
Proof.
  intros w n a Hw [Hodd Hrange].
  assert (Hpow : 2 ^ (w - 1) = 2 * 2 ^ (w - 2)).
  { replace (w - 1) with (Z.succ (w - 2)) by lia.
    rewrite Z.pow_succ_r by lia.
    reflexivity. }
  apply Z.odd_spec in Hodd.
  destruct Hodd as [m Hm].
  subst n.
  unfold table_get, ecmult_table_size.
  destruct (Z.ltb_spec 0 (2 * m + 1)) as [Hpos | Hneg].
  - (* branch: positive index -- entry (n-1)/2 = m *)
    replace (2 * m + 1 - 1) with (m * 2) by lia.
    rewrite Z.div_mul by lia.
    assert (Hlt : (Z.to_nat m < Z.to_nat (2 ^ (w - 2)))%nat).
    { apply Z2Nat.inj_lt; lia. }
    rewrite nth_odd_multiples by exact Hlt.
    rewrite Z2Nat.id by lia.
    reflexivity.
  - (* branch: negative index -- entry (-n-1)/2 = -m-1, then negate *)
    replace (- (2 * m + 1) - 1) with ((- m - 1) * 2) by lia.
    rewrite Z.div_mul by lia.
    assert (Hlt : (Z.to_nat (- m - 1) < Z.to_nat (2 ^ (w - 2)))%nat).
    { apply Z2Nat.inj_lt; lia. }
    rewrite nth_odd_multiples by exact Hlt.
    rewrite Z2Nat.id by lia.
    replace (2 * (- m - 1) + 1) with (- (2 * m + 1)) by lia.
    apply smul_neg_pneg.
    lia.
Qed.

(* ================================================================= *)
(** ** wNAF recoding -- [scalar_signed] / [wnaf_digit] / [wnaf] / [wnaf_eval].

    The width-[w] non-adjacent form: a little-endian list of digits, each
    either [0] or odd with absolute value below [2^(w-1)], summing to the input
    under [wnaf_eval].  The list stops at the last nonzero digit, so its
    [length] is exactly the [last_set_bit + 1] the C returns. *)

(** The signed representative of a scalar: [a] itself below [2^255], and
    [a - n] above.  Specifies the sign prologue of [secp256k1_ecmult_wnaf]
    ([src/ecmult_impl.h:177-181]), which tests bit 255 and, when it is set,
    replaces the scalar by its negation and every digit by its opposite.
    See https://wuille.net/posts/secp256k1-tutorial/#232-the-scalar-field *)
Definition scalar_signed (a : Z) : Z :=
  if 2 ^ 255 <=? a then a - secp256k1_N else a.

(** One recoding digit: the representative of [a] modulo [2^w] taken in
    [(-2^(w-1), 2^(w-1))].  Specifies the [word - (carry << w)] step of
    [secp256k1_ecmult_wnaf] ([src/ecmult_impl.h:197-200]), where the borrowed
    [carry] bit is the top bit of the window.
    See https://wuille.net/posts/secp256k1-tutorial/#222-scalar-multiplication *)
Definition wnaf_digit (a w : Z) : Z :=
  let m := 2 ^ w in
  let r := a mod m in
  if r <? 2 ^ (w - 1) then r else r - m.

(** The recoding loop: emit a digit for an odd remainder, a [0] for an even
    one, and stop as soon as nothing is left.  [fuel] bounds the recursion;
    [wnaf] instantiates it well above what any 256-bit input consumes.  Value
    first, then width, as in [wnaf] and [wnaf_digit].
    See https://wuille.net/posts/secp256k1-tutorial/#222-scalar-multiplication *)
Fixpoint wnaf_go (fuel : nat) (a w : Z) : list Z :=
  match fuel with
  | O => []
  | S fuel' =>
      if Z.eqb a 0 then []
      else if Z.odd a
           then let d := wnaf_digit a w in d :: wnaf_go fuel' ((a - d) / 2) w
           else 0 :: wnaf_go fuel' (a / 2) w
  end.

(** Recursion budget for [wnaf].  Each step strictly shrinks [Z.abs a] while
    it exceeds [2 ^ (w-1)], and terminates within two steps once it does, so a
    256-bit input costs at most about [256 + w] steps; the loop also stops on
    its own at [0].  [300] is slack for every [w <= 31], not a limit.
    See https://wuille.net/posts/secp256k1-tutorial/#222-scalar-multiplication *)
Definition wnaf_fuel : nat := 300%nat.

(** The width-[w] NAF of an integer, little-endian.  Specifies
    [secp256k1_ecmult_wnaf] ([src/ecmult_impl.h:161-220]) -- and
    [secp256k1_ecmult_wnaf_small] ([:223-235]), which is the same function
    narrowed to [int8_t] -- applied to [scalar_signed] of the C's scalar
    argument.  The negative case mirrors the C literally: recode [-a] and
    multiply every digit by [sign = -1], rather than relying on the recursion
    being sign-symmetric.
    See https://wuille.net/posts/secp256k1-tutorial/#222-scalar-multiplication *)
Definition wnaf (a w : Z) : list Z :=
  if a <? 0
  then map Z.opp (wnaf_go wnaf_fuel (- a) w)
  else wnaf_go wnaf_fuel a w.

(** The value a digit list denotes: [sum_i d_i * 2^i], written as a Horner
    fold so it reduces under [vm_compute] without any [pow].
    See https://wuille.net/posts/secp256k1-tutorial/#222-scalar-multiplication *)
Fixpoint wnaf_eval (ds : list Z) : Z :=
  match ds with
  | [] => 0
  | d :: ds' => d + 2 * wnaf_eval ds'
  end.

(** A digit is well formed when it is [0] or a legal signed window index.  This
    is the per-digit half of the C's documented guarantee
    ([src/ecmult_impl.h:156]) -- and it is the half that bounds the TABLE
    SIZE, since [|d| < 2^(w-1)] is exactly what [table_index_wf] needs.  The
    other half ([:157]) -- that two nonzero digits are separated by at least
    [w-1] zeroes -- bounds only the NUMBER OF ADDITIONS the ladder performs,
    a performance property, and no correctness statement in this proof
    depends on it, so it is not modelled.
    See https://wuille.net/posts/secp256k1-tutorial/#222-scalar-multiplication *)
Definition wnaf_digit_wf (w d : Z) : Prop := d = 0 \/ table_index_wf w d.

(** Every digit of a list is well formed -- what a caller must know before
    handing a digit to [table_get].
    See https://wuille.net/posts/secp256k1-tutorial/#222-scalar-multiplication *)
Definition wnaf_wf (w : Z) (ds : list Z) : Prop := Forall (wnaf_digit_wf w) ds.

(** The recoded digits sum to the input.
    See https://wuille.net/posts/secp256k1-tutorial/#222-scalar-multiplication *)
Lemma wnaf_eval_correct : forall (a w : Z),
  2 <= w <= 31 ->
  - 2 ^ 256 < a < 2 ^ 256 ->
  wnaf_eval (wnaf a w) = a.
Proof.
Admitted.

(** Each nonzero wNAF digit is an odd signed window index, as required
    by [secp256k1_ecmult_table_get_ge]. No range hypothesis on [a] is
    needed because fuel exhaustion still leaves well-formed digits.
    See https://wuille.net/posts/secp256k1-tutorial/#222-scalar-multiplication *)
Lemma wnaf_wf_wnaf : forall (a w : Z),
  2 <= w <= 31 ->
  wnaf_wf w (wnaf a w).
Proof.
Admitted.

(* ================================================================= *)
(** ** The Strauss-Shamir ladder -- [G_128] / [strauss_rung] / [strauss_rows] /
    [strauss_gen] / [strauss] / [ecmult_model].

    One shared doubling chain, four interleaved digit streams: the two halves
    of the GLV split of [na] against [A] and [lambda*A], and the two halves of
    the [2^128] split of [ng] against [G] and [2^128 * G]. *)

(** [2^128 * G]: the base of the second generator table (the C's
    [secp256k1_pre_g_128] holds its odd multiples, [src/precompute_ecmult.c:71]).
    See https://wuille.net/posts/secp256k1-tutorial/#231-the-secp256k1-generator *)
Definition G_128 : Point := smul (2 ^ 128) G.

(** One rung doubles the accumulator and adds the four digit multiples.
    A zero digit contributes [PInf], matching the C loop's skip.
    [table_get_odd_multiples] relates C lookups to [smul]. The generator
    points are parameters, allowing evaluation without computing [G_128].
    See https://wuille.net/posts/secp256k1-tutorial/#327-scalar-multiplications-ecmult-ecmult_gen-ecmult_const *)
Definition strauss_rung (a g g128 : Point) (r : Point) (ds : Z * Z * Z * Z)
  : Point :=
  let '(d_1, d_lam, e_1, e_128) := ds in
  padd (padd (padd (padd (pdouble r) (smul d_1 a))
                   (smul d_lam (pmul_lambda a)))
             (smul e_1 g))
       (smul e_128 g128).

(** The four digit lists transposed into rungs, most significant first.  The
    number of rungs is the longest of the four lists, which is the C's [bits]
    ([src/ecmult_impl.h:280-285, 326-331]); a list that ran out contributes a
    [0] digit, which is the C's [i < bits_na_1] guard.
    See https://wuille.net/posts/secp256k1-tutorial/#327-scalar-multiplications-ecmult-ecmult_gen-ecmult_const *)
Definition strauss_rows (w_1 w_lam w_g1 w_g128 : list Z)
  : list (Z * Z * Z * Z) :=
  let bits := Nat.max (Nat.max (length w_1) (length w_lam))
                      (Nat.max (length w_g1) (length w_g128)) in
  rev (map (fun i => (nth i w_1 0, nth i w_lam 0, nth i w_g1 0, nth i w_g128 0))
           (seq 0 bits)).

(** The single-point Strauss double multiply over arbitrary generator points,
    as a function of the two scalar splits its caller performed:
    [na = na_1 + lambda * na_lam] and [ng = ng_1 + 2^128 * ng_128], each half
    a scalar in [[0, n)].  Specifies
    [secp256k1_ecmult_strauss_wnaf] ([src/ecmult_impl.h:251-362]) at [num = 1].
    The splits are arguments rather than computed here because the C obtains
    them from [secp256k1_scalar_split_lambda] and [secp256k1_scalar_split_128],
    whose contracts ([vst/scalar/contract.v]) specify them by the relation above and
    not as a function -- the model must not be more determined than the code.
    [strauss] just below is this function at [g = G] and [g128 = G_128].
    See https://wuille.net/posts/secp256k1-tutorial/#327-scalar-multiplications-ecmult-ecmult_gen-ecmult_const *)
Definition strauss_gen (a g g128 : Point) (na_1 na_lam ng_1 ng_128 : Z)
  : Point :=
  fold_left (strauss_rung a g g128)
            (strauss_rows (wnaf (scalar_signed na_1) window_a)
                          (wnaf (scalar_signed na_lam) window_a)
                          (wnaf (scalar_signed ng_1) window_g)
                          (wnaf (scalar_signed ng_128) window_g))
            PInf.

(** The ladder at the production generator points [G] and [G_128].
    See https://wuille.net/posts/secp256k1-tutorial/#327-scalar-multiplications-ecmult-ecmult_gen-ecmult_const *)
Definition strauss (a : Point) (na_1 na_lam ng_1 ng_128 : Z) : Point :=
  strauss_gen a G G_128 na_1 na_lam ng_1 ng_128.

(** [secp256k1_ecmult] computes [na*A + ng*G], as in [src/ecmult.h:43-46].
    [strauss] models the C algorithm.
    See https://wuille.net/posts/secp256k1-tutorial/#327-scalar-multiplications-ecmult-ecmult_gen-ecmult_const *)
Definition ecmult_model (a : Point) (na ng : Z) : Point :=
  padd (smul na a) (smul ng G).

(** The ladder computes the double multiply.  The two split hypotheses mirror
    the postconditions of [spec_secp256k1_scalar_split_lambda] and
    [spec_secp256k1_scalar_split_128] ([vst/scalar/contract.v]), with the right-hand
    side written as [na mod secp256k1_N] so that [na] itself need not be
    reduced -- for a scalar in [[0, n)] the two agree.
    See https://wuille.net/posts/secp256k1-tutorial/#327-scalar-multiplications-ecmult-ecmult_gen-ecmult_const *)
Lemma strauss_correct :
  forall (a : Point) (na na_1 na_lam ng ng_1 ng_128 : Z),
    on_curve a ->
    0 <= na_1 < secp256k1_N ->
    0 <= na_lam < secp256k1_N ->
    0 <= ng_1 < secp256k1_N ->
    0 <= ng_128 < secp256k1_N ->
    (na_1 + secp256k1_lambda * na_lam) mod secp256k1_N = na mod secp256k1_N ->
    (ng_1 + ng_128 * 2 ^ 128) mod secp256k1_N = ng mod secp256k1_N ->
    strauss a na_1 na_lam ng_1 ng_128 = ecmult_model a na ng.
Proof.
Admitted.
