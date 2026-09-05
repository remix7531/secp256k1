(** * model.ecmult: wNAF recoding and the single-point Strauss double multiply. *)
(** Copyright (C) 2026 remix7531
    SPDX-License-Identifier: MIT *)

(** The trust boundary for the [ecmult] subsystem: what [secp256k1_ecmult]
    computes, written on [model.group]'s [Point] and plain integers.

    SCOPE -- THE SINGLE-POINT STRAUSS PATH ONLY.  [secp256k1_ecmult_multi_var],
    the pippenger algorithm, the batching heuristics and every scratch-space
    function are outside this extraction (see [schnorr-manifest-excluded.tsv])
    and deliberately have no model here.  [secp256k1_ecmult_strauss_wnaf] is
    reached only from [secp256k1_ecmult] ([src/ecmult_impl.h:364-374]), which
    always passes [num = 1], so the model has one point and one [na], never a
    list of them.

    TABLES ARE A PERFORMANCE DEVICE, NOT A SPECIFICATION.  The C reaches [k*A]
    through a table of odd multiples plus a signed window lookup; the model
    says [smul k a] and PROVES the lookup agrees ([table_get_odd_multiples]).
    That is also the only way [strauss] is executable at all: materialising
    the [2^13]-entry [G] table costs far more than the whole ladder.  The two
    GLOBAL precomputed tables ([secp256k1_pre_g], [secp256k1_pre_g_128]) are
    trusted constants owned by [model.tables]; here they appear only as the
    values they hold -- the odd multiples of [G] and of [G_128 = 2^128 * G].

    JACOBIAN COORDINATES, Z-RATIOS AND THE ISOMORPHISM TRICK ARE ABSENT for the
    same reason they are absent from [model.group]: the [z] denominators the C
    carries through [secp256k1_ecmult_odd_multiples_table] and
    [secp256k1_ge_table_set_globalz] are one encoding of a value this file
    names directly.  They are a [contract/ecmult] concern.

    COST.  Everything here reduces under [vm_compute], but a [padd] /
    [pdouble] needs a field inversion, which is one 256-bit [pow_mod] over
    Coq's bignum [Z] (see [model.tests_group]'s own COST note).  Recoding
    ([wnaf], [wnaf_eval], [strauss_rows], [scalar_signed]) is pure [Z] and
    free.  A [strauss] call is not: [strauss_rung]'s body mentions [G_128],
    and [vm_compute] is call by value, so ANY call that builds at least one
    rung realises [G_128] -- 128 [pdouble]s, each a field inversion --
    whatever its digits are.  MEASURED: [strauss G199 1 0 0 0], the cheapest
    possible non-degenerate call (one row, one nonzero digit), costs about
    390 seconds; only the all-zero-digit case [strauss _ 0 0 0 0], which
    builds no rung at all, is free.  Every ladder known-answer test therefore
    lives in [model/tests_slow_ecmult.v] and never in [model/tests_ecmult.v]
    -- that file's header states the same measurement from the other side --
    and [strauss_gen] below is what lets such a test substitute a cheap
    stand-in for [G_128].

    BRANCHES THE MODEL FOLDS.  Two C branches have no counterpart below
    because each is value-equivalent to a case the model already covers.  The
    equivalence is the load-bearing part, so it is written out here for the
    [contract/ecmult] funspec author to discharge deliberately rather than
    discover:
    - [src/ecmult_impl.h:269-271]'s [if (secp256k1_scalar_is_zero(&na[np])
      || secp256k1_gej_is_infinity(&a[np])) continue;], which sets [no = 0]
      and drops the whole [A] stream, including its length from the [bits]
      maximum.  Equivalent to [na_1 = na_lam = 0]
      here: [wnaf 0 w] is the empty list, so [strauss_rows] takes no row from
      it, and a row it did contribute would add [smul 0 _ = PInf], which
      [padd _ PInf = a] absorbs -- [model.group_law]'s [smul_0] (definitional)
      and [padd_PInf_r] (one case split on the point), both [Qed] in
      [model/group_law.v], neither an appeal to the Admitted group law.
    - [src/ecmult_impl.h:319]'s [if (ng)] NULL-pointer arm, documented at
      [src/ecmult.h:45] ("passing NULL as ng is equivalent to the zero
      scalar").  Equivalent to [ng_1 = ng_128 = 0] here, by the same
      argument.

    SIGN CONVENTION.  A [secp256k1_scalar] is an integer in [[0, n)], but
    [secp256k1_ecmult_wnaf] recodes its SIGNED representative: its prologue
    tests bit 255 and, when set, negates the scalar and flips every digit sign.
    [scalar_signed] below is that prologue, and [wnaf] takes the signed integer
    it produces. *)

From Stdlib Require Import ZArith.
From Stdlib Require Import Lia.
From Stdlib Require Import List.
Import ListNotations.

Require Import secp256k1.model.group.

Open Scope Z_scope.

(* ================================================================= *)
(** ** Window geometry -- [window_a] / [window_g] / [ecmult_table_size].
    The three pinned numbers the extraction is built with; every length below
    is derived from them, so a reviewer checks three literals against the C
    headers rather than a table of derived sizes. *)

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
    ([contract/ecmult]) and not part of this list.
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
    ([:144-152]) -- the storage decoding itself is [model.tables]' [gest_denote].
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
    is what lets [strauss] below say [smul] where the C says "load from
    [pre_a]", and what a [contract/ecmult] funspec for
    [secp256k1_ecmult_table_get_ge] will be stated against.
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

(** The recoding is exact: the digits sum back to the input.  STATED AND
    [Admitted] ([audit/scaffold.txt]).
    INTENDED DISCHARGE ROUTE: strong induction on [fuel] with the invariant
    [wnaf_eval (wnaf_go f a w) = a] for [Z.abs a < 2 ^ Z.of_nat f], using
    [Z.div_exact] on the two [(a - d) / 2] and [a / 2] steps ([a - d] is even
    because [a] and [d] are both odd) and [Z.mod_pos_bound] for the digit
    range; the negative case adds [wnaf_eval (map Z.opp ds) = - wnaf_eval ds],
    a one-line list induction.
    See https://wuille.net/posts/secp256k1-tutorial/#222-scalar-multiplication *)
Lemma wnaf_eval_correct : forall (a w : Z),
  2 <= w <= 31 ->
  - 2 ^ 256 < a < 2 ^ 256 ->
  wnaf_eval (wnaf a w) = a.
Proof.
  (* OUTSTANDING: awaits the fuel induction sketched above. *)
Admitted.

(** [wnaf]'s output really satisfies [wnaf_wf]: the C's FIRST documented wNAF
    guarantee ([src/ecmult_impl.h:156], "each wnaf[i] is either 0, or an odd
    integer between -(1<<(w-1) - 1) and (1<<(w-1) - 1)").  This is the link
    between [secp256k1_ecmult_wnaf]'s result and
    [secp256k1_ecmult_table_get_ge]'s precondition: [table_get_odd_multiples]
    demands [table_index_wf w n] of the index, and this lemma -- with
    [wnaf_digit_wf]'s definition -- is the only thing that supplies it, so
    [contract/ecmult]'s funspec for [secp256k1_ecmult_wnaf] and the
    [secp256k1_ecmult_strauss_wnaf] body proof both rest on it.  No range
    hypothesis on [a] is needed: a truncated (fuel-exhausted) list is still
    well formed digit by digit.
    STATED AND [Admitted] ([audit/scaffold.txt]).
    INTENDED DISCHARGE ROUTE: induction on [fuel] for the auxiliary
    [Forall (wnaf_digit_wf w) (wnaf_go fuel a w)], generalised in [a].  In the
    odd branch, [r = a mod 2^w] is odd because [2^w] is even
    ([Z.mod_pow2_bits_low] at bit [0], then [Z.bit0_odd]), which gives both
    conjuncts: the digit is odd in either arm ([r], or [r - 2^w] with [2^w]
    even), and [r = 2^(w-1)] -- the one value that would make the borrowed
    digit [-2^(w-1)], out of range -- is unreachable because [2^(w-1)] is
    even for [w >= 2].  The negative case adds a one-line list induction for
    [Forall (wnaf_digit_wf w) (map Z.opp ds)], using [Z.odd_opp] and the
    symmetry of the range.  Machine-checked true at the boundary set by
    [vm_compute], and over all of [[0, 2^16)] at both windows by
    [model/tests_slow_ecmult.v]'s [chk_wnaf_exhaustive_window_a] /
    [_window_g].
    See https://wuille.net/posts/secp256k1-tutorial/#222-scalar-multiplication *)
Lemma wnaf_wf_wnaf : forall (a w : Z),
  2 <= w <= 31 ->
  wnaf_wf w (wnaf a w).
Proof.
  (* OUTSTANDING: awaits the fuel induction sketched above. *)
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

(** One rung of the ladder: double, then add each of the four digits' multiples
    (a [0] digit contributes [PInf], which [padd] absorbs -- exactly the C's
    [if (n = wnaf[i])] skip).  Mirrors the loop body at
    [src/ecmult_impl.h:336-357]; where the C loads from a table this says
    [smul], which [table_get_odd_multiples] shows is the same point.  The two
    generator-side points are ARGUMENTS: the C hard-codes [secp256k1_pre_g] /
    [secp256k1_pre_g_128], and [strauss] below pins [g] / [g128] to [G] /
    [G_128] to match, but a known-answer test can then substitute a cheap
    stand-in for [G_128] instead of paying its 128 [pdouble]s on every call
    (see the COST note in the file header).
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
    whose contracts ([contract/scalar]) specify them by the relation above and
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

(** The ladder at the generator points the C actually uses.  This is the
    definition [contract/ecmult] and [verif/ecmult] are written against;
    [strauss_gen] exists only so that a known-answer test can run the same
    ladder against a cheap stand-in for [G_128] (see the COST note in the
    file header), and no funspec should mention it.
    See https://wuille.net/posts/secp256k1-tutorial/#327-scalar-multiplications-ecmult-ecmult_gen-ecmult_const *)
Definition strauss (a : Point) (na_1 na_lam ng_1 ng_128 : Z) : Point :=
  strauss_gen a G G_128 na_1 na_lam ng_1 ng_128.

(** What [secp256k1_ecmult] means: [na*A + ng*G] ([src/ecmult.h:43-46]).  This
    is the postcondition [contract/ecmult]'s funspec states; [strauss] is how
    the C gets there.
    See https://wuille.net/posts/secp256k1-tutorial/#327-scalar-multiplications-ecmult-ecmult_gen-ecmult_const *)
Definition ecmult_model (a : Point) (na ng : Z) : Point :=
  padd (smul na a) (smul ng G).

(** The ladder computes the double multiply.  The two split hypotheses mirror
    the postconditions of [spec_secp256k1_scalar_split_lambda] and
    [spec_secp256k1_scalar_split_128] ([contract/scalar]), with the right-hand
    side written as [na mod secp256k1_N] so that [na] itself need not be
    reduced -- for a scalar in [[0, n)] the two agree.
    STATED AND [Admitted] ([audit/scaffold.txt]).
    INTENDED DISCHARGE ROUTE: [wnaf_eval_correct] turns each digit list back
    into its integer; [model.group_law]'s [smul_add] / [smul_mul] and a rung
    induction collapse [fold_left] to [smul] of those integers;
    [model.group_law]'s [lambda_endo] replaces [pmul_lambda a] by
    [smul secp256k1_lambda a]; and [model.group_order]'s [cofactor_one] is what
    allows the two [mod secp256k1_N] hypotheses to be dropped.  The C-side body
    proof of [secp256k1_ecmult_strauss_wnaf] will want its own loop-invariant
    file next to it -- the rung induction above is that invariant.
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
  (* OUTSTANDING: awaits the rung induction sketched above. *)
Admitted.
