(** * model.field: pure functional model of secp256k1 field elements (mod p). *)
(** Copyright (C) 2026 remix7531
    SPDX-License-Identifier: MIT *)

(** The trust boundary for the field subsystem: a field element is a residue in
    [[0, p)], nothing more.  The lazy-reduction "magnitude" of the C
    representation (how far un-normalized limbs may exceed [2^52]) is a *contract*
    concern -- see [theory/field/field_bits] and [contract/field] -- and deliberately
    never appears in this value. *)

Require Import ZArith.
Require Import Lia.
Require Import Coq.ZArith.Znumtheory.
Require Export secp256k1.model.types.
Require Import secp256k1.theory.bytes.
Require Import secp256k1.theory.field.field_bits.
Require Import secp256k1.theory.primality.p.

Open Scope Z_scope.

(** Deterministic obligation preprocessing: just [intros].  The default
    [program_simpl] auto-solver spins on the [(N - a) mod N] obligation
    shapes now that floyd (which used to override it) is no longer loaded. *)
Local Obligation Tactic := intros.

(* ================================================================= *)
(** ** Field operations -- [fe_add] = [(a + b) mod p].
    ([Fe] lives in [model.types]; the prime [secp256k1_P] in [model.constants].) *)

(** Modular field addition: [a + b mod p]. *)
Program Definition fe_add (a b : Fe) : Fe :=
  mkFe ((a + b) mod secp256k1_P) _.
Next Obligation.
  apply Z.mod_pos_bound.
  pose proof secp256k1_P_range.
  lia.
Qed.

(** The field zero. *)
Program Definition fe_zero : Fe := mkFe 0 _.
Next Obligation.
  pose proof secp256k1_P_range.
  lia.
Qed.

(* ================================================================= *)
(** ** More field arithmetic -- [fe_mul] / [fe_sqr] / [fe_negate] /
    [fe_add_int] / [fe_mul_int] / [fe_half].

    Every one of these is "the obvious [Z] operation, then reduce mod p" --
    the C's magnitude/normalization bookkeeping ([src/field.h]'s doc comments
    on each function) is entirely a representation concern (see the file
    header) and never changes which residue is meant. *)

(** Modular field multiplication: [a * b mod p].  Specifies [secp256k1_fe_mul]
    (via [secp256k1_fe_impl_mul] / [secp256k1_fe_mul_inner]).
    See https://wuille.net/posts/secp256k1-tutorial/#324-field-finite-field-element-representation *)
Program Definition fe_mul (a b : Fe) : Fe :=
  mkFe ((a * b) mod secp256k1_P) _.
Next Obligation.
  apply Z.mod_pos_bound.
  pose proof secp256k1_P_range.
  lia.
Qed.

(** Modular field squaring: [a * a mod p].  Specifies [secp256k1_fe_sqr].
    See https://wuille.net/posts/secp256k1-tutorial/#324-field-finite-field-element-representation *)
Program Definition fe_sqr (a : Fe) : Fe :=
  mkFe ((a * a) mod secp256k1_P) _.
Next Obligation.
  apply Z.mod_pos_bound.
  pose proof secp256k1_P_range.
  lia.
Qed.

(** Modular field negation: [(p - a) mod p].  Specifies
    [secp256k1_fe_negate_unchecked] (the C's magnitude parameter [m] only
    bounds the *input*'s representation, so it plays no role at the value
    level).
    See https://wuille.net/posts/secp256k1-tutorial/#324-field-finite-field-element-representation *)
Program Definition fe_negate (a : Fe) : Fe :=
  mkFe ((secp256k1_P - a) mod secp256k1_P) _.
Next Obligation.
  apply Z.mod_pos_bound.
  pose proof secp256k1_P_range.
  lia.
Qed.

(** Add a (small, per the C's [[0,0x7FFF]] doc bound -- not needed at this
    level) integer: [(a + k) mod p].  Specifies [secp256k1_fe_add_int] (via
    [secp256k1_fe_impl_add_int]).
    See https://wuille.net/posts/secp256k1-tutorial/#324-field-finite-field-element-representation *)
Program Definition fe_add_int (a : Fe) (k : Z) : Fe :=
  mkFe ((a + k) mod secp256k1_P) _.
Next Obligation.
  apply Z.mod_pos_bound.
  pose proof secp256k1_P_range.
  lia.
Qed.

(** Multiply by a (small, per the C's [[0,32]] doc bound -- likewise not
    needed here) integer: [(a * k) mod p].  Specifies [secp256k1_fe_mul_int]
    (via [secp256k1_fe_impl_mul_int_unchecked]).
    See https://wuille.net/posts/secp256k1-tutorial/#324-field-finite-field-element-representation *)
Program Definition fe_mul_int (a : Fe) (k : Z) : Fe :=
  mkFe ((a * k) mod secp256k1_P) _.
Next Obligation.
  apply Z.mod_pos_bound.
  pose proof secp256k1_P_range.
  lia.
Qed.

(** Modular halving: [a * inv2 mod p], where [inv2 = (p+1)/2 = 1/2 mod p]
    ([p] is odd, mirroring [model.scalar]'s [scalar_half]).  Specifies
    [secp256k1_fe_half] (via [secp256k1_fe_impl_half]).
    See https://wuille.net/posts/secp256k1-tutorial/#324-field-finite-field-element-representation *)
Program Definition fe_half (a : Fe) : Fe :=
  mkFe ((a * ((secp256k1_P + 1) / 2)) mod secp256k1_P) _.
Next Obligation.
  apply Z.mod_pos_bound.
  pose proof secp256k1_P_range.
  lia.
Qed.

(* ================================================================= *)
(** ** Distinguished elements and predicates -- [fe_one] / [fe_is_zero] /
    [fe_is_odd] / [fe_cmp]. *)

(** The field one. *)
Program Definition fe_one : Fe := mkFe 1 _.
Next Obligation.
  (* [1 < secp256k1_P] is a magnitude fact, not mere positivity -- unfold
     rather than [pose proof secp256k1_P_range] (which only gives [> 0]). *)
  unfold secp256k1_P.
  lia.
Qed.

(** Is [a] the zero residue?  Specifies [secp256k1_fe_is_zero] and (together
    with [fe_add] / [fe_negate]) [secp256k1_fe_equal] /
    [secp256k1_fe_normalizes_to_zero{,_var}], which are all "does this
    represent 0" under a different representation-level guise.
    See https://wuille.net/posts/secp256k1-tutorial/#324-field-finite-field-element-representation *)
Definition fe_is_zero (a : Fe) : bool := Z.eqb (fe_val a) 0.

(** Is [a] odd, as an integer in [[0,p)]?  Specifies [secp256k1_fe_is_odd].
    See https://wuille.net/posts/secp256k1-tutorial/#324-field-finite-field-element-representation *)
Definition fe_is_odd (a : Fe) : bool := Z.odd (fe_val a).

(** Three-way compare of the represented integers in [[0,p)]: [1] if
    [a > b], [-1] if [a < b], [0] if equal -- the same convention as the C's
    [int] return.  Specifies [secp256k1_fe_cmp_var]; note this C function is
    dead code in THIS extraction (only ECDSA/recovery callers reach it, per
    [schnorr-manifest-excluded.tsv]), but Part 5 asks for the model anyway --
    it costs nothing and keeps the model a complete mirror of [field.h].
    See https://wuille.net/posts/secp256k1-tutorial/#324-field-finite-field-element-representation *)
Definition fe_cmp (a b : Fe) : Z :=
  if Z.eqb (fe_val a) (fe_val b) then 0
  else if Z.ltb (fe_val a) (fe_val b) then -1
  else 1.

(* ================================================================= *)
(** ** Field prime primality -- [secp256k1_P_prime].

    Lives here, not in [model.constants] (which owns [secp256k1_N_prime]):
    [secp256k1_P] itself is declared in [model.constants], but the
    certificate route for it is field-subsystem-specific
    ([theory.primality.p], parallel to [theory.primality.n] for [N]), and
    this module is what actually needs the fact (Fermat's little theorem for
    [fe_inv] below; Euler's criterion, via [fe_pow], for [fe_sqrt]). *)

(** [p] is prime, via the coqprime Pocklington certificate in
    [theory.primality.p] ([secp256k1_P_prime_cert]).  Not a project [Axiom]:
    see that file's TRUST NOTE -- [Print Assumptions secp256k1_P_prime] closes
    over coqprime's own [Uint63Axioms.*] / [PrimInt63.*] cone, whitelisted as
    foundational (toolchain) trust, exactly like [secp256k1_N_prime]
    ([model.constants]) does for [N].
    See https://wuille.net/posts/secp256k1-tutorial/#21-the-coordinate-field *)
Lemma secp256k1_P_prime : prime secp256k1_P.
Proof.
  exact secp256k1_P_prime_cert.
Qed.

(* ================================================================= *)
(** ** Exponentiation, inversion, square root -- [fe_pow] / [fe_inv] /
    [fe_sqrt].

    All three route through [theory.field.field_bits]'s [pow_mod]: a
    square-and-multiply exponentiation that reduces mod [p] at every step, so
    [vm_compute] stays fast even for [fe_sqrt]'s ~254-bit exponent (the KAT
    stage needs this -- see the module header). *)

(** Modular exponentiation: [a ^ e mod p], for any [e : Z] (a negative [e] is
    unused by the C surface and maps to [0]; see [pow_mod]).  Not itself one
    C function -- it is the shared engine [fe_inv] (Fermat's little theorem,
    [a^(p-2)]) and [fe_sqrt] (the [(p+1)/4]-power formula) are built from,
    mirroring [secp256k1_fe_sqrt]'s own addition-chain implementation
    ([src/field_impl.h]).
    See https://wuille.net/posts/secp256k1-tutorial/#21-the-coordinate-field *)
Program Definition fe_pow (a : Fe) (e : Z) : Fe :=
  mkFe (pow_mod (fe_val a) e secp256k1_P) _.
Next Obligation.
  apply pow_mod_range.
  pose proof secp256k1_P_range.
  lia.
Qed.

(** Modular inverse: [a ^ (p-2) mod p], which maps [0] to [0] and every other
    element to its multiplicative inverse (Fermat's little theorem, since
    [p] is prime -- [secp256k1_P_prime] above).  Specifies [secp256k1_fe_inv]
    / [secp256k1_fe_inv_var] (both computed by the safegcd path in the C, not
    by this addition chain -- the C's own doc comment states the Fermat
    characterization this model uses: "Performs {r = a**(p-2)}").
    See https://wuille.net/posts/secp256k1-tutorial/#324-field-finite-field-element-representation *)
Definition fe_inv (a : Fe) : Fe := fe_pow a (secp256k1_P - 2).

(** Square root, as an [option]: [Some r] with [fe_val r * fe_val r mod p =
    fe_val a] when [a] is a square, [None] when it is not.  Specifies
    [secp256k1_fe_sqrt]'s boolean return: [p] is [3 mod 4], so
    [a ^ ((p+1)/4)] is always *a* square root of [a] when one exists (the
    standard formula); checking [r*r = a] afterward is exactly the C's own
    "Check that a square root was actually calculated" step.  When [a] is
    not a square, the C still produces a (different) value -- a square root
    of [-a] -- and returns 0; this model only claims the boolean half of that
    behaviour ([None]), not the C's actual output in that branch.
    See https://wuille.net/posts/secp256k1-tutorial/#324-field-finite-field-element-representation *)
Definition fe_sqrt (a : Fe) : option Fe :=
  let r := fe_pow a ((secp256k1_P + 1) / 4) in
  if Z.eqb (fe_val (fe_mul r r)) (fe_val a) then Some r else None.

(* ================================================================= *)
(** ** Byte conversions -- [fe_of_bytes] / [fe_to_bytes].

    Bytes are big-endian [list Z] (each in [[0,256)]), matching
    [theory.bytes]'s convention (already used for the scalar subsystem's
    [_set_b32] / [_get_b32]). *)

(** Big-endian 32-byte decode, reduced mod p.  Specifies
    [secp256k1_fe_set_b32_mod] (which always reduces) and the reduction half
    of [secp256k1_fe_set_b32_limit] (whose overflow check -- whether the raw
    bytes already represent a value [< p] -- is a range fact on the input
    bytes, not part of this model's return value; that check belongs to
    [contract.field]).
    See https://wuille.net/posts/secp256k1-tutorial/#324-field-finite-field-element-representation *)
Program Definition fe_of_bytes (bs : list Z) : Fe :=
  mkFe (Z_of_be_bytes bs mod secp256k1_P) _.
Next Obligation.
  apply Z.mod_pos_bound.
  pose proof secp256k1_P_range.
  lia.
Qed.

(** Big-endian 32-byte encode of [a]'s canonical representative in [[0,p)].
    Specifies [secp256k1_fe_get_b32] (defined only for normalized input, whose
    C value already equals [fe_val a]).
    See https://wuille.net/posts/secp256k1-tutorial/#324-field-finite-field-element-representation *)
Definition fe_to_bytes (a : Fe) : list Z := be_bytes_of_Z (fe_val a) 32.

