(* Copyright (C) 2026 remix7531. SPDX-License-Identifier: MIT *)

(* begin hide *)
From Stdlib Require Ascii.
From Stdlib Require Bool.
From Stdlib Require Field.
From Stdlib Require Lia.
From Stdlib Require List.
From Stdlib Require Logic.Eqdep_dec.
From Stdlib Require Logic.ProofIrrelevance.
From Stdlib Require Program.
From Stdlib Require Ring.
From Stdlib Require ZArith.
From Stdlib Require Znumtheory.

From Coqprime Require List.UList.
From Coqprime Require PrimalityTest.Euler.
From Coqprime Require PrimalityTest.Zp.
From Coqprime Require elliptic.GZnZ.
From Coqprime Require elliptic.SMain.
From Coqprime Require elliptic.ZEll.
From Coqprime Require examples.PocklingtonRefl.

(* begin framework imports *)
From VST.floyd Require VSU.
From VST.floyd Require proofauto.
Require secp256k1.clight.extraction.

Module CProofFramework.
Export VSU.
Export extraction.
Export proofauto.
End CProofFramework.
(* end framework imports *)

Import Coqprime.List.UList.
Import Coqprime.PrimalityTest.Euler.
Import Coqprime.PrimalityTest.Zp.
Import Coqprime.elliptic.GZnZ.
Import Coqprime.elliptic.SMain.
Import Coqprime.elliptic.ZEll.
Import Coqprime.examples.PocklingtonRefl.

Import Stdlib.Bool.Bool.
Import Stdlib.Lists.List.
Import Stdlib.Lists.List.ListNotations.
Import Stdlib.Logic.Eqdep_dec.
Import Stdlib.Logic.ProofIrrelevance.
Import Stdlib.Program.Program.
Import Stdlib.Strings.Ascii.
Import Stdlib.ZArith.ZArith.
Import Stdlib.ZArith.Znumtheory.
Import Stdlib.micromega.Lia.
Import Stdlib.setoid_ring.Field.
Import Stdlib.setoid_ring.Ring.

(* Imported libraries can change Rocq options. Set the argument policy
   after loading them and before declaring the specification. *)
Unset Implicit Arguments.
Module Math.

(* VST enables asymmetric patterns globally. Keep constructor parameters
   explicit in the mathematical definitions. *)
Local Unset Asymmetric Patterns.
(* end hide *)


(* begin hide *)
Module algebra.
(* end hide *)
(** * Introduction *)

(** Formal verification requires a formal specification. Before we can
    prove that a program is correct, we must state precisely what it
    should do. This document gives that statement for
    {{https://bips.dev/340/}BIP340 Schnorr signatures on secp256k1}.
    The greater goal is to prove that the Schnorr functions in the libsecp256k1
    C library implement these mathematical rules and execute safely.

    A digital signature lets the holder of a secret key sign a message
    that others can check using the corresponding public key. The
    Schnorr signature scheme was invented by
    {{https://link.springer.com/article/10.1007/BF00196725}
    Claus Peter Schnorr}. He patented the method, including
    {{https://patents.google.com/patent/US4995082A/en}
    US patent 4995082}. Bitcoin initially used ECDSA signatures. It
    added the BIP340 variant of Schnorr in
    {{https://bitcoinops.org/en/newsletters/2021/11/17/}
    2021 through the Taproot upgrade}, after that patent had expired.

    The specification starts with pure mathematics. It describes
    Schnorr using abstract mathematical objects, including integers,
    groups, finite fields and curve points. It defines the results
    of operations without prescribing how the C library computes
    them. Memory layouts, machine integer arithmetic, big integer
    routines and optimization tricks belong to the implementation
    proof. Memory safety and the absence of undefined behavior are
    also obligations of that proof, rather than mathematical rules
    that define Schnorr.

    The explanation builds from the bottom up. Operations and their
    laws lead to groups and fields, then to the curve, hashing and
    signatures. Mathematical bytes connect these objects to the
    inputs and outputs required by BIP340. Each definition is
    accompanied by an explanation so that a reader can judge whether
    it expresses the intended rule. The reader needs a technical
    background, but no prior experience with Rocq or Schnorr.

    The final chapter connects the mathematics to C through contracts
    written with the {{https://vst.cs.princeton.edu/}Verified Software
    Toolchain}, abbreviated VST. A contract states what a caller must
    provide and what the function must guarantee. The implementation
    proof must establish that calls satisfying these preconditions
    compute the results specified by the mathematics and have defined
    behavior under {{https://compcert.org/}CompCert C semantics},
    including safe memory access. Functional agreement and memory
    safety are both required.

    Once these contracts are proved under their stated assumptions,
    a reader who agrees with the mathematical specification and trusts
    {{https://rocq-prover.org/}Rocq proof checking} and CompCert C
    semantics can rely on the verified Schnorr functions to be
    functionally correct and memory safe whenever their preconditions
    hold. The proof establishes the connection to C. Agreement that
    the specification captures the intended behavior remains a human
    judgment. Resistance to forgery requires a separate cryptographic
    security argument.

    You are reading a Rocq script rendered as HTML by Rocq. The
    {{specification.v}complete source} can be opened in a
    Rocq editor. The page hides imports and some supporting proofs
    for readability. They remain in the source and are checked during
    compilation.

    The presentation follows
    {{https://wuille.net/posts/secp256k1-tutorial/}Pieter Wuille on
    secp256k1}. Further reading includes
    {{https://crypto.stanford.edu/~dabo/cryptobook/}A Graduate Course
    in Applied Cryptography} and {{https://shoup.net/ntb/}A
    Computational Introduction to Number Theory and Algebra}. The C
    reference is {{https://github.com/bitcoin-core/secp256k1}
    libsecp256k1}, at release [v0.8.0]. *)

(** * 1. Operations, Groups and Fields *)

(** An operation tells us how to combine or transform values. Laws
    describe how those operations behave. We use these laws to define
    groups and fields, the abstract structures needed for arithmetic
    on scalars, coordinates and curve points.

    A [Definition] names a value or function. A [Lemma] or [Theorem]
    states a claim. Commands between [Proof.] and [Qed.] construct
    evidence checked by Rocq. A _tactic_ is a command that builds
    part of this evidence. For example, [reflexivity] proves equality
    by reducing both sides to the same expression. *)

(* ================================================================= *)
(** ** 1.1 Operations *)

(** An _operation_ takes values and produces a value. Integer addition
    takes two integers, such as [2] and [3], and returns their sum.
    Negation takes one integer and returns its opposite. We will also
    add curve points, where addition has a different rule. The symbol
    [+] can name either operation because the types of its inputs
    determine which rule applies.

    In Rocq, [(A : Type)] introduces a type named [A]. The signature
    [A -> A -> A] describes a function taking two values of type [A]
    and returning one. A [Class] lets Rocq find an operation from the
    types involved. For example, [Add A] supplies the function named
    [add]. These declarations supply names and signatures. Laws such
    as associativity come separately.

    Braces around an argument, as in [{A : Type}], make it implicit.
    Rocq infers it from the supplied values when possible. Explicit
    arguments use parentheses. These are argument declarations,
    unlike the braces that enclose record fields. *)

Class Zero (A : Type) : Type := zero : A.
Class Add (A : Type) : Type := add : A -> A -> A.
Class Neg (A : Type) : Type := neg : A -> A.
Class One (A : Type) : Type := one : A.
Class Mul (A B C : Type) : Type := mul : A -> B -> C.
Class Power (A E : Type) : Type := pow : A -> E -> A.
Class Inv (A : Type) : Type := inv : A -> A.
Class Eqb (A : Type) : Type := eqb : A -> A -> bool.

(** [Zero] and [One] supply distinguished values, usually written [0]
    and [1]. [Neg] supplies negation and [Inv] supplies a multiplicative
    inverse. [Eqb] supplies an equality test returning [true] or
    [false], the two values of [bool].

    [Mul] has separate types for its two inputs and its output. Ordinary
    multiplication uses the same type throughout. Multiplying a scalar
    by a curve point takes different input types and returns a point.
    [Power A E] takes a base of type [A] and an exponent of type [E],
    and returns a value of type [A]. The exponent type will select
    how to calculate the power.

    A [Notation] declaration gives a readable spelling to a function
    call. Thus [a + b] below is a spelling of [add a b]. A scope groups
    these spellings so Rocq can distinguish them from integer
    arithmetic. A suffix such as [%N] or [%Z] selects one scope for one
    expression. For example, [0%N] is zero at the binary natural-number
    type [N]. *)

Declare Scope math_scope.
Delimit Scope math_scope with M.

Notation "a + b" := (add a b) (at level 50, left associativity) : math_scope.
Notation "- a" := (neg a) (at level 35, right associativity) : math_scope.
Notation "a - b" := (add a (neg b)) (at level 50, left associativity) : math_scope.
Notation "a * b" := (mul a b) (at level 40, left associativity) : math_scope.
Notation "a ^ e" := (pow a e) (at level 30, right associativity) : math_scope.
Notation "/ a" := (inv a) (at level 35, right associativity) : math_scope.
Notation "a / b" := (mul a (inv b)) (at level 40, left associativity) : math_scope.
Notation "a =? b" := (eqb a b) (at level 70, no associativity) : math_scope.

(* begin hide *)
Local Open Scope math_scope.
(* end hide *)

(** Read [- a] as the additive opposite of [a], [/ a] as its
    multiplicative inverse, and [a =? b] as an equality test.
    Subtraction adds the opposite. Division multiplies by the
    inverse. The symbol [=] states an equality, while [=?] computes a
    boolean answer. The notation [a ^ e] calls [pow]. Its base and
    exponent types select the power operation. *)

(* ================================================================= *)
(** ** 1.2 Groups *)

(** A {{https://en.wikipedia.org/wiki/Group_(mathematics)}group}
    consists of a set and an associative operation with an identity
    and an inverse for each value. Integer addition is an example. A
    sum of integers is an integer, zero leaves each value unchanged,
    and a number plus its negative is zero.

    _Associativity_ allows regrouping without changing the result. An
    _identity_ leaves a value unchanged. An _inverse_ cancels a value
    to the identity. Closure is expressed by [A -> A -> A], whose
    result belongs to [A].

    The fields of [Group] are proofs of these laws. [forall x : A]
    means that a statement holds for every value [x] of type [A]. *)

Class Group (A : Type) {ZeroA : Zero A} {AddA : Add A} {NegA : Neg A} : Type := {
  group_add_assoc : forall x y z : A, x + (y + z) = x + y + z;
  group_add_zero : forall x : A, zero + x = x;
  group_add_inverse : forall x : A, - x + x = zero
}.

(** The first equation says that [x + (y + z)] equals [(x + y) + z]. The
    second and third put zero and the inverse on the left. Together with
    associativity, these laws also imply the corresponding right-hand
    equations. They are sufficient to justify cancellation and solving
    an equation such as [a + x = b].

    A group need not let us exchange the order of its inputs. When
    [x + y = y + x] always holds, the group is called _abelian_, or
    commutative. Integer addition has this property. The separate
    proposition below records it without choosing any new operation.
    In Rocq, [Prop] is the type of logical statements. *)

(** Composing permutations gives a nonabelian example. Swap positions
    one and two, then swap two and three. An item starting in position
    one finishes in position three. Reversing the swaps leaves it in
    position two. The operation is composition and the identity leaves
    each position unchanged. *)

(** Left cancellation follows by adding the inverse on the left.
    The tactic [intro] names an input or assumption, and [intros]
    names several. [apply] uses an existing theorem. [rewrite]
    replaces an expression using a known equality. Here [f_equal]
    applies the same function to both sides of an equality. *)
Lemma group_add_cancel_left {A : Type} `{Group A} (a b c : A) :
  a + b = a + c -> b = c.
Proof.
  intro equation.
  apply (f_equal (fun x => - a + x)) in equation.
  rewrite !group_add_assoc, !group_add_inverse, !group_add_zero in equation.
  exact equation.
Qed.

(** The left laws also give a right identity. *)
Lemma group_add_zero_right {A : Type} `{Group A} (a : A) :
  a + zero = a.
Proof.
  apply (group_add_cancel_left (- a)).
  rewrite group_add_assoc, !group_add_inverse, group_add_zero.
  reflexivity.
Qed.

(** The same cancellation gives a right inverse. *)
Lemma group_add_inverse_right {A : Type} `{Group A} (a : A) :
  a + - a = zero.
Proof.
  apply (group_add_cancel_left (- a)).
  rewrite group_add_assoc, group_add_inverse, group_add_zero, group_add_zero_right.
  reflexivity.
Qed.

Definition Abelian (A : Type) `{Group A} : Prop :=
  forall x y : A, x + y = y + x.

(** A _homomorphism_ is a function between groups that preserves their
    operation. One elementary example is doubling integers: doubling
    [x + y] gives the same result as doubling each input and adding the
    results. The equation below says exactly that for any function [f].
    The types of [x] and [y] select addition in the source group, while
    the type of [f x] selects addition in the destination group. *)

Definition Homomorphism {A B : Type} `{Group A} `{Group B} (f : A -> B) : Prop :=
  forall x y : A, f (x + y) = f x + f y.

(** This property lets an equation in one group give an equation in
    another. Once a function is shown to be a homomorphism, we can move
    addition through it using [f (x + y) = f x + f y]. *)

(* ================================================================= *)
(** ** 1.3 Fields *)

(** #<div class="spec-figure" data-figure="field-f7"></div># *)

(** A {{https://en.wikipedia.org/wiki/Field_(mathematics)}field}
    supports addition, subtraction, multiplication and division by
    nonzero values. The rational numbers are a familiar example. Unlike
    the integers, they include a multiplicative inverse for every
    nonzero element: the inverse of [2] is [1 / 2].

    A _finite field_ has the same laws with finitely many values. For
    a small example, take the integers from zero to six and reduce
    every sum and product modulo seven. Reduction keeps the remainder
    after division by seven. Adding five and four gives two, because
    nine has remainder two. Multiplying three and five gives one, so
    five is the multiplicative inverse of three.

    The prime modulus matters. Modulo eight, two has no multiplicative
    inverse: multiplying it by any integer always gives an even
    remainder. Modulo a prime, every nonzero remainder has an inverse.
    The secp256k1 coordinate and scalar fields use this construction
    with different large primes.

    The additive laws below make an abelian group. Multiplication is
    associative and commutative, has identity [one], and has inverses
    away from zero. Distributivity connects the two operations, allowing
    a product over a sum to be expanded. Finally, zero and one must be
    distinct. *)

Class Field (A : Type)
    {ZeroA : Zero A} {AddA : Add A} {NegA : Neg A}
    {OneA : One A} {MulA : Mul A A A} {InvA : Inv A} : Type := {
  field_add_assoc : forall x y z : A, x + (y + z) = x + y + z;
  field_add_comm : forall x y : A, x + y = y + x;
  field_add_zero : forall x : A, zero + x = x;
  field_add_inverse : forall x : A, - x + x = zero;
  field_multiply_assoc : forall x y z : A, x * (y * z) = x * y * z;
  field_multiply_comm : forall x y : A, x * y = y * x;
  field_multiply_one : forall x : A, one * x = x;
  field_distributive : forall x y z : A, x * (y + z) = x * y + x * z;
  field_zero_not_one : zero <> one;
  field_multiply_inverse : forall x : A, x <> zero -> / x * x = one
}.

(** Ordinary division by zero is undefined. In
    [field_multiply_inverse], [x <> zero -> ...] requires the inverse
    equation only for nonzero [x]. Rocq functions are total, so the
    inverse function still accepts zero. These laws do not prescribe
    its value there. A division operation must check its divisor or
    handle zero separately.

    The classes [Group] and [Field] state laws. They do not establish
    those laws for any particular implementation. The following
    chapters define concrete values and operations, then prove that
    they satisfy the laws. *)

(* ================================================================= *)
(** ** 1.4 Powers *)

(** _Powers_ mean repeated multiplication. Three copies of [a] give
    [a * a * a]. Zero copies give [one]. The same construction works
    for any type with multiplication and an identity. We first define
    it directly, then use the multiplication laws to justify a faster
    algorithm.

    Rocq has several number types. [nat] is unary, with constructors
    [O] and [S]. Each successor adds one. [positive] is binary and
    excludes zero. Its constructors [xH], [xO] and [xI] mean one,
    twice a positive number, and twice that number plus one. [N] adds
    zero to [positive], using [N0] and [Npos]. Finally, [Z] adds a
    sign, with [Z0], [Zpos] and [Zneg]. Both [nat] and [N] represent
    natural numbers, including zero. They differ in representation,
    not in which numbers they contain. We use [nat] for array lengths
    and the first definition of powers, [N] for large exponents, and
    [Z] for integer arithmetic.

    A [Fixpoint] defines a recursive function. The [match] expression
    follows the two constructors of [nat]. At [O] it returns [one].
    At [S rest] it multiplies [a] by the power for [rest]. Each
    recursive call uses a smaller argument, so the calculation
    terminates. *)

Fixpoint power {A : Type} {MulA : Mul A A A} {OneA : One A}
    (a : A) (e : nat) : A :=
  match e with
  | O => one
  | S rest => a * power a rest
  end.

(** These equations state the two cases of repeated multiplication.
    [S e] means [e + 1]. *)

Lemma power_zero {A : Type} {MulA : Mul A A A} {OneA : One A}
    (a : A) :
  power a O = one.
Proof.
  reflexivity.
Qed.

Lemma power_succ {A : Type} {MulA : Mul A A A} {OneA : One A}
    (a : A) (e : nat) :
  power a (S e) = a * power a e.
Proof.
  reflexivity.
Qed.

(** Large exponents need a faster calculation. Squaring uses the
    fact that multiplying [2 * k] copies of [a] gives the square of
    [power a k]. For [2 * k + 1] copies, multiply that square by [a].
    The prime in [power'] names this efficient implementation. Its
    exponent uses the binary type [N]. Each recursive call removes
    one binary digit, instead of subtracting one from the exponent.
    The two functions therefore take different representations of
    the same natural number. *)

Definition power' {A : Type} {MulA : Mul A A A} {OneA : One A}
    (a : A) (e : N) : A :=
  let fix positive_power (e' : positive) : A :=
    match e' with
    | xH => (* One: return the base. *) a
    | xO rest => (* Even: square the power of the remaining digits. *)
        let s := positive_power rest in s * s
    | xI rest => (* Odd: multiply the base by the squared prefix. *)
        let s := positive_power rest in a * (s * s)
    end in
  match e with
  | N0 => (* Zero: return the multiplicative identity. *) one
  | Npos p => positive_power p
  end.

(** Associativity and a right identity justify the faster algorithm.
    The next lemma joins two runs of multiplication when the first is
    nonempty.

    The proof uses [induction] to split the recursive argument into
    its base and step cases, and [destruct] to split the cases of a
    value. The tactic [lia] closes linear integer inequalities.
    Bullets separate the resulting proof cases. *)

Lemma power_add_positive {A : Type} {MulA : Mul A A A} {OneA : One A}
    (Hassoc : forall x y z : A, x * (y * z) = (x * y) * z)
    (Hone : forall x : A, x * one = x) (a : A) (n m : nat) :
  (0 < n)%nat -> power a (n + m)%nat = power a n * power a m.
Proof.
  revert m.
  induction n as [|n IH].
  - (* An empty first run is excluded by the premise. *)
    intros m Hn.
    lia.
  - (* Remove the first multiplication from the nonempty run. *)
    intros m Hn.
    destruct n as [|n].
    + (* A singleton run is just its base. *)
      rewrite Nat.add_succ_l, Nat.add_0_l, !power_succ, power_zero, Hone.
      reflexivity.
    + (* Associativity joins the remaining runs. *)
      rewrite Nat.add_succ_l, !power_succ.
      rewrite IH by lia.
      apply Hassoc.
Qed.

(** The next theorem proves that the binary algorithm has exactly the
    meaning given by repeated multiplication. [N.to_nat e] converts
    the binary exponent to its unary representation without changing
    its value. This conversion appears in the correctness statement.
    The efficient calculation itself stays in [N]. *)

Theorem power'_eq_power {A : Type} {MulA : Mul A A A} {OneA : One A}
    (Hassoc : forall x y z : A, x * (y * z) = (x * y) * z)
    (Hone : forall x : A, x * one = x) (a : A) (e : N) :
  power' a e = power a (N.to_nat e).
Proof.
  destruct e as [|e].
  - (* Both definitions assign the identity to exponent zero. *)
    reflexivity.
  - (* Positive exponents are read one binary digit at a time. *)
    induction e as [e IH|e IH|].
    + (* An odd exponent adds the base after squaring. *)
      change (a * (power' a (Npos e) * power' a (Npos e)) =
        power a (N.to_nat (Npos (xI e)))).
      replace (N.to_nat (Npos (xI e))) with
        (S (N.to_nat (Npos e) + N.to_nat (Npos e))) by lia.
      rewrite power_succ, IH, power_add_positive by
        (try assumption; lia).
      reflexivity.
    + (* An even exponent is the square of the shorter power. *)
      change (power' a (Npos e) * power' a (Npos e) =
        power a (N.to_nat (Npos (xO e)))).
      replace (N.to_nat (Npos (xO e))) with
        (N.to_nat (Npos e) + N.to_nat (Npos e))%nat by lia.
      rewrite IH, power_add_positive by (try assumption; lia).
      reflexivity.
    + (* Multiplication by the identity leaves the base unchanged. *)
      change (a = a * one).
      symmetry.
      apply Hone.
Qed.

(** These definitions supply [Power] for each exponent type. A [nat]
    exponent selects repeated multiplication. An [N] exponent selects
    the efficient binary algorithm. The theorem above proves that
    they agree under the stated multiplication laws. *)

Definition Power_nat {A : Type} {MulA : Mul A A A} {OneA : One A} :
    Power A nat := power.

Definition Power_N {A : Type} {MulA : Mul A A A} {OneA : One A} :
    Power A N := power'.

(* begin hide *)
#[export] Existing Instance Power_nat.
#[export] Existing Instance Power_N.
#[export] Hint Mode Power + + : typeclass_instances.
(* end hide *)

(** For a literal exponent, [a ^ 3%nat] selects repeated
    multiplication and [a ^ 3%N] selects the binary algorithm.
    A variable exponent already carries the type that selects
    the instance. *)

(* begin hide *)
End algebra.
(* end hide *)


(* begin hide *)
Module bytes.
(* end hide *)
(** * 2. Bytes *)

(** Keys, signatures and messages cross a software interface as
    bytes. We must specify which values fit, how many bytes are
    present, and which end holds the most significant part. A byte
    holds an integer from zero to 255. An array records an exact
    number of values. The {{#appendix-word-operations}word and array
    appendix} gives the supporting operations. *)

(* begin hide *)

Open Scope Z_scope.
(* end hide *)

(* ================================================================= *)
(** ** 2.1 Bytes and Bounds *)

(** A _word_ is an unsigned integer with a fixed bit width. A byte has
    type [Word 8], so it has eight bits and can hold values from zero
    to 255. A Rocq [Record] collects named fields, here an integer and
    a proof that it fits. The type [nat] describes nonnegative lengths.
    [Z.of_nat] converts a length to an integer for the bound. *)

Record Word (width : nat) := mkWord {
  word_val : Z;
  word_range : 0 <= word_val < 2 ^ Z.of_nat width
}.
Arguments mkWord {width}.
Arguments word_val {width}.
Arguments word_range {width}.
Coercion word_val : Word >-> Z.


(** The projection [word_val word] retrieves the stored integer. The
    [Coercion] declaration lets Rocq insert this projection when a word
    appears in integer arithmetic. Construction requires a range
    proof, so an oversized literal cannot silently wrap. *)

Definition word_of_Z (width : nat) (value : Z)
    (range : 0 <= value < 2 ^ Z.of_nat width) : Word width :=
  @mkWord width value range.




(** #<!-- begin appendix --># *)
(** * A. Word and Array Operations *)

(** The encodings used by fields and signatures rest on the checked
    constructors below. SHA-256 also needs modular word arithmetic,
    bit operations and length-preserving array operations. These
    definitions make those choices explicit. *)

(** ** A.1 Modular Word Arithmetic *)


(* begin hide *)
Local Definition word_modulus (width : nat) : Z := 2 ^ Z.of_nat width.

Local Program Definition word_reduce (width : nat) (value : Z) : Word width :=
  word_of_Z width (value mod word_modulus width) _.
Next Obligation.
  apply Z.mod_pos_bound.
  unfold word_modulus.
  apply Z.pow_pos_nonneg; lia.
Qed.
(* end hide *)

(** Arithmetic on words deliberately wraps. [word_add] reduces the sum
    modulo [2^width], so adding 255 and one as [Word 8] values gives
    zero. The hidden helper [word_reduce] performs that reduction and
    proves the result fits. Bitwise [xor], [and] and [not] act within
    the same width. *)

Definition word_add {width : nat} (left right : Word width) : Word width :=
  word_reduce width (word_val left + word_val right).

Definition word_xor {width : nat} (left right : Word width) : Word width :=
  word_reduce width (Z.lxor (word_val left) (word_val right)).

Definition word_and {width : nat} (left right : Word width) : Word width :=
  word_reduce width (Z.land (word_val left) (word_val right)).

Definition word_not {width : nat} (value : Word width) : Word width :=
  word_reduce width (Z.lnot (word_val value)).

(** A right shift drops low bits and fills high bits with zeros. A right
    rotation moves those low bits to the high end. For an eight-bit
    word, rotating one right by one gives 128, while shifting it gives
    zero. Both operations require a count smaller than the width. Their
    readable spellings are [value shr count] and [value rotr count]. *)

Definition word_shr {width : nat} (value : Word width) (count : nat)
    (_ : (count < width)%nat) : Word width :=
  word_reduce width (Z.shiftr (word_val value) (Z.of_nat count)).

Definition word_rotr {width : nat} (value : Word width) (count : nat)
    (_ : (count < width)%nat) : Word width :=
  word_reduce width
    (Z.lor
      (Z.shiftr (word_val value) (Z.of_nat count))
      (Z.shiftl (word_val value) (Z.of_nat (width - count)))).

(* begin hide *)
Declare Scope word_scope.
Delimit Scope word_scope with word.
(* end hide *)
Notation "left 'xor' right" := (word_xor left right)
  (at level 50, left associativity) : word_scope.
Notation "left 'and' right" := (word_and left right)
  (at level 40, left associativity) : word_scope.
Notation "'not' value" := (word_not value)
  (at level 35, right associativity) : word_scope.
Notation "value 'shr' count" := (word_shr value count _)
  (at level 40, left associativity) : word_scope.
Notation "value 'rotr' count" := (word_rotr value count _)
  (at level 40, left associativity) : word_scope.

(** #<!-- end appendix --># *)

(* ================================================================= *)
(** ** 2.2 Arrays of Known Length *)

(** An [Array A n] contains exactly [n] values of type [A]. Its
    underlying [list A] could have any length, but [array_length]
    proves the required length. Thus an array of 32 bytes cannot hold
    a 31-byte key.

    The projection [array_list array] selects the list, while
    [array_length array] selects its length proof. [Word] and [Array]
    are records because they store data and an invariant. A class
    instead provides operations or laws that Rocq selects from a type.
    The array operations below wrap standard list operations and
    preserve the length facts in their result types. *)

Record Array (A : Type) (n : nat) := mkArray {
  array_list : list A;
  array_length : length array_list = n
}.
Arguments mkArray {A n}.
Arguments array_list {A n}.
Arguments array_length {A n}.
Coercion array_list : Array >-> list.

Definition array_of_list {A : Type} (values : list A) :
    Array A (length values) :=
  mkArray values eq_refl.

(** #<!-- begin appendix --># *)
(** ** A.2 Length-preserving Operations *)

(** Mapping changes elements without changing their number. Appending
    with [++] adds lengths, splitting chooses a cut, and zipping pairs
    elements at corresponding positions. In a [Program Definition],
    an underscore can stand for a proof that Rocq generates as a
    separate obligation. Every resulting length is still checked. *)

(* begin hide *)
Local Obligation Tactic :=
  (intros;
   repeat match goal with
   | array : Array _ _ |- _ => destruct array as [? ?]
   end;
   cbn [array_list] in *;
   rewrite ?length_map, ?length_app, ?length_firstn,
     ?length_skipn, ?length_combine, ?repeat_length in *;
   cbn [length] in *;
   lia).
(* end hide *)

(** [Program Definition] accepts [_] for missing evidence. Rocq may
    infer it directly or produce an obligation that must be proved.
    The following array definitions use a shared tactic for their list
    length equations. These holes are checked proofs, not
    assumptions. *)

Program Definition array_nil {A : Type} : Array A 0 := mkArray [] _.

Program Definition array_snoc {A : Type} {n : nat}
    (array : Array A n) (value : A) : Array A (S n) :=
  mkArray (array_list array ++ [value]) _.

Program Definition array_map {A B : Type} {n : nat}
    (function : A -> B) (array : Array A n) : Array B n :=
  mkArray (map function (array_list array)) _.

Program Definition array_app {A : Type} {m n : nat}
    (left : Array A m) (right : Array A n) : Array A (m + n) :=
  mkArray (array_list left ++ array_list right) _.

(* begin hide *)
Declare Scope array_scope.
Delimit Scope array_scope with array.
(* end hide *)
Notation "left ++ right" := (array_app left right)
  (at level 60, right associativity) : array_scope.

Program Definition array_split {A : Type} (m n : nat)
    (array : Array A (m + n)) : Array A m * Array A n :=
  (mkArray (firstn m (array_list array)) _,
   mkArray (skipn m (array_list array)) _).

Program Definition array_zip {A B : Type} {n : nat}
    (left : Array A n) (right : Array B n) : Array (A * B) n :=
  mkArray (combine (array_list left) (array_list right)) _.

Program Definition array_repeat {A : Type} (value : A) (n : nat) :
    Array A n :=
  mkArray (repeat value n) _.

(** [array_repeat] fills an array with copies of one value. A cast
    changes the way a length is expressed using a proof that the two
    expressions are equal. It leaves the elements unchanged. *)

Definition array_cast {A : Type} {m n : nat} (length_equal : m = n)
    (array : Array A m) : Array A n :=
  mkArray (array_list array)
    (eq_trans (array_length array) length_equal).

(* begin hide *)
Local Fixpoint list_get_bounded {A : Type} (values : list A) (index : nat)
    (index_range : (index < length values)%nat) : A :=
  match values as values' return (index < length values')%nat -> A with
  | [] => fun invalid => False_rect A (Nat.nlt_0_r index invalid)
  | value :: rest =>
      match index as index' return
          (index' < length (value :: rest))%nat -> A with
      | O => fun _ => value
      | S rest_index => fun rest_range =>
          list_get_bounded rest rest_index
            (proj2 (Nat.succ_lt_mono rest_index (length rest)) rest_range)
      end
  end index_range.
(* end hide *)

(** [array_get] counts positions from zero and requires [index < n].
    There is no default element for an invalid index. Concatenation and
    chunking convert between an array of equal-sized arrays and one flat
    array, preserving the element order. *)

Definition array_get {A : Type} {n : nat} (array : Array A n)
    (index : nat) (index_range : (index < n)%nat) : A :=
  list_get_bounded (array_list array) index
    (eq_ind_r (fun length => (index < length)%nat) index_range
      (array_length array)).

(* begin hide *)
Local Program Definition array_cons {A : Type} {n : nat} (value : A)
    (array : Array A n) : Array A (S n) :=
  mkArray (value :: array_list array) _.
(* end hide *)

(* begin hide *)
Local Fixpoint array_concat_go {A : Type} {m : nat} (n : nat)
    (arrays : Array (Array A m) n) : Array A (n * m) :=
  match n as n' return Array (Array A m) n' -> Array A (n' * m) with
  | O => fun _ => array_nil
  | S rest_length => fun nonempty =>
      let '(first_array, rest_arrays) :=
        array_split 1 rest_length nonempty in
      array_app (array_get first_array 0 (Nat.lt_0_succ 0))
        (array_concat_go rest_length rest_arrays)
  end arrays.
(* end hide *)

Definition array_concat {A : Type} {m n : nat}
    (arrays : Array (Array A m) n) : Array A (n * m) :=
  array_concat_go n arrays.

Fixpoint array_chunks {A : Type} (n k : nat)
    (array : Array A (n * k)) : Array (Array A k) n :=
  match n as n' return Array A (n' * k) -> Array (Array A k) n' with
  | O => fun _ => array_nil
  | S rest_length => fun nonempty =>
      let '(first_chunk, rest_array) :=
        array_split k (rest_length * k) nonempty in
      array_cons first_chunk (array_chunks rest_length k rest_array)
  end array.

(* ================================================================= *)
(** ** A.3 Checked Literals *)

(** [words] constructs arrays of fixed-width words from numeric
    literals. Choosing width eight constructs bytes. [Forall] requires
    the range condition to hold for every list entry. This keeps
    hexadecimal SHA-256 constants readable without accepting an
    out-of-range value. *)

(* begin hide *)
Local Fixpoint checked_words (width : nat) (values : list Z)
    (values_range : Forall
      (fun value => 0 <= value < 2 ^ Z.of_nat width) values) :
    Array (Word width) (length values) :=
  match values as values' return
      Forall (fun value => 0 <= value < 2 ^ Z.of_nat width) values' ->
      Array (Word width) (length values') with
  | [] => fun _ => array_nil
  | value :: rest => fun ranges =>
      array_cons (word_of_Z width value (Forall_inv ranges))
        (checked_words width rest (Forall_inv_tail ranges))
  end values_range.

(* end hide *)

Definition words (width : nat) (values : list Z)
    {values_range : Forall
      (fun value => 0 <= value < 2 ^ Z.of_nat width) values} :
    Array (Word width) (length values) :=
  checked_words width values values_range.

(* begin hide *)
Local Definition byte_of_ascii (character : ascii) : Word 8.
Proof.
  apply ((word_of_Z 8) (Z.of_nat (nat_of_ascii character))).
  split.
  - (* conjunct 0: character value is nonnegative *)
    apply Nat2Z.is_nonneg.
  - (* conjunct 1: character value fits one byte *)
    change (Z.of_nat (nat_of_ascii character) < Z.of_nat 256).
    apply (proj1 (Nat2Z.inj_lt _ _)).
    apply nat_ascii_bounded.
Defined.
(* end hide *)

(** [chars] writes character data as [Word 8] values. It adds no
    terminating zero byte, so the tag length is exactly the number of
    characters supplied. *)

Definition chars (characters : list ascii) :
    Array (Word 8) (length characters) :=
  array_map byte_of_ascii (array_of_list characters).

(* ================================================================= *)
(** ** A.4 Integer Encoding *)

(** _Big-endian encoding_ puts the most significant byte first. For
    example, bytes one and two denote [1 * 256 + 2], which is 258.
    [fold_left] reads from left to right, multiplying the accumulated
    value by 256 before adding each byte. *)

Definition Z_of_byte_list (byte_list : list (Word 8)) : Z :=
  fold_left
    (fun accumulator byte => accumulator * 256 + word_val byte)
    byte_list 0.

(* begin hide *)
Local Definition byte_of_residue (value : Z) : Word 8.
Proof.
  apply ((word_of_Z 8) (value mod 256)).
  apply Z.mod_pos_bound.
  lia.
Defined.

Local Lemma byte_quotient_range : forall (n : nat) (value : Z),
  0 <= value < 2 ^ (8 * Z.of_nat (S n)) ->
  0 <= value / 256 < 2 ^ (8 * Z.of_nat n).
Proof.
  intros n value range.
  split.
  - (* conjunct 0: quotient is nonnegative *)
    apply Z.div_pos; lia.
  - (* conjunct 1: quotient fits the remaining bytes *)
    apply Z.div_lt_upper_bound.
    + (* byte radix is positive *)
      lia.
    + (* original bound scales by one byte *)
      rewrite Nat2Z.inj_succ in range.
      replace (8 * Z.succ (Z.of_nat n))
        with (8 * Z.of_nat n + 8) in range by lia.
      rewrite Z.pow_add_r in range by lia.
      replace (2 ^ 8) with 256 in range by reflexivity.
      nia.
Qed.
(* end hide *)

(** Encoding reverses that process. Division by 256 extracts the
    preceding bytes, while the remainder is the last byte. The range
    argument requires the whole integer to fit in [n] bytes, so no high
    bits can be discarded. Leading zero bytes are retained to reach the
    requested length. *)

(* begin hide *)
Local Fixpoint encode_bytes (value : Z) (n : nat)
    (range : 0 <= value < 2 ^ (8 * Z.of_nat n)) : Array (Word 8) n :=
  match n as n' return
      0 <= value < 2 ^ (8 * Z.of_nat n') -> Array (Word 8) n' with
  | O => fun _ => array_nil
  | S rest_length => fun successor_range =>
      array_snoc
        (encode_bytes (value / 256) rest_length
          (byte_quotient_range rest_length value successor_range))
        (byte_of_residue value)
  end range.

(* end hide *)
(** #<!-- end appendix --># *)

(* ================================================================= *)
(** ** 2.3 Integer Encodings *)

(** For example, the two bytes [0x01] and [0x02] encode the integer
    [258] in big-endian order. [bytes_of_Z] writes exactly [n] bytes
    and retains leading zeros. Its range argument ensures that no high
    bits are discarded. [Z_of_bytes] reads the same sequence back as
    an integer. The {{#appendix-word-operations}appendix proof} shows
    that decoding an encoding recovers the original integer. *)

Definition bytes_of_Z (value : Z) (n : nat)
    (range : 0 <= value < 2 ^ (8 * Z.of_nat n)) : Array (Word 8) n :=
  encode_bytes value n range.

Definition Z_of_bytes {n : nat} (array : Array (Word 8) n) : Z :=
  Z_of_byte_list (array_list array).

(** #<!-- begin appendix --># *)
(** ** A.5 Byte Projections and Word Encodings *)

(** [bytes_Z] exposes the separate byte values as ordinary integers.
    It is useful when comparing an encoding with a test vector or a
    C memory representation. *)

Definition bytes_Z {n : nat} (array : Array (Word 8) n) : list Z :=
  map word_val (array_list array).

(* begin hide *)
Local Lemma byte_fold_left_acc : forall (byte_list : list (Word 8))
    (accumulator : Z),
  fold_left
    (fun acc byte => acc * 256 + word_val byte)
    byte_list accumulator =
  accumulator * 256 ^ Z.of_nat (length byte_list) +
  fold_left
    (fun acc byte => acc * 256 + word_val byte)
    byte_list 0.
Proof.
  induction byte_list as [|byte rest induction]; intros accumulator.
  - (* empty list *)
    cbn.
    lia.
  - (* one byte followed by a suffix *)
    cbn [length].
    rewrite Nat2Z.inj_succ.
    rewrite Z.pow_succ_r by lia.
    cbn [fold_left].
    rewrite (induction (accumulator * 256 + word_val byte)).
    rewrite (induction (0 * 256 + word_val byte)).
    lia.
Qed.
(* end hide *)

(** The range statement records the unsigned bound for any byte list. *)

Lemma Z_of_byte_list_range (byte_list : list (Word 8)) :
  0 <= Z_of_byte_list byte_list <
    2 ^ (8 * Z.of_nat (length byte_list)).
(* begin hide *)
Proof.
  unfold Z_of_byte_list.
  induction byte_list as [|byte rest induction].
  - (* empty list *)
    cbn.
    lia.
  - (* one byte followed by a bounded suffix *)
    cbn [length].
    cbn [fold_left].
    rewrite byte_fold_left_acc.
    pose proof (word_range byte) as byte_bounds.
    replace (8 * Z.of_nat (S (length rest)))
      with (8 * Z.of_nat (length rest) + 8)
      by (rewrite Nat2Z.inj_succ; lia).
    rewrite Z.pow_add_r by lia.
    replace (2 ^ 8) with 256 by reflexivity.
    assert (power_nonnegative :
      0 <= 2 ^ (8 * Z.of_nat (length rest)))
      by (apply Z.pow_nonneg; lia).
    replace (256 ^ Z.of_nat (length rest))
      with (2 ^ (8 * Z.of_nat (length rest)))
      by (rewrite Z.pow_mul_r by lia; reflexivity).
    nia.
Qed.
(* end hide *)

(** Words whose width is a multiple of eight convert to bytes in this
    same order. A [Word 32] occupies four bytes. *)

Definition word_to_bytes {n : nat} (word : Word (8 * n)) :
    Array (Word 8) n.
(* begin hide *)
Proof.
  apply (bytes_of_Z (word_val word) n).
  pose proof (word_range word) as range.
  rewrite Nat2Z.inj_mul in range.
  cbn in range.
  exact range.
Defined.
(* end hide *)

Definition word_of_bytes {n : nat} (array : Array (Word 8) n) : Word (8 * n).
(* begin hide *)
Proof.
  apply (word_of_Z (8 * n) (Z_of_bytes array)).
  unfold Z_of_bytes.
  pose proof (Z_of_byte_list_range (array_list array)) as range.
  rewrite (array_length array) in range.
  rewrite Nat2Z.inj_mul.
  cbn.
  exact range.
Defined.
(* end hide *)



(** Bytewise [xor] pairs equally positioned bytes. The shared length [n]
    rules out unequal inputs. *)

Definition bytes_xor {n : nat} (left right : Array (Word 8) n) :
    Array (Word 8) n :=
  array_map (fun pair => word_xor (fst pair) (snd pair))
    (array_zip left right).

(* begin hide *)
Declare Scope bytes_scope.
Delimit Scope bytes_scope with bytes.
(* end hide *)
Notation "left 'xor' right" := (bytes_xor left right)
  (at level 50, left associativity) : bytes_scope.

(** #<!-- end appendix --># *)

(* ================================================================= *)
(** ** 2.4 Encoding and Decoding *)

(** [Encode] and [Decode] name the byte conversion for each type. An
    [option A] is either [Some value], a successful result, or [None], a
    rejection. Having the right number of bytes does not guarantee a
    valid field element or signature. Decoding also checks the value
    constraints of the target type. *)

Class Encode (A : Type) (n : nat) : Type := {
  encode : A -> Array (Word 8) n
}.

Class Decode (A : Type) (n : nat) : Type := {
  decode : Array (Word 8) n -> option A
}.

(** Generic encodings cover words with a whole number of bytes. Their
    width is [8 * n]. Decoding every array of this size succeeds. *)

#[export] Instance Word_encode (n : nat) : Encode (Word (8 * n)) n :=
  {| encode := @word_to_bytes n |}.

#[export] Instance Word_decode (n : nat) : Decode (Word (8 * n)) n :=
  {| decode bs := Some (@word_of_bytes n bs) |}.

(** ** 2.5 Rejecting Invalid Components *)

(** The notation [let* value := expression in ...] continues only when
    [expression] returns [Some value]. A [None] result propagates
    immediately. This lets a decoder reject malformed components before
    using them. *)

Definition option_bind {A B : Type} (value : option A)
    (continuation : A -> option B) : option B :=
  match value with
  | Some result => continuation result
  | None => None
  end.
Notation "'let*' pattern ':=' expression 'in' continuation" :=
  (option_bind expression (fun pattern => continuation))
  (at level 200, pattern pattern at level 0, expression at level 100,
   continuation at level 200, right associativity).



(* begin hide *)
End bytes.
(* end hide *)


(* begin hide *)
Module integer_bytes.
Import Math.bytes.
(** * impl.theory.bytes: big-endian byte-string <-> Z conversion *)
(** Copyright (C) 2026 remix7531
    SPDX-License-Identifier: MIT *)

(** Pure [Z] model of the big-endian byte (de)serialization performed by
    [secp256k1_read_be64] / [secp256k1_write_be64] and, lifted to 32 bytes, by
    [secp256k1_scalar_set_b32] / [secp256k1_scalar_get_b32].  No VST, no word
    size: a byte list is most-significant-first.  The heavier bridge to the
    64-bit-limb evaluator ([eval4]/[limb]) is left to the proof phase. *)



Open Scope Z_scope.

(* ================================================================= *)
(** ** Encode/decode definitions -- [Z_of_be_bytes] / [be_bytes_of_Z]. *)

(** Decode a big-endian byte list (head = most significant) to a [Z]. *)
Definition Z_of_be_bytes (bs : list Z) : Z :=
  fold_left (fun acc b => acc * 256 + b) bs 0.

(** Encode the low [n] bytes of [v], big-endian (head = most significant). *)
Fixpoint be_bytes_of_Z (v : Z) (n : nat) : list Z :=
  match n with
  | O => []
  | S k => be_bytes_of_Z (v / 256) k ++ [v mod 256]
  end.

(** Removing one low byte leaves a value that fits the remaining
    bytes. *)
Lemma byte_quotient_range : forall (n : nat) (v : Z),
  0 <= v < 2 ^ (8 * Z.of_nat (S n)) ->
  0 <= v / 256 < 2 ^ (8 * Z.of_nat n).
Proof.
  intros n v range.
  split.
  - (* conjunct 0: quotient is nonnegative *)
    apply Z.div_pos; lia.
  - (* conjunct 1: quotient fits the remaining bytes *)
    apply Z.div_lt_upper_bound.
    + (* byte radix is positive *)
      lia.
    + (* original bound scales by one byte *)
      rewrite Nat2Z.inj_succ in range.
      replace (8 * Z.succ (Z.of_nat n))
        with (8 * Z.of_nat n + 8) in range by lia.
      rewrite Z.pow_add_r in range by lia.
      replace (2 ^ 8) with 256 in range by reflexivity.
      nia.
Qed.


(* ================================================================= *)
(** ** Checked byte arrays agree with integer lists. *)

(** The checked encoder constructs one byte at a time by the same
    recursion as [be_bytes_of_Z]. These lemmas connect byte arrays to
    the integer lists used by memory contracts. *)

Lemma bytes_Z_of_Z : forall (n : nat) (v : Z)
    (range : 0 <= v < 2 ^ (8 * Z.of_nat n)),
  bytes_Z (bytes_of_Z v n range) = be_bytes_of_Z v n.
Proof.
  induction n as [|k induction]; intros v range.
  - (* zero bytes *)
    reflexivity.
  - (* extract the low byte *)
    cbn [bytes_of_Z bytes.encode_bytes be_bytes_of_Z].
    unfold bytes_Z in *.
    cbn [array_snoc array_list].
    pose proof (byte_quotient_range k v range) as quotient_range.
    rewrite map_app.
    rewrite induction by exact quotient_range.
    f_equal.
Qed.

Lemma Z_of_byte_list_spec : forall bs : list (Word 8),
  Z_of_byte_list bs = Z_of_be_bytes (map word_val bs).
Proof.
  intros bs.
  unfold Z_of_byte_list, Z_of_be_bytes.
  generalize 0.
  induction bs as [|b bs IH]; intros acc.
  - (* No bytes leave the accumulator unchanged. *)
    reflexivity.
  - (* Both decoders consume the same next byte. *)
    apply IH.
Qed.

(* ================================================================= *)
(** ** Length and range of [be_bytes_of_Z]. *)

(** [be_bytes_of_Z v n] has exactly [n] bytes. *)
Lemma be_bytes_of_Z_length : forall n v, length (be_bytes_of_Z v n) = n.
Proof.
  induction n; intros v.
  - (* Zero output bytes form the empty list. *)
    reflexivity.
  - (* The low byte extends the encoded prefix by one. *)
    simpl.
    rewrite length_app.
    rewrite IHn.
    simpl.
    lia.
Qed.

(** Same, as a [Zlength] fact (the form VST's [tarray] reasoning wants). *)
Lemma be_bytes_of_Z_Zlength : forall n v,
  Zlength (be_bytes_of_Z v n) = Z.of_nat n.
Proof.
  intros n v.
  rewrite Zlength_correct.
  rewrite be_bytes_of_Z_length.
  reflexivity.
Qed.

(** Every encoded byte [b] satisfies [0 <= b < 256]. *)
Lemma be_bytes_of_Z_range : forall n v,
  Forall (fun b => 0 <= b < 256) (be_bytes_of_Z v n).
Proof.
  induction n; intros v.
  - (* The empty encoding has no range obligations. *)
    constructor.
  - (* Both the prefix and the low byte must fit. *)
    simpl.
    apply Forall_app.
    split.
    + (* The prefix already satisfies every byte bound. *)
      apply IHn.
    + (* Reduction modulo 256 bounds the low byte. *)
      constructor; [| constructor].
      apply Z.mod_pos_bound.
      lia.
Qed.

(* ================================================================= *)
(** ** Decode algebra -- [Z_of_be_bytes] accumulator/append/bound lemmas. *)

(** The big-endian accumulator [fold_left] started at an arbitrary [a]
    factors as [a * 256^len + (fold from 0)].  This is the workhorse for
    the append and bound lemmas below. *)
Lemma be_fold_left_acc : forall (bs : list Z) (a : Z),
  fold_left (fun acc b => acc * 256 + b) bs a
  = a * 256 ^ Z.of_nat (length bs)
    + fold_left (fun acc b => acc * 256 + b) bs 0.
Proof.
  induction bs as [|b bs IH]; intros a.
  - (* An empty suffix contributes zero. *)
    simpl.
    lia.
  - (* One more byte scales the suffix weight by 256. *)
    simpl length.
    rewrite Nat2Z.inj_succ.
    rewrite Z.pow_succ_r by lia.
    cbn [fold_left].
    rewrite (IH (a * 256 + b)).
    rewrite (IH (0 * 256 + b)).
    lia.
Qed.

(** Big-endian decode distributes over append (head = most significant):
    the prefix is scaled by [256^(length of the suffix)]. *)
Lemma Z_of_be_bytes_app : forall (bs1 bs2 : list Z),
  Z_of_be_bytes (bs1 ++ bs2)
  = Z_of_be_bytes bs1 * 256 ^ Z.of_nat (length bs2) + Z_of_be_bytes bs2.
Proof.
  intros bs1 bs2.
  unfold Z_of_be_bytes.
  rewrite fold_left_app.
  rewrite (be_fold_left_acc bs2 (fold_left (fun acc b => acc * 256 + b) bs1 0)).
  reflexivity.
Qed.

(** Encoding and then decoding a fitting integer returns that integer. *)
Lemma Z_of_be_bytes_of_Z : forall (n : nat) (v : Z),
  0 <= v < 2 ^ (8 * Z.of_nat n) ->
  Z_of_be_bytes (be_bytes_of_Z v n) = v.
Proof.
  induction n as [|n induction]; intros v range.
  - (* zero bytes imply zero value *)
    cbn [be_bytes_of_Z Z_of_be_bytes].
    change (0 <= v < 1) in range.
    destruct range as [nonnegative upper_bound].
    assert (v = 0) by lia.
    subst v.
    reflexivity.
  - (* decode the prefix and low byte *)
    cbn [be_bytes_of_Z].
    rewrite Z_of_be_bytes_app.
    cbn [length Z_of_be_bytes fold_left].
    rewrite induction by apply (byte_quotient_range n v range).
    change (v / 256 * 256 + v mod 256 = v).
    rewrite Z.mul_comm.
    symmetry.
    apply Z.div_mod.
    lia.
Qed.

(* end hide *)

(** #<!-- begin appendix --># *)
(** ** A.6 Encoding Preserves Values *)

(** Encoding must preserve the integer, including leading zero bytes.
    The first proof connects the checked arrays to the integer-list
    computation, whose division and remainder steps reconstruct the
    input. The second shows that a word survives the same round trip.
    Neither result depends on a particular test vector. *)
Lemma Z_of_bytes_of_Z : forall (n : nat) (v : Z)
    (range : 0 <= v < 2 ^ (8 * Z.of_nat n)),
  Z_of_bytes (bytes_of_Z v n range) = v.
Proof.
  intros n v range.
  unfold Z_of_bytes.
  rewrite Z_of_byte_list_spec.
  change (Z_of_be_bytes (bytes_Z (bytes_of_Z v n range)) = v).
  rewrite bytes_Z_of_Z.
  apply Z_of_be_bytes_of_Z.
  exact range.
Qed.

(** Words are determined by their integer projection. *)
Lemma word_val_inj : forall (width : nat) (left right : Word width),
  word_val left = word_val right -> left = right.
Proof.
  intros width [left left_range] [right right_range] values_equal.
  cbn in values_equal.
  subst right.
  f_equal.
  apply proof_irrelevance.
Qed.

(** A byte-aligned word survives its byte codec unchanged. *)
Lemma word_of_bytes_to_bytes : forall (n : nat) (word : Word (8 * n)),
  word_of_bytes (word_to_bytes word) = word.
Proof.
  intros n word.
  apply word_val_inj.
  cbn [word_of_bytes word_of_Z].
  unfold word_to_bytes.
  apply Z_of_bytes_of_Z.
Qed.

(** #<!-- end appendix --># *)

(* begin hide *)
(** A big-endian byte list of length [n], with every byte between zero
    and 255, decodes to an integer [v] satisfying [0 <= v < 256^n]. *)
Lemma Z_of_be_bytes_bound : forall (l : list Z),
  Forall (fun b => 0 <= b < 256) l ->
  0 <= Z_of_be_bytes l < 256 ^ Z.of_nat (length l).
Proof.
  intros l Hl.
  unfold Z_of_be_bytes.
  induction l as [|x l IH].
  - (* The empty byte list represents zero. *)
    simpl.
    lia.
  - (* A bounded high byte extends a bounded suffix. *)
    inversion Hl as [|y ys Hx Hys]; subst.
    specialize (IH Hys).
    simpl length.
    rewrite Nat2Z.inj_succ, Z.pow_succ_r by lia.
    cbn [fold_left].
    rewrite (be_fold_left_acc l (0 * 256 + x)).
    assert (0 <= 256 ^ Z.of_nat (length l)) by (apply Z.pow_nonneg; lia).
    nia.
Qed.

(** A big-endian decode of nonnegative bytes is nonnegative -- the
    nonnegative half of [Z_of_be_bytes_bound], kept as its own lemma
    for the [scalar_set_b32_seckey] use site. *)
Lemma Z_of_be_bytes_nonneg : forall bs,
  Forall (fun b => 0 <= b < 256) bs ->
  0 <= Z_of_be_bytes bs.
Proof.
  intros bs Hall.
  exact (proj1 (Z_of_be_bytes_bound bs Hall)).
Qed.

End integer_bytes.
(* end hide *)


(* begin hide *)
Module fermat.
Import Math.algebra.
(** * theory.integers.fermat: Fermat's little theorem, for any prime. *)
(** Copyright (C) 2026 remix7531
    SPDX-License-Identifier: MIT *)

(** Fermat little theorem supplies the inverse formula for a prime
    modulus. The field instances first accept primality as a hypothesis.
    The certificate modules later discharge it for the two fixed moduli.
    The proof specializes the Euler theorem from Coqprime. *)







Open Scope Z_scope.


(** Binary exponentiation reduces after each multiplication, avoiding
    construction of the unreduced power. *)

(** One [pow_mod] step per bit of the exponent, most-significant first. *)
Fixpoint pow_mod_pos (a : Z) (e : positive) (m : Z) : Z :=
  match e with
  | xH => a mod m
  | xO e' => let h := pow_mod_pos a e' m in (h * h) mod m
  | xI e' => let h := pow_mod_pos a e' m in (h * h * a) mod m
  end.

(** Modular exponentiation, with zero for negative exponents. *)
Definition pow_mod (a e m : Z) : Z :=
  match e with
  | Z0 => 1 mod m
  | Zpos p => pow_mod_pos a p m
  | Zneg _ => 0
  end.

(** [pow_mod_pos] stays inside [[0, m)] for a positive modulus. *)
Lemma pow_mod_pos_range : forall a e m, 0 < m -> 0 <= pow_mod_pos a e m < m.
Proof.
  intros a e m Hm.
  induction e as [e' _|e' _|]; simpl; apply Z.mod_pos_bound; lia.
Qed.

(** Modular exponentiation returns a residue for a positive modulus. *)
Lemma pow_mod_range : forall a e m, 0 < m -> 0 <= pow_mod a e m < m.
Proof.
  intros a e m Hm.
  destruct e as [|p|p]; simpl.
  - apply Z.mod_pos_bound; lia.
  - apply pow_mod_pos_range; lia.
  - lia.
Qed.

(** Reducing intermediate products preserves their residue. *)
Lemma pow_mod_sqr_mul_cong : forall x y n,
  (x mod n) * (x mod n) * y mod n = x * x * y mod n.
Proof.
  intros x y n.
  rewrite (Zmult_mod (x * x) y n).
  rewrite (Zmult_mod x x n).
  rewrite Zmult_mod_idemp_l.
  rewrite Zmult_mod_idemp_r.
  reflexivity.
Qed.

(** Binary exponentiation agrees with integer exponentiation modulo [m]. *)
Lemma pow_mod_pos_spec : forall a e m,
  pow_mod_pos a e m = a ^ (Z.pos e) mod m.
Proof.
  intros a e m.
  induction e as [e' IH|e' IH|].
  - (* Restrict reduction to preserve the [Z.pos] form used by the rewrites. *)
    cbn [pow_mod_pos].
    rewrite IH.
    rewrite Pos2Z.inj_xI.
    replace (2 * Z.pos e' + 1) with (Z.pos e' + Z.pos e' + 1) by lia.
    rewrite (Z.pow_add_r a (Z.pos e' + Z.pos e') 1) by lia.
    rewrite (Z.pow_add_r a (Z.pos e') (Z.pos e')) by lia.
    rewrite Z.pow_1_r.
    apply pow_mod_sqr_mul_cong.
  - (* e = xO e' : even exponent, a plain square *)
    cbn [pow_mod_pos].
    rewrite IH.
    rewrite Pos2Z.inj_xO.
    replace (2 * Z.pos e') with (Z.pos e' + Z.pos e') by lia.
    rewrite (Z.pow_add_r a (Z.pos e') (Z.pos e')) by lia.
    symmetry.
    apply Zmult_mod.
  - (* e = xH : base case *)
    cbn [pow_mod_pos].
    rewrite Z.pow_1_r.
    reflexivity.
Qed.

(** Modular exponentiation agrees with [Z.pow] for nonnegative exponents. *)
Lemma pow_mod_spec : forall a e m : Z, 0 <= e -> pow_mod a e m = a ^ e mod m.
Proof.
  intros a e m He.
  destruct e as [|q|q].
  - (* zero exponent *)
    reflexivity.
  - (* positive exponent *)
    apply pow_mod_pos_spec.
  - (* negative exponent contradicts the precondition *)
    lia.
Qed.

(** An integer strictly between [0] and a prime is prime to it. *)
Lemma rel_prime_of_range : forall p a : Z, prime p -> 0 < a < p -> rel_prime a p.
Proof.
  intros p a Hp Ha.
  apply rel_prime_le_prime.
  - (* the upper endpoint is prime *)
    exact Hp.
  - (* the base lies inside that endpoint *)
    lia.
Qed.

(** Fermat's little theorem: [a^(p-1) = 1 mod p] for [a] prime to [p]. *)
Lemma fermat_little : forall p a : Z,
  prime p -> rel_prime a p -> a ^ (p - 1) mod p = 1.
Proof.
  intros p a Hp Ha.
  assert (Hphi : phi p = p - 1).
  { apply prime_phi_n_minus_1.
    exact Hp. }
  (* Replace the prime's totient before applying Euler's theorem. *)
  rewrite <- Hphi.
  apply phi_power_is_1.
  - (* the prime modulus is positive *)
    pose proof (prime_ge_2 p Hp).
    lia.
  - (* the base is relatively prime to the modulus *)
    exact Ha.
Qed.

(** The inverse law in the shape the field instances need: [a^(p-2) * a = 1]
    for [0 < a < p]. *)
Lemma pow_mod_inverse : forall p a : Z,
  prime p -> 0 < a < p -> (pow_mod a (p - 2) p * a) mod p = 1.
Proof.
  intros p a Hp Ha.
  pose proof (prime_ge_2 p Hp) as H2.
  rewrite pow_mod_spec by lia.
  rewrite Zmult_mod_idemp_l.
  rewrite Z.mul_comm.
  rewrite <- Z.pow_succ_r by lia.
  replace (Z.succ (p - 2)) with (p - 1) by lia.
  apply fermat_little.
  - (* the modulus is prime *)
    exact Hp.
  - (* the base is relatively prime to the modulus *)
    apply rel_prime_of_range.
    + (* the modulus is prime *)
      exact Hp.
    + (* the base lies in the required range *)
      exact Ha.
Qed.

(** The same inverse law over [Z.pow]: the shape the generic [power']
    reduces to through [pow_hom] below. *)
Lemma pow_inverse : forall p a : Z,
  prime p -> 0 < a < p -> (a ^ (p - 2) mod p * a) mod p = 1.
Proof.
  intros p a Hp Ha.
  pose proof (prime_ge_2 p Hp) as H2.
  rewrite Zmult_mod_idemp_l, Z.mul_comm, <- Z.pow_succ_r by lia.
  replace (Z.succ (p - 2)) with (p - 1) by lia.
  apply fermat_little.
  - (* the modulus is prime *)
    exact Hp.
  - (* the range makes the base relatively prime *)
    apply rel_prime_of_range.
    + (* the modulus is prime *)
      exact Hp.
    + (* the base lies in the required range *)
      exact Ha.
Qed.

(** [algebra]'s exponentiation by squaring, read through a residue
    map: if [f] sends the carrier's product to the product of residues mod
    [m], it sends [power' a (Npos e)] to [f a ^ e mod m]. Stated for any
    carrier, so that [field.v] and [scalar.v] use it at [fe_val] and
    [scalar_val]. *)
Lemma pow_pos_hom : forall (A : Type) (MulA : Mul A A A) (OneA : One A)
    (f : A -> Z) (m : Z),
  0 < m ->
  (forall x : A, 0 <= f x < m) ->
  (forall x y : A, f (mul x y) = (f x * f y) mod m) ->
  forall (a : A) (e : positive),
    f (power' a (Npos e)) = f a ^ Zpos e mod m.
Proof.
  intros A MulA OneA f m Hm Hrange Hmul a e.
  induction e as [e IH|e IH|].
  - (* odd exponent *)
    change (f (mul a (mul (power' a (Npos e)) (power' a (Npos e)))) =
      f a ^ Zpos (xI e) mod m).
    rewrite Hmul, Hmul, IH, <- Zmult_mod, Zmult_mod_idemp_r.
    replace (Zpos (xI e)) with (Zpos e + Zpos e + 1) by lia.
    rewrite !Z.pow_add_r, Z.pow_1_r by lia.
    f_equal; ring.
  - (* even exponent *)
    change (f (mul (power' a (Npos e)) (power' a (Npos e))) =
      f a ^ Zpos (xO e) mod m).
    rewrite Hmul, IH, <- Zmult_mod.
    replace (Zpos (xO e)) with (Zpos e + Zpos e) by lia.
    rewrite Z.pow_add_r by lia.
    reflexivity.
  - (* exponent one *)
    change (f a = f a ^ 1 mod m).
    rewrite Z.pow_1_r, Z.mod_small by apply Hrange.
    reflexivity.
Qed.

(** The same for every natural exponent, with [Z.of_N e] on the integer
    side. The extra premise says that the carrier's [one] maps to integer
    one, which is the zero exponent case. *)
Lemma pow_hom : forall (A : Type) (MulA : Mul A A A) (OneA : One A)
    (f : A -> Z) (m : Z),
  0 < m ->
  (forall x : A, 0 <= f x < m) ->
  f one = 1 ->
  (forall x y : A, f (mul x y) = (f x * f y) mod m) ->
  forall (a : A) (e : N), f (power' a e) = f a ^ Z.of_N e mod m.
Proof.
  intros A MulA OneA f m Hm Hrange Hone Hmul a e.
  destruct e as [|q].
  - (* zero exponent *)
    change (f one = 1 mod m).
    rewrite Hone.
    symmetry.
    apply Z.mod_small.
    pose proof (Hrange one).
    lia.
  - (* positive exponent *)
    apply pow_pos_hom; assumption.
Qed.

End fermat.
(* end hide *)


(* begin hide *)
Module field.
Import Math.algebra.
Import Math.bytes.
Import Math.fermat.
(* end hide *)
(** * 3. The Coordinate Field *)

(** A curve coordinate is a residue modulo a prime [p]. Addition and
    multiplication wrap modulo [p], and every nonzero value has an
    inverse. These are the field operations needed by the curve
    equation.

    We represent each residue by its unique integer from zero to
    [p - 1]. This keeps the mathematical operations independent of
    machine limbs, carry propagation, and delayed reduction. The C
    verification connects its memory representation to this value. *)

(* begin hide *)


(* end hide *)

(* begin hide *)
Open Scope Z_scope.
(* end hide *)

(* ================================================================= *)
(** ** 3.1 The Prime *)

(** The coordinate modulus is [p = 2^256 - 2^32 - 977], the prime
    specified in {{https://www.secg.org/sec2-v2.pdf#page=13}SEC 2
    section 2.4.1}. We call it the coordinate prime to distinguish it
    from the group order [n]. *)

Definition secp256k1_P : Z := 2 ^ 256 - 2 ^ 32 - 977.

(** Every constructed value must lie between [0] and [p - 1].
    Reduction with [mod p] supplies this range because [p] is
    positive. The explicit constants supply the remaining bounds. *)

(* begin hide *)
Local Obligation Tactic :=
  (intros; try apply Z.mod_pos_bound; unfold secp256k1_P; lia).
(* end hide *)

(** The repeated range obligations are hidden. A result outside the
    canonical range would make its definition fail. *)

(* ================================================================= *)
(** ** 3.2 Field Elements *)

(** Because [p] is prime, its integer residues form a field. [Fe]
    stores a representative together with a proof that it is
    canonical. Any function producing an [Fe] must establish this
    bound, so callers cannot accidentally construct an unreduced
    coordinate. *)

Record Fe := mkFe {
  fe_val : Z;
  fe_range : 0 <= fe_val < secp256k1_P
}.
Coercion fe_val : Fe >-> Z.

(** The _canonical representative_ determines a field value. Its
    range evidence does not distinguish two values with the same
    representative. This follows from _proof irrelevance_, rather than
    from erasing proofs during execution.

    The lemma [fe_eq_ext] lets us prove equality of field values by
    proving equality of their integer representatives. *)

Lemma fe_eq_ext (a b : Fe) :
  fe_val a = fe_val b -> a = b.
Proof.
  destruct a as [va Ha], b as [vb Hb].
  simpl.
  intros ->.
  f_equal; apply proof_irrelevance.
Qed.

(** The scope [fe_scope], written with the key [F], distinguishes
    field literals from integer literals. *)

Declare Scope fe_scope.
Delimit Scope fe_scope with F.
Bind Scope fe_scope with Fe.

(* ================================================================= *)
(** ** 3.3 Arithmetic *)

(** Arithmetic operates on integer representatives and then reduces
    modulo [p]. Reduction selects the unique representative in the
    canonical range. These formulas need no machine limbs or carry
    bounds. *)

(** The checked constructor keeps a representative only when its range
    is proved. The reducing helper instead accepts any integer, reduces
    it modulo the field modulus, and supplies the range evidence. *)

Program Definition fe_reduce (value : Z) : Fe :=
  mkFe (value mod secp256k1_P) _.

(** Modular addition computes [(a + b) mod p]. *)
Definition fe_add (a b : Fe) : Fe :=
  fe_reduce (a + b).

(** Modular negation computes [(p - a) mod p]. *)
Definition fe_negate (a : Fe) : Fe :=
  fe_reduce (secp256k1_P - a).

(** Modular multiplication computes [(a * b) mod p]. *)
Definition fe_mul (a b : Fe) : Fe :=
  fe_reduce (a * b).

(** Modular squaring computes [(a * a) mod p]. *)
Definition fe_sqr (a : Fe) : Fe :=
  fe_reduce (a * a).

(** Adding an integer computes [(a + k) mod p]. *)
Definition fe_add_int (a : Fe) (k : Z) : Fe :=
  fe_reduce (a + k).

(** Multiplication by an integer computes [(a * k) mod p]. *)
Definition fe_mul_int (a : Fe) (k : Z) : Fe :=
  fe_reduce (a * k).

(** Modular halving multiplies by [inv2 = (p + 1) / 2]. Since [p] is
    odd, [2 * inv2 = 1 mod p]. For example, modulo [7] the half of
    [3] is [5], since [2 * 5 = 3 mod 7]. *)
Program Definition fe_half (a : Fe) : Fe :=
  mkFe ((a * ((secp256k1_P + 1) / 2)) mod secp256k1_P) _.

(** The following instances connect the generic symbols [+], [-] and
    [*] to coordinate arithmetic. Subtraction is addition of the
    additive inverse. *)

Definition Fe_add : Add Fe := fe_add.
(* begin hide *)
#[export] Existing Instance Fe_add.
(* end hide *)

Definition Fe_neg : Neg Fe := fe_negate.
(* begin hide *)
#[export] Existing Instance Fe_neg.
(* end hide *)

Definition Fe_mul : Mul Fe Fe Fe := fe_mul.
(* begin hide *)
#[export] Existing Instance Fe_mul.
(* end hide *)

(* ================================================================= *)
(** ** 3.4 Distinguished Elements *)

(** Zero and one are the additive and multiplicative identities. The
    boolean tests inspect canonical representatives, so their answers
    depend only on the represented field element. *)

(** The field zero. *)
Program Definition fe_zero : Fe := mkFe 0 _.
Notation "0" := fe_zero : fe_scope.

(** The field one. *)
Program Definition fe_one : Fe := mkFe 1 _.
Notation "1" := fe_one : fe_scope.

(** [fe_is_zero] decides whether [a] represents zero. *)
Definition fe_is_zero (a : Fe) : bool := Z.eqb a 0.

(** [fe_is_odd] reports the parity of the canonical representative.
    Choosing one parity distinguishes a point from its negation when
    only an x coordinate is encoded. *)
Definition fe_is_odd (a : Fe) : bool := Z.odd a.

(** [fe_eqb] computes equality of canonical representatives. By
    [fe_eq_ext], this is also equality of field elements. *)
Definition fe_eqb (a b : Fe) : bool := Z.eqb a b.

(** These instances connect the generic constants and equality symbol
    to [fe_zero], [fe_one] and [fe_eqb]. *)

Definition Fe_zero : Zero Fe := fe_zero.
(* begin hide *)
#[export] Existing Instance Fe_zero.
(* end hide *)

Definition Fe_one : One Fe := fe_one.
(* begin hide *)
#[export] Existing Instance Fe_one.
(* end hide *)

Definition Fe_eqb : Eqb Fe := fe_eqb.
(* begin hide *)
#[export] Existing Instance Fe_eqb.
(* end hide *)

(** Opening [math_scope] makes the generic symbols denote field
    arithmetic below. The suffix [%Z] selects integer notation for an
    expression whose type would otherwise be ambiguous. *)

(* begin hide *)
Local Open Scope math_scope.
(* end hide *)

(* ================================================================= *)
(** ** 3.5 The Additive Group *)

(** Addition forms a group. Associativity says that parentheses do not
    affect a sum. Zero is neutral, and adding the negation returns
    zero. Each proof first applies [fe_eq_ext], which reduces equality
    of field elements to equality of their integer representatives.
    The tactic [cbn] unfolds the small arithmetic definitions and
    reduces their projections. Modular identities then remove
    redundant inner reductions. The remaining goals are ordinary
    integer arithmetic. *)

Definition Fe_group : Group Fe.
Proof.
  constructor.
  - (* Folding the two inner reductions exposes associativity. *)
    intros x y z.
    apply fe_eq_ext.
    cbn [add Fe_add fe_val fe_add fe_reduce].
    rewrite Zplus_mod_idemp_r, Zplus_mod_idemp_l.
    f_equal; lia.
  - (* A canonical residue is unchanged by another reduction. *)
    intros x.
    apply fe_eq_ext.
    unfold zero, Fe_zero.
    cbn [add Fe_add fe_val fe_add fe_zero fe_reduce].
    rewrite Z.add_0_l.
    apply Z.mod_small, fe_range.
  - (* The unreduced sum of an element and its negation is [p]. *)
    intros x.
    apply fe_eq_ext.
    unfold zero, Fe_zero.
    cbn [add neg Fe_add Fe_neg fe_val fe_add fe_negate fe_zero fe_reduce].
    rewrite Zplus_mod_idemp_l.
    replace (secp256k1_P - fe_val x + fe_val x)%Z with secp256k1_P by lia.
    apply Z_mod_same_full.
Defined.
(* begin hide *)
#[export] Existing Instance Fe_group.
(* end hide *)

(** Coordinate addition is commutative because integer addition is
    commutative before the common reduction modulo [p]. *)

Lemma Fe_abelian :
  Abelian Fe.
Proof.
  intros x y.
  apply fe_eq_ext.
  cbn [add Fe_add fe_val fe_add fe_reduce].
  f_equal; lia.
Qed.

(* ================================================================= *)
(** ** 3.6 Inversion and Square Roots *)

(** Inversion and square roots can be computed with powers. The power
    operation uses exponentiation by squaring, which handles a large
    exponent with repeated squaring and selected multiplications. Each
    recursive step removes one exponent bit. Every result remains an
    [Fe]. *)

(** For nonzero [a], the little theorem of Fermat states
    [a ^ (p - 1) = 1 mod p]. Splitting off one factor gives
    [a * a ^ (p - 2) = 1 mod p]. Thus [p - 2] comes from the inverse
    law. It is not a special implementation shortcut.

    The named exponent uses [N]. The next equality checks that
    conversion from [Z] preserved the formula. Negative integers
    would otherwise convert to zero. The tactic [vm_compute]
    evaluates a closed expression using the virtual machine. Rocq
    checks the resulting equality. *)
Definition fe_inv_exponent : N := Z.to_N (secp256k1_P - 2).

Lemma fe_inv_exponent_spec :
  Z.of_N fe_inv_exponent = (secp256k1_P - 2)%Z.
Proof.
  vm_compute.
  reflexivity.
Qed.

(** The inverse is this power of [a]. Exponentiation by squaring
    computes it efficiently. The value at zero is zero, but division
    by zero still has no field inverse law. *)
Definition fe_inv (a : Fe) : Fe :=
  a ^ fe_inv_exponent.

(** The square-root exponent has the same exactness check. *)
Definition fe_sqrt_exponent : N := Z.to_N ((secp256k1_P + 1) / 4).

Lemma fe_sqrt_exponent_spec :
  Z.of_N fe_sqrt_exponent = ((secp256k1_P + 1) / 4)%Z.
Proof.
  vm_compute.
  reflexivity.
Qed.

(** A square root of [a] is an [r] such that [r * r = a]. Not every
    residue has one. Since [p = 3 mod 4], raising a square to
    [(p + 1) / 4] produces a root. The candidate is squared and
    compared with [a], so [Some r] certifies a successful calculation
    and [None] rejects a
    {{https://en.wikipedia.org/wiki/Quadratic_residue}nonresidue}. *)
Definition fe_sqrt (a : Fe) : option Fe :=
  let r := a ^ fe_sqrt_exponent in
  if r * r =? a then Some r else None.

(** The inverse instance gives [/ a] the meaning [fe_inv a]. Division
    by [b] is multiplication by [/ b]. *)

Definition Fe_inv : Inv Fe := fe_inv.
(* begin hide *)
#[export] Existing Instance Fe_inv.
(* end hide *)

(* ================================================================= *)
(** ** 3.7 The Field *)

(** A field combines the additive group with multiplication and
    inversion. The additive laws are supplied by [Fe_group] and
    [Fe_abelian]. For the multiplication laws, [fe_eq_ext] exposes the
    integer representatives, modular identities fold inner reductions,
    and [ring] proves the resulting polynomial equalities by
    normalizing both sides.

    The inverse law needs the hypothesis [Hp] that [p] is prime.
    [pow_hom] changes a power of [Fe] values into the corresponding
    integer power modulo [p]. [pow_inverse] then applies the little
    theorem of Fermat to a nonzero representative in the interval from
    [1] to [p - 1]. *)

Definition Fe_field (Hp : prime secp256k1_P) : Field Fe.
Proof.
  refine {| field_add_assoc := group_add_assoc;
            field_add_comm := Fe_abelian;
            field_add_zero := group_add_zero;
            field_add_inverse := group_add_inverse |}.
  - (* Associativity remains after redundant reductions are folded. *)
    intros x y z.
    apply fe_eq_ext.
    cbn [mul Fe_mul fe_val fe_mul fe_reduce].
    rewrite Zmult_mod_idemp_r, Zmult_mod_idemp_l.
    f_equal; ring.
  - (* Commutativity follows from the integer product. *)
    intros x y.
    apply fe_eq_ext.
    cbn [mul Fe_mul fe_val fe_mul fe_reduce].
    f_equal; ring.
  - (* Multiplication by one preserves a canonical residue. *)
    intros x.
    apply fe_eq_ext.
    unfold one, Fe_one.
    cbn [mul Fe_mul fe_val fe_mul fe_one fe_reduce].
    rewrite Z.mul_1_l.
    apply Z.mod_small, fe_range.
  - (* Folding modular reductions exposes integer distributivity. *)
    intros x y z.
    apply fe_eq_ext.
    cbn [add mul Fe_add Fe_mul fe_val fe_mul fe_add fe_reduce].
    rewrite Zmult_mod_idemp_r, Zplus_mod_idemp_l, Zplus_mod_idemp_r.
    f_equal; ring.
  - (* The canonical representatives of zero and one differ. *)
    intros H.
    apply (f_equal fe_val) in H.
    discriminate.
  - (* Fermat theorem supplies the inverse of a nonzero residue. *)
    intros a Ha.
    apply fe_eq_ext.
    unfold one, Fe_one.
    cbn [mul Fe_mul fe_val fe_mul fe_one fe_reduce].
    unfold inv, Fe_inv, fe_inv, pow, Power_N.
    assert (Hpower : forall e,
      fe_val (power' a e) = ((fe_val a ^ Z.of_N e) mod secp256k1_P)%Z).
    { apply (pow_hom Fe Fe_mul Fe_one fe_val secp256k1_P).
      + (* The modulus is positive. *)
        unfold secp256k1_P.
        lia.
      + (* Every value has a canonical representative. *)
        apply fe_range.
      + (* The field identity represents integer one. *)
        reflexivity.
      + (* Multiplication reduces the integer product. *)
        intros x y.
        reflexivity. }
    rewrite Hpower.
    rewrite fe_inv_exponent_spec.
    apply pow_inverse.
    + (* The caller supplies the checked primality certificate. *)
      exact Hp.
    + (* The nonzero canonical residue is at least [1] and below [p]. *)
      assert (Hnz : fe_val a <> 0)
        by (intros Hz; apply Ha, fe_eq_ext; exact Hz).
      pose proof (fe_range a).
      lia.
Defined.

(** The inverse definition is sealed after its algebraic law is
    established. *)

#[global] Opaque fe_inv.
#[global] Typeclasses Opaque Fe_inv.

(** Symbolically expanding [fe_inv] would expose hundreds of modular
    multiplications from its 256 bit exponent. [Opaque] prevents proof
    simplifiers from performing that expansion. Reasoning can use the
    field inverse law instead. Concrete evaluation with [vm_compute]
    can still execute the definition. *)

(* ================================================================= *)
(** ** 3.8 Byte Encoding *)

(** External encodings use 32 bytes in
    {{https://en.wikipedia.org/wiki/Endianness}big endian} order. The
    most significant byte comes first. For example, the representative
    [0x1234] is encoded with thirty leading zero bytes followed by
    [0x12] and [0x34]. Public keys and signature coordinates use this
    representation. *)

(** Every canonical field representative fits in 32 bytes because
    [p < 2^256]. The helper packages it as a [Word 256] for the
    generic word encoding. *)
Definition fe_encode_range (a : Fe) : Word 256.
Proof.
  refine (@mkWord 256 (fe_val a) _).
  pose proof (fe_range a).
  change (0 <= fe_val a < 2 ^ 256).
  unfold secp256k1_P in *.
  lia.
Defined.

(** Encoding writes the canonical representative [fe_val a]. *)
Definition Fe_encode : Encode Fe 32 := {|
  encode a := @word_to_bytes 32 (fe_encode_range a)
|}.
(* begin hide *)
#[export] Existing Instance Fe_encode.
(* end hide *)

(** Decoding is strict. It returns [Some] exactly when the bytes denote
    an integer below [p]. It returns [None] for [p] and every larger
    256 bit integer instead of reducing them to a different value. *)
Definition Fe_decode : Decode Fe 32 := {|
  decode bs :=
    let v := Z_of_bytes bs in
    match Z_le_dec 0 v, Z_lt_dec v secp256k1_P with
    | left Hlo, left Hhi => Some (mkFe v (conj Hlo Hhi))
    | _, _ => None
    end
|}.
(* begin hide *)
#[export] Existing Instance Fe_decode.
(* end hide *)

(** For example, the field value with representative [0x1234] becomes
    32 bytes ending in [0x12] and [0x34]. Decoding those bytes
    recovers the same value. An encoding of [p] is rejected, since
    [p] is outside the canonical range. *)

(* begin hide *)
End field.
(* end hide *)


(* begin hide *)
Module scalar.
Import Math.algebra.
Import Math.bytes.
Import Math.fermat.
(* end hide *)
(** * 4. The Scalar Field *)

(** A scalar is an integer residue modulo the group order [n]. This
    modulus is different from the coordinate prime [p]. Both values
    fit in 32 bytes, but the distinct types [Scalar] and [Fe] prevent
    mixing their arithmetic.

    This chapter defines scalar addition, negation, multiplication,
    halving, and inversion. The curve chapter connects these
    operations to point multiplication. In particular, it proves why
    adding the generator [n] times gives the identity. Here [n]
    denotes the group order, not the size of the coordinate field. *)

(* begin hide *)


(* end hide *)

(* begin hide *)
Open Scope Z_scope.
(* end hide *)

(* ================================================================= *)
(** ** 4.1 The Group Order *)

(** The scalar modulus is the group order [n] from
    {{https://www.secg.org/sec2-v2.pdf#page=13}SEC 2 section 2.4.1}.
    The standard uses this name for the order of its generator. Its
    primality makes the residues modulo [n] a field. *)

Definition secp256k1_N : Z :=
  0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEBAAEDCE6AF48A03BBFD25E8CD0364141.

(** Every constructed value must lie between [0] and [n - 1].
    Reduction with [mod n] supplies this range because [n] is
    positive. The explicit constant supplies the remaining bounds. *)
(* begin hide *)
Local Obligation Tactic :=
  (intros; try apply Z.mod_pos_bound; unfold secp256k1_N; lia).
(* end hide *)

(* ================================================================= *)
(** ** 4.2 Scalars *)

(** [Scalar] stores a canonical representative modulo [n] and the
    proof that it is in range. Any function producing a scalar must
    establish this invariant. *)

Record Scalar := mkScalar {
  scalar_val : Z;
  scalar_range : 0 <= scalar_val < secp256k1_N
}.
Coercion scalar_val : Scalar >-> Z.

(** As with [Fe], the canonical representative determines the value.
    A range proof does not distinguish two scalars with the same
    representative. [scalar_eq_ext] therefore reduces equality of
    [Scalar] values to ordinary integer equality. *)
Lemma scalar_eq_ext (a b : Scalar) :
  scalar_val a = scalar_val b -> a = b.
Proof.
  destruct a as [va Ha], b as [vb Hb].
  simpl.
  intros ->.
  f_equal; apply proof_irrelevance.
Qed.

(** The scope [scalar_scope], written with the key [S], distinguishes
    scalar literals from integer and coordinate literals. *)
Declare Scope scalar_scope.
Delimit Scope scalar_scope with S.
Bind Scope scalar_scope with Scalar.

(* ================================================================= *)
(** ** 4.3 Arithmetic *)

(** Arithmetic uses the integer representatives and reduces each
    answer modulo [n]. For a small example modulo [11], [8 + 7 = 4],
    [-8 = 3] and [8 * 7 = 1]. *)

(** The checked constructor keeps a representative only when its range
    is proved. The reducing helper instead accepts any integer, reduces
    it modulo the field modulus, and supplies the range evidence. *)

Program Definition scalar_reduce (value : Z) : Scalar :=
  mkScalar (value mod secp256k1_N) _.

(** Modular addition computes [(a + b) mod n]. *)
Definition scalar_add (a b : Scalar) : Scalar :=
  scalar_reduce (scalar_val a + scalar_val b).

(** Modular negation computes [(n - a) mod n]. *)
Definition scalar_negate (a : Scalar) : Scalar :=
  scalar_reduce (secp256k1_N - scalar_val a).

(** Modular multiplication computes [(a * b) mod n]. *)
Definition scalar_mul (a b : Scalar) : Scalar :=
  scalar_reduce (a * b).

(** Modular halving multiplies by [inv2 = (n + 1) / 2]. Since [n] is
    odd, [2 * inv2 = 1 mod n]. For example, modulo [11] the half of
    [7] is [9], since [2 * 9 = 7 mod 11]. *)
Program Definition scalar_half (a : Scalar) : Scalar :=
  mkScalar ((scalar_val a * ((secp256k1_N + 1) / 2)) mod secp256k1_N) _.

(** The following instances connect the generic symbols [+], [-] and
    [*] to scalar arithmetic. Halving remains a named operation. *)
Definition Scalar_add : Add Scalar := scalar_add.
(* begin hide *)
#[export] Existing Instance Scalar_add.
(* end hide *)

Definition Scalar_neg : Neg Scalar := scalar_negate.
(* begin hide *)
#[export] Existing Instance Scalar_neg.
(* end hide *)

Definition Scalar_mul : Mul Scalar Scalar Scalar := scalar_mul.
(* begin hide *)
#[export] Existing Instance Scalar_mul.
(* end hide *)

(* ================================================================= *)
(** ** 4.4 Distinguished Scalars *)

(** Zero and one are the additive and multiplicative identities. *)
Program Definition scalar_zero : Scalar := mkScalar 0 _.
Notation "0" := scalar_zero : scalar_scope.

(** The multiplicative identity. *)
Program Definition scalar_one : Scalar := mkScalar 1 _.
Notation "1" := scalar_one : scalar_scope.

(** [scalar_eqb] computes equality of canonical representatives. By
    [scalar_eq_ext], this is also equality of scalar values. *)
Definition scalar_eqb (a b : Scalar) : bool := Z.eqb (scalar_val a) (scalar_val b).

(** These instances connect the generic constants and equality symbol
    to [scalar_zero], [scalar_one] and [scalar_eqb]. *)
Definition Scalar_zero : Zero Scalar := scalar_zero.
(* begin hide *)
#[export] Existing Instance Scalar_zero.
(* end hide *)

Definition Scalar_one : One Scalar := scalar_one.
(* begin hide *)
#[export] Existing Instance Scalar_one.
(* end hide *)

Definition Scalar_eqb : Eqb Scalar := scalar_eqb.
(* begin hide *)
#[export] Existing Instance Scalar_eqb.
(* end hide *)

(** The notation scopes introduced for coordinates also distinguish
    scalar arithmetic from integer arithmetic in the proofs below. *)
(* begin hide *)
Local Open Scope math_scope.
(* end hide *)

(* ================================================================= *)
(** ** 4.5 The Additive Group *)

(** The proof follows the coordinate field pattern. [scalar_eq_ext]
    exposes integer representatives, [cbn] reduces the arithmetic
    definitions, and modular identities remove redundant reductions. *)

Definition Scalar_group : Group Scalar.
Proof.
  constructor.
  - (* Folding the two inner reductions exposes associativity. *)
    intros x y z.
    apply scalar_eq_ext.
    cbn [add Scalar_add scalar_val scalar_add scalar_reduce].
    rewrite Zplus_mod_idemp_r, Zplus_mod_idemp_l.
    f_equal; lia.
  - (* A canonical residue is unchanged by another reduction. *)
    intros x.
    apply scalar_eq_ext.
    unfold zero, Scalar_zero.
    cbn [add Scalar_add scalar_val scalar_add scalar_zero scalar_reduce].
    rewrite Z.add_0_l.
    apply Z.mod_small, scalar_range.
  - (* The unreduced sum of an element and its negation is [n]. *)
    intros x.
    apply scalar_eq_ext.
    unfold zero, Scalar_zero.
    cbn [add neg Scalar_add Scalar_neg scalar_val scalar_add scalar_negate scalar_zero scalar_reduce].
    rewrite Zplus_mod_idemp_l.
    replace (secp256k1_N - scalar_val x + scalar_val x)%Z with secp256k1_N by lia.
    apply Z_mod_same_full.
Defined.
(* begin hide *)
#[export] Existing Instance Scalar_group.
(* end hide *)

(** Scalar addition is commutative because integer addition is
    commutative before the common reduction modulo [n]. *)
Lemma Scalar_abelian :
  Abelian Scalar.
Proof.
  intros x y.
  apply scalar_eq_ext.
  cbn [add Scalar_add scalar_val scalar_add scalar_reduce].
  f_equal; lia.
Qed.

(* ================================================================= *)
(** ** 4.6 Inversion and the Field *)

(** For a nonzero scalar, the little theorem of Fermat gives
    [a ^ (n - 1) = 1 mod n]. Removing one factor shows that
    [a ^ (n - 2)] is its inverse. The argument is the same as for
    coordinates, with modulus [n] in place of [p]. *)

(** The exponent uses binary natural numbers. The equality below
    checks that converting the integer formula to [N] preserves its
    value. *)
Definition scalar_inv_exponent : N := Z.to_N (secp256k1_N - 2).

Lemma scalar_inv_exponent_spec :
  Z.of_N scalar_inv_exponent = (secp256k1_N - 2)%Z.
Proof.
  vm_compute.
  reflexivity.
Qed.

(** Exponentiation by squaring computes [a ^ (n - 2)]. Zero maps to
    zero. Every nonzero scalar maps to its multiplicative inverse. *)
Definition scalar_inv (a : Scalar) : Scalar :=
  a ^ scalar_inv_exponent.

Definition Scalar_inv : Inv Scalar := scalar_inv.
(* begin hide *)
#[export] Existing Instance Scalar_inv.
(* end hide *)

(** A field combines the additive group with multiplication and
    inversion. The additive laws are supplied by [Scalar_group] and
    [Scalar_abelian]. For the multiplication laws, [scalar_eq_ext]
    exposes the integer representatives, modular identities fold inner
    reductions, and [ring] proves the polynomial equalities as in the
    coordinate field.

    The inverse law needs the hypothesis [Hn] that [n] is prime.
    [pow_hom] changes a power of scalars into the corresponding integer
    power modulo [n]. [pow_inverse] then applies the little theorem of
    Fermat to a nonzero representative from [1] through [n - 1]. *)

Definition Scalar_field (Hn : prime secp256k1_N)
    : Field Scalar.
Proof.
  refine {| field_add_assoc := group_add_assoc;
            field_add_comm := Scalar_abelian;
            field_add_zero := group_add_zero;
            field_add_inverse := group_add_inverse |}.
  - (* Associativity remains after redundant reductions are folded. *)
    intros x y z.
    apply scalar_eq_ext.
    cbn [mul Scalar_mul scalar_val scalar_mul scalar_reduce].
    rewrite Zmult_mod_idemp_r, Zmult_mod_idemp_l.
    f_equal; ring.
  - (* Commutativity follows from the integer product. *)
    intros x y.
    apply scalar_eq_ext.
    cbn [mul Scalar_mul scalar_val scalar_mul scalar_reduce].
    f_equal; ring.
  - (* Multiplication by one preserves a canonical residue. *)
    intros x.
    apply scalar_eq_ext.
    unfold one, Scalar_one.
    cbn [mul Scalar_mul scalar_val scalar_mul scalar_one scalar_reduce].
    rewrite Z.mul_1_l.
    apply Z.mod_small, scalar_range.
  - (* Folding modular reductions exposes integer distributivity. *)
    intros x y z.
    apply scalar_eq_ext.
    cbn [add mul Scalar_add Scalar_mul scalar_val scalar_mul scalar_add scalar_reduce].
    rewrite Zmult_mod_idemp_r, Zplus_mod_idemp_l, Zplus_mod_idemp_r.
    f_equal; ring.
  - (* The canonical representatives of zero and one differ. *)
    intros H.
    apply (f_equal scalar_val) in H.
    discriminate.
  - (* Fermat theorem supplies the inverse of a nonzero residue. *)
    intros a Ha.
    apply scalar_eq_ext.
    unfold one, Scalar_one.
    cbn [mul Scalar_mul scalar_val scalar_mul scalar_one scalar_reduce].
    unfold inv, Scalar_inv, scalar_inv, pow, Power_N.
    assert (Hpower : forall e,
      scalar_val (power' a e) = ((scalar_val a ^ Z.of_N e) mod secp256k1_N)%Z).
    { apply (pow_hom Scalar Scalar_mul Scalar_one scalar_val secp256k1_N).
      + (* The modulus is positive. *)
        unfold secp256k1_N.
        lia.
      + (* Every value has a canonical representative. *)
        apply scalar_range.
      + (* The field identity represents integer one. *)
        reflexivity.
      + (* Multiplication reduces the integer product. *)
        intros x y.
        reflexivity. }
    rewrite Hpower.
    rewrite scalar_inv_exponent_spec.
    apply pow_inverse.
    + (* The caller supplies the checked primality certificate. *)
      exact Hn.
    + (* The nonzero canonical residue is at least [1] and below [n]. *)
      assert (Hnz : scalar_val a <> 0)
        by (intros Hz; apply Ha, scalar_eq_ext; exact Hz).
      pose proof (scalar_range a).
      lia.
Defined.

(** Symbolically expanding [scalar_inv] would expose hundreds of
    modular multiplications from its 256 bit exponent. [Opaque]
    prevents proof simplifiers from performing that expansion.
    Reasoning can use the field inverse law instead. Concrete
    evaluation with [vm_compute] can still execute the definition. *)

#[global] Opaque scalar_inv.
#[global] Typeclasses Opaque Scalar_inv.

(* ================================================================= *)
(** ** 4.7 Byte Encoding *)

(** External scalar encodings use 32 bytes in big endian order. A
    private key and the [s] part of a signature use the canonical
    encoding. A hash digest follows a different rule because every
    possible digest must yield a scalar, including digests at least
    [n]. *)

(** [scalar_of_bytes] reads a 32 byte big-endian integer and explicitly
    reduces it modulo [n]. This is the rule [int(h) mod n] used when a
    hash becomes a challenge scalar. *)
Program Definition scalar_of_bytes (bs : Array (Word 8) 32) : Scalar :=
  mkScalar (Z_of_bytes bs mod secp256k1_N) _.

(** Every canonical scalar representative fits in 32 bytes because
    [n < 2^256]. The helper packages it as a [Word 256] for the
    generic word encoding. *)
Definition scalar_encode_range (a : Scalar) : Word 256.
Proof.
  refine (@mkWord 256 (scalar_val a) _).
  pose proof (scalar_range a).
  change (0 <= scalar_val a < 2 ^ 256).
  unfold secp256k1_N in *.
  lia.
Defined.

(** Encoding writes the canonical representative. *)
Definition Scalar_encode : Encode Scalar 32 := {|
  encode a := @word_to_bytes 32 (scalar_encode_range a)
|}.
(* begin hide *)
#[export] Existing Instance Scalar_encode.
(* end hide *)

(** [Scalar_decode] is strict. It returns [Some] exactly when the bytes
    denote an integer below [n]. It returns [None] for [n] and every
    larger 256 bit integer. This preserves the overflow check used for
    externally supplied private keys and signature scalars. *)
Definition Scalar_decode : Decode Scalar 32 := {|
  decode bs :=
    let v := Z_of_bytes bs in
    match Z_le_dec 0 v, Z_lt_dec v secp256k1_N with
    | left Hlo, left Hhi => Some (mkScalar v (conj Hlo Hhi))
    | _, _ => None
    end
|}.
(* begin hide *)
#[export] Existing Instance Scalar_decode.
(* end hide *)

(** Scalars therefore have two deliberate byte conversion rules. A
    canonical encoding of [n] is rejected. Treating the same 32 bytes
    as a hash digest reduces them modulo [n], producing zero. *)

(* begin hide *)
End scalar.
(* end hide *)


(* begin hide *)
Module field_prime.
Import Math.field.
(* end hide *)

(** ** 4.8 Primality Certificates *)

(** {{https://github.com/thery/coqprime}Coqprime} is a Rocq library
    for certified primality. [PocklingtonRefl] uses _proof by
    reflection_. Its correctness theorem turns a successful boolean
    certificate check into a proof of [prime n]. A [vm_compute] can
    reduce this check to [true].

    [Pock_certif n a dec sqrt] is a Pocklington certificate in the
    Brillhart, Lehmer and Selfridge form. Here [n] is the candidate,
    [a] is a witness base, and [dec] lists prime factors of [n - 1]
    with their exponents. The auxiliary value [sqrt] supports a
    check that a certain integer is not a square. It is not the
    square root of [n].

    The factorisation need not be complete. The factored part can
    be only slightly larger than the cube root of [n], provided
    the other arithmetic checks also pass. The lists below include
    only the factors needed by these checks. The remaining cofactor
    need not be proved prime.

    Certificates form a list. A certificate resolves its factors
    against entries later in that list. A whole chain therefore fits
    in one lemma. [BasePrimes] supplies 5000 proved lemmas, from
    [prime2] through [prime48611]. They cover all primes from 2
    through 48611. Both chains end at these existing proofs.

    [Pocklington_refl] is itself proved in Rocq. The source of the
    factorisations does not enter the trust boundary. An inconsistent
    factorisation, a missing factor proof, or a composite candidate
    cannot establish the required checker equality.

    The closing tactic [vm_cast_no_check (refl_equal true)] skips its
    immediate conversion check. [Qed.] still checks the proof in the
    kernel. This avoids evaluating the same certificate twice. The
    [BigN] checker uses primitive 63-bit integer operations. Their
    axioms appear in the report from [make axioms]. *)

(** The comments name the two intermediate factors [Pa] and [Pb].
    These names are explanatory labels, not Rocq definitions. The
    factor list in each certificate stops once the checker has
    enough information. The full equations show what remains. *)

Local Open Scope positive_scope.

Lemma secp256k1_P_prime : prime secp256k1_P.
Proof.
  apply (Pocklington_refl
    (* P - 1 = 2 * Pa * 3 * 7 * 13441 *)
    (Pock_certif (Z.to_pos secp256k1_P) 3
      ((2, 1) ::
       (0x1DB8260E5E3B460A46A0088FCCF6A3A5936D75D89A776D4C0DA4F338AAFB, 1) :: nil)
      1)
    (* Pa - 1 = 2 * Pb * 3 * 5 * 29^2 * 31 * 7723 * 132896956044521568488119 *)
    ((Pock_certif 0x1DB8260E5E3B460A46A0088FCCF6A3A5936D75D89A776D4C0DA4F338AAFB 10
       ((2, 1) ::
        (0xC03A94B2D3E64419A05CD8CCBF987069, 1) :: nil)
       1) ::
     (* Pb - 1 = 2^3 * 1627 * 2657 * 4423 * 41201 * 7^2 * 11 * 96557 * 7240687 * 107590001 *)
     (Pock_certif 0xC03A94B2D3E64419A05CD8CCBF987069 3
       ((    2, 3) ::
        ( 1627, 1) ::
        ( 2657, 1) ::
        ( 4423, 1) ::
        (41201, 1) :: nil)
       0x2B441F3E4147C0) ::
     (* Every leaf is already proved in Coqprime BasePrimes. *)
     (Proof_certif     2 prime2)     ::
     (Proof_certif  1627 prime1627)  ::
     (Proof_certif  2657 prime2657)  ::
     (Proof_certif  4423 prime4423)  ::
     (Proof_certif 41201 prime41201) :: nil)).
  vm_cast_no_check (refl_equal true).
Qed.

(* begin hide *)
End field_prime.
Module order_prime.
Import Math.scalar.
Local Open Scope positive_scope.
(* end hide *)

(** The group order uses the same checker. Its intermediate factor
    is named [Na] in the comments. *)

Lemma secp256k1_N_prime : prime secp256k1_N.
Proof.
  apply (Pocklington_refl
    (* N - 1 = 2^6 * 149 * 631 * Na * 3 * 107361793816595537 * 341948486974166000522343609283189 *)
    (Pock_certif (Z.to_pos secp256k1_N) 7
      ((                  2, 6) ::
       (                149, 1) ::
       (                631, 1) ::
       (0x978C6F353C3889A79, 1) :: nil)
      0x3A09C70114BEF6E06C0648E)
    (* Na - 1 = 2^3 * 17 * 59 * 4051 * 120233 * 44706919 *)
    ((Pock_certif 0x978C6F353C3889A79 3
       ((   2, 3) ::
        (  17, 1) ::
        (  59, 1) ::
        (4051, 1) :: nil)
       0x32AB55E) ::
     (* Every leaf is already proved in Coqprime BasePrimes. *)
     (Proof_certif    2 prime2)    ::
     (Proof_certif   17 prime17)   ::
     (Proof_certif   59 prime59)   ::
     (Proof_certif  149 prime149)  ::
     (Proof_certif  631 prime631)  ::
     (Proof_certif 4051 prime4051) :: nil)).
  vm_cast_no_check (refl_equal true).
Qed.

(* begin hide *)
End order_prime.
(* end hide *)


(* begin hide *)
Module raw.
Export Math.algebra.
Export Math.field.
Export Math.scalar.
(** * theory.group.raw: unchecked coordinate formulas. *)
(** Copyright (C) 2026 remix7531
    SPDX-License-Identifier: MIT *)




Open Scope Z_scope.
Local Open Scope math_scope.


(* ================================================================= *)

(** ** Internal coordinate formulas *)

(** The internal coordinate type allows arbitrary field pairs. The
    public [Point] type adds validity evidence. Negation, doubling and
    addition below are the formulas whose closure proofs justify the
    public operations. *)

Inductive Point := PInf | PAff (x y : Fe).


Local Obligation Tactic := (intros; unfold secp256k1_P; lia).


Program Definition curve_b : Fe := mkFe 7 _.

Definition on_curve (a : Point) : Prop :=
  match a with
  | PInf => True
  | PAff x y => y * y = x * x * x + curve_b
  end.

(* ================================================================= *)

Definition point_eqb (a b : Point) : bool :=
  match a, b with
  | PInf, PInf => true
  | PAff x1 y1, PAff x2 y2 => (x1 =? x2) && (y1 =? y2)
  | _, _ => false
  end.
Definition Point_eqb : Eqb Point := point_eqb.

#[export] Existing Instance Point_eqb.


(* ================================================================= *)

Definition pneg (a : Point) : Point :=
  match a with
  | PInf => PInf
  | PAff x y => PAff x (- y)
  end.

(** A vertical tangent gives the identity. Otherwise its slope is
    [3*x^2 / (2*y)]. *)

Definition pdouble (a : Point) : Point :=
  match a with
  | PInf => PInf
  | PAff x y =>
      if fe_is_zero y then PInf
      else
        let lam := fe_mul_int (fe_sqr x) 3 / fe_mul_int y 2 in
        let x3 := fe_sqr lam - fe_mul_int x 2 in
        let y3 := lam * (x - x3) - y in
        PAff x3 y3
  end.

(** Equal points select doubling. Distinct points with equal x
    coordinates select the identity. The remaining case uses the
    chord slope [(y2-y1)/(x2-x1)]. *)

Definition padd (a b : Point) : Point :=
  match a, b with
  | PInf, _ => b
  | _, PInf => a
  | PAff x1 y1, PAff x2 y2 =>
      if x1 =? x2 then
        (if y1 =? y2 then pdouble a else PInf)
      else
        let lam := (y2 - y1) / (x2 - x1) in
        let x3 := fe_sqr lam - (x1 + x2) in
        let y3 := lam * (x1 - x3) - y1 in
        PAff x3 y3
  end.


Definition Point_add : Add Point := padd.

#[export] Existing Instance Point_add.

Definition Point_neg : Neg Point := pneg.

#[export] Existing Instance Point_neg.


(* ================================================================= *)

Fixpoint repeat_addition' (n : positive) (a : Point) : Point :=
  match n with
  | xH => a
  | xO m => pdouble (repeat_addition' m a)
  | xI m => a + pdouble (repeat_addition' m a)
  end.

Definition smul (n : Z) (a : Point) : Point :=
  match n with
  | Z0 => PInf
  | Zpos m => repeat_addition' m a
  | Zneg m => - repeat_addition' m a
  end.
Definition Point_smul : Mul Z Point Point := smul.

#[export] Existing Instance Point_smul.


Definition Point_smul_scalar : Mul Scalar Point Point :=
  fun k a => smul (scalar_val k) a.

#[export] Existing Instance Point_smul_scalar.


(* ================================================================= *)

(** ** B.2 Curve Constants *)

(** The generator coordinates are fixed by secp256k1. The bounds
    checks make both hexadecimal literals coordinate-field elements. *)

Program Definition G_x : Fe :=
  mkFe 0x79BE667EF9DCBBAC55A06295CE870B07029BFCDB2DCE28D959F2815B16F81798 _.

Program Definition G_y : Fe :=
  mkFe 0x483ADA7726A3C4655DA4FBFC0E1108A8FD17B448A68554199C47D08FFB10D4B8 _.


Definition G : Point := PAff G_x G_y.

Lemma on_curve_G : on_curve G.
Proof.
  apply fe_eq_ext.
  vm_compute.
  reflexivity.
Qed.

(* ================================================================= *)


(** The GLV field constant and its corresponding scalar. *)

Program Definition beta : Fe :=
  mkFe 0x7AE96A2B657C07106E64479EAC3434E99CF0497512F58995C1396C28719501EE _.

Definition secp256k1_lambda : Z :=
  0x5363AD4CC05C30E0A5261C028812645A122E22EA20816678DF02967C1B23BD72.


Lemma beta_cube_root_unity :
  beta * beta * beta = 1%F /\ beta <> 1%F.
Proof.
  split.
  - (* The cube of beta is the multiplicative identity. *)
    apply fe_eq_ext.
    vm_compute.
    reflexivity.
  - (* Beta itself is not the identity, so its order is three. *)
    intros H.
    apply (f_equal fe_val) in H.
    vm_compute in H.
    discriminate.
Qed.

Definition pmul_lambda (a : Point) : Point :=
  match a with
  | PInf => PInf
  | PAff x y => PAff (x * beta) y
  end.

End raw.
(* end hide *)


(* begin hide *)
Module residues.
Import Math.field.
Import Math.scalar.
Import Math.raw.
(** * theory.residues: equality and the defining properties of the residues. *)
(** Copyright (C) 2026 remix7531
    SPDX-License-Identifier: MIT *)

(** The residue operations carry range evidence. Their equality lemmas
    let proofs reason about the integer representatives. The negation
    and halving lemmas state the equations used by C contracts. *)



Open Scope Z_scope.

(* ================================================================= *)
(** ** Modulus bounds
    Both moduli are positive and below [2^256]. The scalar modulus is
    odd. These facts discharge range and parity conditions. *)

Lemma secp256k1_P_range : 0 < secp256k1_P < 2 ^ 256.
Proof. unfold secp256k1_P. lia. Qed.

Lemma secp256k1_N_range : 0 < secp256k1_N < 2 ^ 256.
Proof. unfold secp256k1_N. lia. Qed.

(** [n] is odd: what makes [2] a unit mod [n], hence [scalar_half] exact
    ([scalar_half_prop] below). *)
Lemma secp256k1_N_odd : Z.Odd secp256k1_N.
Proof.
  exists ((secp256k1_N - 1) / 2).
  vm_compute.
  reflexivity.
Qed.

(* ================================================================= *)
(** ** Equality of field elements is decidable. *)

(** Two field elements are equal exactly when their residues are, and
    residues are integers.  What [law]'s
    [on_curve_irrel] needs to apply [UIP_dec] to the curve equation. *)
Definition fe_eq_dec (a b : Fe) : {a = b} + {a <> b}.
Proof.
  destruct (Z.eq_dec (fe_val a) (fe_val b)) as [H|H].
  - left.
    apply fe_eq_ext.
    exact H.
  - right.
    intros Hc.
    apply H.
    rewrite Hc.
    reflexivity.
Defined.

(* ================================================================= *)
(** ** Point equality decides equality. *)

Lemma point_eqb_eq : forall a b : Point, point_eqb a b = true <-> a = b.
Proof.
  intros a b.
  split.
  - intros Heq.
    destruct a as [|x1 y1], b as [|x2 y2]; try discriminate.
    + reflexivity.
    + cbv [point_eqb eqb Fe_eqb fe_eqb] in Heq.
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
    + cbv [point_eqb eqb Fe_eqb fe_eqb].
      apply andb_true_iff.
      split.
      * apply Z.eqb_refl.
      * apply Z.eqb_refl.
Qed.

(* ================================================================= *)
(** ** Defining properties of the scalar operations. *)

(** Defining property of [scalar_negate]: it is THE additive inverse mod [n].
    Within [[0, n)] the property [(a + r) mod n = 0] determines [r] uniquely,
    so this is an equivalence with the [(n - a) mod n] construction, not a
    weakening.  Used by [secp256k1_scalar_split_lambda] to recover the
    [scalar_negate] value from the property-based [secp256k1_scalar_negate]
    postcondition. *)
Lemma scalar_negate_unique (a r : Scalar) :
  Z.modulo (Z.add (scalar_val a) (scalar_val r)) secp256k1_N = 0 ->
  r = scalar_negate a.
Proof.
  intros H.
  pose proof (scalar_range a) as Ha.
  pose proof (scalar_range r) as Hr.
  apply scalar_eq_ext.
  replace (scalar_val (scalar_negate a))
    with ((secp256k1_N - scalar_val a) mod secp256k1_N) by reflexivity.
  destruct (Z.eq_dec (scalar_val a) 0) as [Ha0|Ha0].
  - rewrite Ha0 in *. rewrite Z.add_0_l, Z.mod_small in H by lia.
    rewrite Z.sub_0_r, Z_mod_same_full. lia.
  - rewrite Z.mod_small by lia.
    apply Zmod_divides in H;[|lia].
    destruct H as [c Hc]. assert (0 < scalar_val a) by lia.
    assert (c = 1) by nia. subst c. lia.
Qed.

(** Forward direction of [scalar_negate_unique], used by the property-based
    [secp256k1_scalar_negate] body proof to discharge its postcondition. *)
Lemma scalar_negate_prop (a : Scalar) :
  Z.modulo (Z.add (scalar_val a) (scalar_val (scalar_negate a))) secp256k1_N = 0.
Proof.
  replace (scalar_val (scalar_negate a))
    with ((secp256k1_N - scalar_val a) mod secp256k1_N) by reflexivity.
  rewrite Zplus_mod_idemp_r.
  replace (scalar_val a + (secp256k1_N - scalar_val a)) with secp256k1_N by ring.
  apply Z_mod_same_full.
Qed.

(** Defining property of [scalar_half]: doubling it recovers [a] mod [n]
    (since [2] is a unit mod the odd modulus [n] -- [secp256k1_N_odd] -- so
    [a/2] is the unique solution in [[0, n)]).  Equivalent to the
    [a * 2^{-1} mod n] construction, not weaker. *)
Lemma scalar_half_prop (a : Scalar) :
  Z.modulo (Z.mul 2 (scalar_val (scalar_half a))) secp256k1_N = scalar_val a.
Proof.
  pose proof (scalar_range a) as Ha.
  replace (scalar_val (scalar_half a))
    with ((scalar_val a * ((secp256k1_N + 1) / 2)) mod secp256k1_N) by reflexivity.
  rewrite Zmult_mod_idemp_r.
  destruct secp256k1_N_odd as [h Hh].
  assert (Hdiv : secp256k1_N + 1 = 2 * ((secp256k1_N + 1) / 2)).
  { replace (secp256k1_N + 1) with (2 * (h + 1)) by lia.
    rewrite Z.mul_comm, Z_div_mult by lia.
    lia. }
  replace (2 * (scalar_val a * ((secp256k1_N + 1) / 2)))
    with (scalar_val a * (2 * ((secp256k1_N + 1) / 2))) by ring.
  rewrite <- Hdiv.
  replace (scalar_val a * (secp256k1_N + 1)) with (scalar_val a + scalar_val a * secp256k1_N) by ring.
  rewrite Z.mod_add by lia.
  apply Z.mod_small; lia.
Qed.

End residues.
(* end hide *)


(* begin hide *)
Module ell.
Import Math.fermat.
Import Math.raw.
Import Math.residues.
Import Math.field_prime.
(** * theory.group_ell: coqprime's elliptic group law, instantiated at [Fe]. *)
(** Copyright (C) 2026 remix7531
    SPDX-License-Identifier: MIT *)

(** Coqprime proves the Weierstrass group law over an abstract field.
    This module instantiates that field with [Fe] and transports the
    resulting addition law to the internal coordinate representation.
    Fermat little theorem supplies the inverse law. The transport
    proof checks every coordinate case used by addition.

    Coqprime is an external dependency. The assumption audit records
    the primitive integer and extensionality axioms used by these
    proofs. *)





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
       fe_zero fe_one fe_reduce];
  fe_mod_norm;
  f_equal;
  ring.

(* ================================================================= *)
(** ** [Fe] as a coqprime field -- [fe_sub] / [fe_div] / [Fe_ring_theory].

    [field_theory] wants subtraction and division as primitive operations;
    [field] has neither, so both are defined here in the shape the
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
    cbn [fe_val fe_add fe_zero fe_reduce].
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
    cbn [fe_val fe_mul fe_one fe_reduce].
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
    cbn [fe_val fe_add fe_negate fe_zero fe_reduce].
    rewrite sub_P_mod.
    rewrite addr_mod.
    rewrite Z.add_opp_diag_r.
    apply Zmod_0_l.
Qed.

(** Registering the ring makes [ring] work on [Fe] goals directly, here and in
    [theory.group_law]. *)
Add Ring Fe_ring : Fe_ring_theory.

(* ================================================================= *)
(** ** The inverse law -- what makes [fe_inv] an inverse. *)

(** [fe_inv] is a left inverse -- the [Finv_l] field obligation, and the one
    fact [theory.group_law]'s [padd_comm] really rests on.  It is the
    inverse law of [field]'s [Field] instance at the certified
    prime; [fe_inv] itself is sealed there and is never unfolded here. *)
Lemma fe_inv_l : forall a : Fe, a <> fe_zero -> fe_mul (fe_inv a) a = fe_one.
Proof.
  intros a Ha.
  exact (@field_multiply_inverse Fe _ _ _ _ _ _ (Fe_field secp256k1_P_prime) a Ha).
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

(** The curve's [a] coefficient: zero, as in [raw]. *)
Definition fe_a : Fe := fe_zero.

(** The curve's [b] coefficient: [raw]'s [curve_b], the same field
    element [on_curve] is written with. *)
Definition fe_b : Fe := curve_b.

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
    cbn [fe_val fe_zero fe_reduce].
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
  cbn [fe_val fe_negate fe_reduce] in Hy.
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
    [raw]'s [Point] does not, and [on_curve] is a separate predicate.
    So the two maps are asymmetric: [elt_to_point] is total, [point_to_elt]
    needs [on_curve a] as an argument.  That asymmetry is exactly why
    [padd_assoc] carries three [on_curve] hypotheses and [padd_comm] carries
    none. *)

(** The curve-point type of the instance. *)
Definition ECurve : Set := elt fe_one fe_add fe_mul fe_a fe_b.

(** coqprime's group operation at the instance. *)
Definition eadd (p q : ECurve) : ECurve := SMain.add Fe_ell_theory p q.

(** The curve equation in coqprime's shape. *)
Definition curve_eq (x y : Fe) : Prop :=
  SMain.pow fe_one fe_mul y 2
    = fe_add (fe_add (SMain.pow fe_one fe_mul x 3) (fe_mul fe_a x)) fe_b.

(** The model's [on_curve] and coqprime's constructor obligation are the same
    statement.  This is the only place the two curve equations meet. *)
Lemma on_curve_iff : forall x y : Fe, on_curve (PAff x y) <-> curve_eq x y.
Proof.
  intros x y.
  unfold on_curve, curve_eq, fe_a.
  cbn [SMain.pow].
  split.
  - intros H.
    apply (f_equal fe_val) in H.
    cbn [add mul Fe_add Fe_mul fe_val fe_add fe_mul curve_b fe_reduce] in H.
    fe_mod_norm_in H.
    apply fe_eq_ext.
    cbn [add mul Fe_add Fe_mul fe_val fe_add fe_mul fe_zero fe_b curve_b fe_reduce].
    fe_mod_norm.
    rewrite H.
    f_equal.
    ring.
  - intros H.
    apply (f_equal fe_val) in H.
    cbn [add mul Fe_add Fe_mul fe_val fe_add fe_mul fe_zero fe_b curve_b fe_reduce] in H.
    fe_mod_norm_in H.
    apply fe_eq_ext.
    cbn [add mul Fe_add Fe_mul fe_val fe_add fe_mul curve_b fe_reduce].
    fe_mod_norm.
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
  unfold padd, eqb, Fe_eqb, fe_eqb.
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
  unfold padd, eqb, Fe_eqb, fe_eqb.
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
  pattern p, q, (SMain.add Fe_ell_theory p q).
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
      unfold padd, eqb, Fe_eqb, fe_eqb.
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
      (* [apply f_equal2], not [f_equal]: the latter tries [reflexivity] on
         [fe_inv B = fe_inv B'], and deciding whether two inverses of
         different arguments are convertible unfolds the 256-step chain on
         both sides, exponentially.  The seal on [fe_inv] does not stop
         unification from trying; only never asking does. *)
      apply f_equal2.
      - ring.
      - apply f_equal.
        ring. }
    rewrite Hlam in Hx2, Hy2.
    subst x2 y2.
    unfold fe_sub, fe_a.
    cbn [SMain.pow].
    apply f_equal2.
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
    cbn [SMain.pow].
    apply f_equal2.
    + ring.
    + ring.
Qed.

(** Associativity on the source side, in the orientation [padd_assoc] wants
    (coqprime's [add_assoc] is stated the other way round).  Stating it here
    is what keeps [Coqprime.elliptic.SMain] out of [theory.group_law]'s import
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

    [theory.group_law]'s header records closure as DELIBERATELY NOT STATED
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
(** ** Facts needed for [padd_comm].

    [padd_comm] is NOT delivered by the transport (see the file header), so
    [theory.group_law] proves it directly.  The only real content of that proof
    is that [fe_inv] is a genuine inverse away from zero; these three lemmas
    plus [fe_inv_l] and the [Fe] ring are everything it uses. *)

(** A difference of residues vanishes only when the values agree. *)
Lemma fe_sub_zero : forall a b : Fe,
  fe_add a (fe_negate b) = fe_zero -> fe_val a = fe_val b.
Proof.
  intros a b H.
  apply (f_equal fe_val) in H.
  cbn [fe_val fe_add fe_negate fe_zero fe_reduce] in H.
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

End ell.
(* end hide *)


(* begin hide *)
Module law.
Import Math.algebra.
Import Math.field.
Import Math.raw.
Import Math.residues.
Import Math.ell.
(** * theory.group_law: the abelian-group properties of [raw]'s [padd]. *)
(** Copyright (C) 2026 remix7531
    SPDX-License-Identifier: MIT *)

(** The chord-and-tangent operation forms an abelian group on curve
    points. Binary scalar multiplication agrees with repeated addition
    and respects integer addition and multiplication. *)



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
    [theory.group_ell]). *)

(** Addition is commutative.  Unconditional: the chord slope is unchanged by
    swapping the two points, and the [x1 = x2] branches are symmetric by
    construction, so no [on_curve] hypothesis is needed.
    That unconditionality is also why coqprime's [add_comm] does not deliver
    this statement -- its points carry an on-curve proof -- so the argument is
    direct, over [theory.group_ell]'s field instance.  Its only real content is
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
        unfold padd, eqb, Fe_eqb, fe_eqb.
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
    Discharged by [theory.group_ell]: carry all three points across
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
(** ** The group -- [curve_group] / [curve_abelian].

    [padd_comm] and [padd_assoc] above are the two hard axioms; the rest of
    the [Group] interface is the identity ([padd_PInf_l]), closure
    ([ell]'s [padd_on_curve], plus [pneg_on_curve] below) and
    the inverse law ([padd_pneg_l] below), none of which needs the coqprime
    port. *)

(** A point together with the proof that it is on the curve.  This is the
    carrier: [padd] is only associative here.
    See https://wuille.net/posts/secp256k1-tutorial/#22-the-curve-group *)
Definition CurvePoint : Type := {a : Point | on_curve a}.

(** [on_curve] is proof-irrelevant: at infinity it is [True], and at an affine
    point it is an equation between two field elements, whose equality is
    decidable ([fe_eq_dec]), so [UIP_dec] applies.  So a [CurvePoint] is
    determined by its point. *)
Lemma on_curve_irrel : forall (a : Point) (p q : on_curve a), p = q.
Proof.
  intros a p q.
  destruct a as [|x y].
  - simpl in p, q.
    destruct p, q.
    reflexivity.
  - simpl in p, q.
    apply Eqdep_dec.UIP_dec.
    apply fe_eq_dec.
Qed.

(** Two curve points with the same underlying point are equal. *)
Lemma curve_point_eq : forall a b : CurvePoint, proj1_sig a = proj1_sig b -> a = b.
Proof.
  intros [a Ha] [b Hb] H.
  simpl in H.
  subst b.
  f_equal.
  apply on_curve_irrel.
Qed.

(** Negation preserves the curve equation: only [y] flips sign, and [y^2] does
    not see it. *)
Lemma pneg_on_curve : forall a : Point, on_curve a -> on_curve (pneg a).
Proof.
  intros a Ha.
  destruct a as [|x y].
  - exact I.
  - cbn [pneg on_curve] in Ha |- *.
    rewrite <- Ha.
    apply fe_eq_ext.
    cbn [mul neg Fe_mul Fe_neg fe_val fe_mul fe_negate fe_reduce].
    rewrite Zmult_mod_idemp_l.
    rewrite Zmult_mod_idemp_r.
    replace ((secp256k1_P - fe_val y) * (secp256k1_P - fe_val y))
      with (fe_val y * fe_val y + (secp256k1_P - 2 * fe_val y) * secp256k1_P) by ring.
    rewrite Z_mod_plus_full.
    reflexivity.
Qed.

(** The inverse law: a point plus its negation is the identity.  Both branches
    of [padd]'s equal-x case are covered -- the vertical chord when
    [y <> -y], and the tangent at a [y = 0] point, which [pdouble] sends to
    infinity.  No [on_curve] hypothesis is needed.
    See https://wuille.net/posts/secp256k1-tutorial/#221-the-group-operation *)
Lemma padd_pneg_l : forall a : Point, padd (pneg a) a = PInf.
Proof.
  intros a.
  destruct a as [|x y].
  - reflexivity.
  - unfold pneg, padd, eqb, Fe_eqb, fe_eqb, neg, Fe_neg.
    rewrite Z.eqb_refl.
    destruct (fe_val (fe_negate y) =? fe_val y) eqn:Hy.
    + apply Z.eqb_eq in Hy.
      assert (Hz : fe_val (fe_negate y) = 0).
      { rewrite Hy.
        apply fe_self_negate_zero.
        apply fe_eq_ext.
        symmetry.
        exact Hy. }
      unfold pdouble, fe_is_zero.
      rewrite Hz.
      reflexivity.
    + reflexivity.
Qed.

(** Doubling preserves the curve equation: on an affine point [pdouble a] is
    [padd a a] by [padd]'s equal-coordinates branch, and [padd] is closed. *)
Lemma pdouble_on_curve : forall a : Point, on_curve a -> on_curve (pdouble a).
Proof.
  intros a Ha.
  destruct a as [|x y].
  - exact I.
  - replace (pdouble (PAff x y)) with (padd (PAff x y) (PAff x y)).
    + apply padd_on_curve; exact Ha.
    + cbv [padd eqb Fe_eqb fe_eqb].
      rewrite !Z.eqb_refl.
      reflexivity.
Qed.

(** Double-and-add preserves the curve equation, step by step. *)
Lemma repeat_addition_binary_on_curve : forall (m : positive) (a : Point),
  on_curve a -> on_curve (repeat_addition' m a).
Proof.
  induction m as [m IH|m IH|]; intros a Ha; cbn [repeat_addition'].
  - apply padd_on_curve.
    + exact Ha.
    + apply pdouble_on_curve.
      apply IH.
      exact Ha.
  - apply pdouble_on_curve.
    apply IH.
    exact Ha.
  - exact Ha.
Qed.

(** Every multiple of a curve point is a curve point. *)
Lemma smul_on_curve : forall (n : Z) (a : Point), on_curve a -> on_curve (smul n a).
Proof.
  intros [|m|m] a Ha; cbn [smul].
  - exact I.
  - apply repeat_addition_binary_on_curve.
    exact Ha.
  - apply pneg_on_curve.
    apply repeat_addition_binary_on_curve.
    exact Ha.
Qed.

(** Every multiple of the identity is the identity. *)
Lemma repeat_addition_binary_PInf : forall m : positive, repeat_addition' m PInf = PInf.
Proof.
  induction m as [m IH|m IH|]; cbn [repeat_addition']; try rewrite IH; reflexivity.
Qed.

Lemma smul_PInf : forall n : Z, smul n PInf = PInf.
Proof.
  intros [|m|m]; cbn [smul]; try rewrite repeat_addition_binary_PInf; reflexivity.
Qed.

(* ----------------------------------------------------------------- *)
(** *** The operations on [CurvePoint]. *)

(** The identity. *)
Definition cp_zero : CurvePoint := exist _ PInf I.

(** Addition, closed by [padd_on_curve]. *)
Definition cp_add (a b : CurvePoint) : CurvePoint :=
  exist _ (padd (proj1_sig a) (proj1_sig b))
          (padd_on_curve (proj1_sig a) (proj1_sig b) (proj2_sig a) (proj2_sig b)).

(** Negation, closed by [pneg_on_curve]. *)
Definition cp_negate (a : CurvePoint) : CurvePoint :=
  exist _ (pneg (proj1_sig a)) (pneg_on_curve (proj1_sig a) (proj2_sig a)).

Lemma cp_add_assoc : forall x y z : CurvePoint,
  cp_add x (cp_add y z) = cp_add (cp_add x y) z.
Proof.
  intros x y z.
  apply curve_point_eq.
  simpl.
  symmetry.
  apply padd_assoc; apply proj2_sig.
Qed.

Lemma cp_add_comm : forall x y : CurvePoint, cp_add x y = cp_add y x.
Proof.
  intros x y.
  apply curve_point_eq.
  simpl.
  apply padd_comm.
Qed.

Lemma cp_add_zero : forall x : CurvePoint, cp_add cp_zero x = x.
Proof.
  intros x.
  apply curve_point_eq.
  simpl.
  apply padd_PInf_l.
Qed.

Lemma cp_add_inverse : forall x : CurvePoint, cp_add (cp_negate x) x = cp_zero.
Proof.
  intros x.
  apply curve_point_eq.
  simpl.
  apply padd_pneg_l.
Qed.

(** The points of secp256k1 form a group under the chord-and-tangent law, and
    that group is abelian. Both results are [Qed] and use the certified field and elliptic group laws.
    See https://wuille.net/posts/secp256k1-tutorial/#22-the-curve-group *)
#[export] Instance CurvePoint_zero : Zero CurvePoint := cp_zero.
#[export] Instance CurvePoint_add : Add CurvePoint := cp_add.
#[export] Instance CurvePoint_neg : Neg CurvePoint := cp_negate.

#[export] Instance curve_group : Group CurvePoint := {|
  group_add_assoc := cp_add_assoc;
  group_add_zero := cp_add_zero;
  group_add_inverse := cp_add_inverse
|}.

Lemma curve_abelian : Abelian CurvePoint.
Proof.
  exact cp_add_comm.
Qed.

Lemma padd_cancel_l : forall a b c, on_curve a -> on_curve b -> on_curve c -> padd a b = padd a c -> b = c.
Proof.
  intros a b c Ha Hb Hc H.
  apply (f_equal (padd (pneg a))) in H.
  rewrite <- !padd_assoc in H by (auto using pneg_on_curve).
  rewrite padd_pneg_l, !padd_PInf_l in H.
  exact H.
Qed.
Lemma pneg_add : forall a b, on_curve a -> on_curve b -> pneg (padd a b) = padd (pneg a) (pneg b).
Proof.
  intros a b Ha Hb.
  apply (padd_cancel_l (padd a b)); auto using padd_on_curve, pneg_on_curve.
  rewrite (padd_comm (padd a b) (pneg (padd a b))), padd_pneg_l.
  rewrite padd_assoc by auto using padd_on_curve, pneg_on_curve.
  rewrite (padd_comm (pneg a) (pneg b)).
  rewrite <- (padd_assoc b (pneg b) (pneg a)) by auto using pneg_on_curve.
  rewrite (padd_comm b (pneg b)), padd_pneg_l, padd_PInf_l.
  rewrite padd_comm, padd_pneg_l.
  reflexivity.
Qed.
Fixpoint repeated_add (n : nat) (a : Point) : Point :=
  match n with O => PInf | S m => padd a (repeated_add m a) end.
Lemma repeated_add_on_curve : forall n a, on_curve a -> on_curve (repeated_add n a).
Proof. induction n; intros a Ha; cbn; auto using padd_on_curve. Qed.
Lemma repeated_add_add : forall m n a, on_curve a -> repeated_add (m+n) a = padd (repeated_add m a) (repeated_add n a).
Proof.
  induction m; intros n a Ha; cbn; auto.
  rewrite IHm, padd_assoc by auto using repeated_add_on_curve.
  reflexivity.
Qed.
Lemma repeat_addition_binary_repeated : forall n a, on_curve a -> repeat_addition' n a = repeated_add (Pos.to_nat n) a.
Proof.
  induction n as [n IH|n IH|]; intros a Ha; cbn [repeat_addition'].
  - assert (Hd : forall a, pdouble a = padd a a).
    { intros [|x y]; [reflexivity|symmetry; apply padd_same]. }
    rewrite Hd, IH by exact Ha.
    rewrite <- repeated_add_add by exact Ha.
    rewrite Pos2Nat.inj_xI.
    replace (2 * Pos.to_nat n)%nat with (Pos.to_nat n + Pos.to_nat n)%nat by lia.
    reflexivity.
  - assert (Hd : forall a, pdouble a = padd a a).
    { intros [|x y]; [reflexivity|symmetry; apply padd_same]. }
    rewrite Hd, IH by exact Ha.
    rewrite <- repeated_add_add by exact Ha.
    rewrite Pos2Nat.inj_xO.
    f_equal; lia.
  - cbn; symmetry; apply padd_PInf_r.
Qed.
Lemma smul_of_nat : forall n a, on_curve a -> smul (Z.of_nat n) a = repeated_add n a.
Proof.
  intros n a Ha; destruct n as [|n]; [reflexivity|].
  change (repeat_addition' (Pos.of_succ_nat n) a = repeated_add (S n) a).
  rewrite repeat_addition_binary_repeated by exact Ha.
  rewrite SuccNat2Pos.id_succ; reflexivity.
Qed.
Lemma smul_opp : forall n a, smul (-n) a = pneg (smul n a).
Proof.
  intros [|n|n] a; cbn [Z.opp smul neg Point_neg]; try reflexivity.
  destruct (repeat_addition' n a); cbn [pneg neg Point_neg]; try reflexivity.
  f_equal; unfold neg, Fe_neg; ring.
Qed.
Lemma smul_succ : forall n a, on_curve a -> smul (n+1) a = padd a (smul n a).
Proof.
  intros n a Ha.
  destruct (Z_le_gt_dec 0 n) as [Hn|Hn].
  - replace n with (Z.of_nat (Z.to_nat n)) by (rewrite Z2Nat.id; lia).
    replace (Z.of_nat (Z.to_nat n) + 1) with (Z.of_nat (S (Z.to_nat n))) by lia.
    rewrite !smul_of_nat by exact Ha.
    reflexivity.
  - set (k := Z.to_nat (-n-1)).
    assert (Hk : n = - Z.of_nat (S k)).
    { unfold k; rewrite Nat2Z.inj_succ, Z2Nat.id by lia; lia. }
    rewrite Hk.
    replace (- Z.of_nat (S k) + 1) with (- Z.of_nat k) by (rewrite Nat2Z.inj_succ; lia).
    rewrite !smul_opp, !smul_of_nat by exact Ha.
    cbn [repeated_add].
    rewrite pneg_add by auto using repeated_add_on_curve.
    rewrite <- padd_assoc by auto using repeated_add_on_curve, pneg_on_curve.
    rewrite (padd_comm a (pneg a)), padd_pneg_l, padd_PInf_l.
    reflexivity.
Qed.
Lemma smul_add : forall (m n : Z) (a : Point),
  on_curve a -> smul (m + n) a = padd (smul m a) (smul n a).
Proof.
  intros m n a Ha.
  revert m; apply Z.bi_induction.
  - intros x y He; unfold Z.eq in He; subst; reflexivity.
  - cbn [Z.add smul]; reflexivity.
  - intros m; split; intros IH.
    + replace (Z.succ m + n) with ((m+n)+1) by lia.
      rewrite smul_succ by exact Ha.
      replace (Z.succ m) with (m+1) by lia.
      rewrite smul_succ, IH by exact Ha.
      rewrite padd_assoc by auto using smul_on_curve.
      reflexivity.
    + replace (Z.succ m + n) with ((m+n)+1) in IH by lia.
      replace (Z.succ m) with (m+1) in IH by lia.
      rewrite !smul_succ in IH by exact Ha.
      rewrite padd_assoc in IH by auto using smul_on_curve.
      eapply padd_cancel_l; eauto using smul_on_curve, padd_on_curve.
Qed.
Lemma smul_mul : forall (m n : Z) (a : Point),
  on_curve a -> smul (m * n) a = smul m (smul n a).
Proof.
  intros m n a Ha.
  revert m; apply Z.bi_induction.
  - intros x y He; unfold Z.eq in He; subst; reflexivity.
  - reflexivity.
  - intros m; split; intros IH.
    + replace (Z.succ m * n) with (n + m*n) by ring.
      rewrite smul_add by exact Ha.
      replace (Z.succ m) with (m+1) by lia.
      rewrite smul_succ by auto using smul_on_curve.
      rewrite IH; reflexivity.
    + replace (Z.succ m * n) with (n + m*n) in IH by ring.
      rewrite smul_add in IH by exact Ha.
      replace (Z.succ m) with (m+1) in IH by lia.
      rewrite smul_succ in IH by auto using smul_on_curve.
      eapply (padd_cancel_l (smul n a)); eauto using smul_on_curve.
Qed.

End law.
(* end hide *)


(* begin hide *)
Module finite.
Import Math.field Math.algebra.
Import Math.raw Math.ell.
Import Math.residues.
Import Math.law.
Import Math.field_prime.
Open Scope Z_scope.
Lemma field_modulus_not_two : ~ (2 | secp256k1_P).
Proof.
  intros [k Hk].
  pose proof P_odd as Hodd.
  rewrite Hk, Z_mod_mult in Hodd; discriminate.
Qed.
Lemma curve_discriminant_coprime : rel_prime secp256k1_P (4*0*0*0+27*7*7).
Proof. apply Zgcd_1_rel_prime; vm_compute; reflexivity. Qed.
Definition finite_ell_theory := ZEll.pell_theory 0 7 field_modulus_not_two
  curve_discriminant_coprime secp256k1_P_prime (Z.divide_refl secp256k1_P).
Definition finite_curve_group := ZEll.pG 0 7 field_modulus_not_two
  curve_discriminant_coprime secp256k1_P_prime (Z.divide_refl secp256k1_P).
Definition FiniteField := GZnZ.znz secp256k1_P.
Definition finite_to_fe (a : FiniteField) : Fe.
Proof.
  refine (mkFe (GZnZ.val _ a) _).
  rewrite (GZnZ.inZnZ _ a).
  apply Z.mod_pos_bound; pose proof secp256k1_P_range; lia.
Defined.
Lemma finite_to_fe_injective : forall a b, finite_to_fe a = finite_to_fe b -> a = b.
Proof.
  intros [a Ha] [b Hb] H; apply GZnZ.zirr.
  exact (f_equal fe_val H).
Qed.
Lemma finite_to_fe_add : forall a b, finite_to_fe (GZnZ.add _ a b) = fe_add (finite_to_fe a) (finite_to_fe b).
Proof. intros; apply fe_eq_ext; reflexivity. Qed.
Lemma finite_to_fe_mul : forall a b, finite_to_fe (GZnZ.mul _ a b) = fe_mul (finite_to_fe a) (finite_to_fe b).
Proof. intros; apply fe_eq_ext; reflexivity. Qed.
Lemma finite_to_fe_zero : finite_to_fe (GZnZ.zero _) = fe_zero.
Proof. apply fe_eq_ext; reflexivity. Qed.
Lemma finite_to_fe_one : finite_to_fe (GZnZ.one _) = fe_one.
Proof. apply fe_eq_ext; reflexivity. Qed.
Lemma finite_to_fe_opp : forall a, finite_to_fe (GZnZ.opp _ a) = fe_negate (finite_to_fe a).
Proof.
  intro a; apply fe_eq_ext; cbn [finite_to_fe GZnZ.opp GZnZ.val fe_negate fe_val fe_reduce].
  rewrite sub_P_mod; reflexivity.
Qed.
Lemma finite_to_fe_sub : forall a b, finite_to_fe (GZnZ.sub _ a b) = fe_sub (finite_to_fe a) (finite_to_fe b).
Proof.
  intros a b; apply fe_eq_ext; cbn [finite_to_fe GZnZ.sub GZnZ.val fe_sub fe_add fe_negate fe_val fe_reduce].
  rewrite sub_P_mod, addr_mod; f_equal; ring.
Qed.
Lemma finite_to_fe_inv : forall a, a <> GZnZ.zero _ -> finite_to_fe (GZnZ.inv _ a) = fe_inv (finite_to_fe a).
Proof.
  intros a Ha; apply (fe_inv_unique _ _ (finite_to_fe a)).
  - rewrite <- finite_to_fe_mul.
    rewrite (@Finv_l _ _ _ _ _ _ _ _ _ _ (GZnZ.FZpZ _ secp256k1_P_prime)) by exact Ha.
    apply finite_to_fe_one.
  - apply fe_inv_l; intro H; apply Ha; apply finite_to_fe_injective.
    rewrite finite_to_fe_zero; exact H.
Qed.
Definition FiniteCurve := SMain.elt (ZEll.pkI secp256k1_P) (@ZEll.pkplus secp256k1_P)
  (@ZEll.pkmul secp256k1_P) (ZEll.pA 0 secp256k1_P) (ZEll.pB 7 secp256k1_P).
Definition finite_point_to_raw (a : FiniteCurve) : Point :=
  match a with
  | SMain.inf_elt _ _ _ _ _ => PInf
  | SMain.curve_elt _ _ _ _ _ x y _ => PAff (finite_to_fe x) (finite_to_fe y)
  end.
Lemma finite_to_fe_a : finite_to_fe (ZEll.pA 0 secp256k1_P) = fe_a.
Proof. apply fe_eq_ext; reflexivity. Qed.
Lemma finite_to_fe_b : finite_to_fe (ZEll.pB 7 secp256k1_P) = fe_b.
Proof. apply fe_eq_ext; reflexivity. Qed.
Lemma finite_to_fe_pow : forall a n,
  finite_to_fe (SMain.pow (GZnZ.one _) (GZnZ.mul _) a n) = SMain.pow fe_one fe_mul (finite_to_fe a) n.
Proof.
  intros a n; induction n; cbn [SMain.pow].
  - apply finite_to_fe_one.
  - destruct n; cbn [SMain.pow] in *; [reflexivity|rewrite finite_to_fe_mul, IHn; reflexivity].
Qed.
Ltac finite_operations :=
  unfold ZEll.pkI, ZEll.pkO, ZEll.pkplus, ZEll.pkmul, ZEll.pksub, ZEll.pkopp, ZEll.pkdiv, ZEll.pkinv in *;
  repeat rewrite ?finite_to_fe_add, ?finite_to_fe_mul, ?finite_to_fe_sub,
    ?finite_to_fe_opp, ?finite_to_fe_one, ?finite_to_fe_zero,
    ?finite_to_fe_pow, ?finite_to_fe_a, ?finite_to_fe_b in *.
Lemma finite_point_on_curve : forall a, on_curve (finite_point_to_raw a).
Proof.
  intros [|x y H]; [exact I|].
  apply on_curve_iff; unfold curve_eq.
  apply (f_equal finite_to_fe) in H.
  finite_operations.
  exact H.
Qed.
Lemma finite_point_add : forall a b,
  padd (finite_point_to_raw a) (finite_point_to_raw b) =
  finite_point_to_raw (SMain.add finite_ell_theory a b).
Proof.
  intros a b.
  pattern a, b, (SMain.add finite_ell_theory a b).
  apply SMain.add_case.
  - intros r; reflexivity.
  - intros [|x y H]; reflexivity.
  - intros [|x y H]; [reflexivity|].
    cbn [finite_point_to_raw SMain.opp].
    finite_operations.
    change (padd (PAff (finite_to_fe x) (finite_to_fe y))
      (pneg (PAff (finite_to_fe x) (finite_to_fe y))) = PInf).
    rewrite padd_comm; apply padd_pneg_l.
  - intros p1 x1 y1 H1 p2 x2 y2 H2 l Hp1 Hp2 Hdbl Hy1 Hl Hx2 Hy2.
    subst p1 p2; cbn [finite_point_to_raw].
    assert (Hy : finite_to_fe y1 <> fe_zero).
    { intro H; apply Hy1; apply finite_to_fe_injective.
      change (finite_to_fe y1 = finite_to_fe (GZnZ.zero _)); rewrite finite_to_fe_zero; exact H. }
    assert (Hden : GZnZ.add _ y1 y1 <> GZnZ.zero _).
    { intro H; apply (f_equal finite_to_fe) in H.
      rewrite finite_to_fe_add, finite_to_fe_zero in H.
      apply Hy; apply fe_val_zero_iff; apply fe_self_negate_zero.
      replace (finite_to_fe y1) with
        (fe_add (fe_add (finite_to_fe y1) (finite_to_fe y1))
          (fe_negate (finite_to_fe y1))) at 1 by ring.
      rewrite H; ring. }
    apply (f_equal finite_to_fe) in Hl.
    apply (f_equal finite_to_fe) in Hx2.
    apply (f_equal finite_to_fe) in Hy2.
    finite_operations.
    unfold GZnZ.div in Hl.
    assert (Htwice : GZnZ.mul _ (GZnZ.add _ (GZnZ.one _) (GZnZ.one _)) y1 = GZnZ.add _ y1 y1).
    { apply finite_to_fe_injective; finite_operations; ring. }
    rewrite Htwice in Hl.
    rewrite finite_to_fe_mul, finite_to_fe_inv in Hl by exact Hden.
    finite_operations.
    rewrite padd_same, pdouble_aff by (intro H; apply Hy; apply fe_val_zero_iff; exact H).
    cbn zeta.
    assert (Hl' : finite_to_fe l =
      fe_mul (fe_add (fe_add (fe_mul (finite_to_fe x1) (finite_to_fe x1))
        (fe_mul (finite_to_fe x1) (finite_to_fe x1)))
        (fe_mul (finite_to_fe x1) (finite_to_fe x1)))
        (fe_inv (fe_add (finite_to_fe y1) (finite_to_fe y1)))).
    { rewrite Hl; apply f_equal2; [unfold fe_a; cbn [SMain.pow]; ring|reflexivity]. }
    rewrite Hl' in Hx2, Hy2.
    rewrite Hy2, Hx2.
    unfold fe_sub; cbn [SMain.pow].
    apply f_equal2; ring.
  - intros p1 x1 y1 H1 p2 x2 y2 H2 p3 x3 y3 H3 l Hp1 Hp2 Hp3 Hsum Hx Hl Hx3 Hy3.
    subst p1 p2 p3; cbn [finite_point_to_raw].
    assert (Hxv : fe_val (finite_to_fe x1) <> fe_val (finite_to_fe x2)).
    { intro H; apply Hx; apply finite_to_fe_injective; apply fe_eq_ext; exact H. }
    assert (Hden : GZnZ.sub _ x2 x1 <> GZnZ.zero _).
    { intro H; apply (f_equal finite_to_fe) in H.
      rewrite finite_to_fe_sub, finite_to_fe_zero in H.
      apply Hxv; symmetry; apply fe_sub_zero; exact H. }
    apply (f_equal finite_to_fe) in Hl.
    apply (f_equal finite_to_fe) in Hx3.
    apply (f_equal finite_to_fe) in Hy3.
    finite_operations.
    unfold GZnZ.div in Hl.
    rewrite finite_to_fe_mul, finite_to_fe_inv in Hl by exact Hden.
    rewrite !finite_to_fe_sub in Hl.
    rewrite padd_gen by exact Hxv.
    cbn zeta.
    rewrite Hl in Hx3, Hy3.
    rewrite Hy3, Hx3.
    unfold fe_sub; cbn [SMain.pow].
    apply f_equal2; ring.
Qed.
Definition fe_to_finite (a : Fe) : FiniteField.
Proof.
  refine (GZnZ.mkznz _ (fe_val a) _).
  symmetry; apply Z.mod_small; apply fe_range.
Defined.
Lemma finite_fe_roundtrip : forall a, finite_to_fe (fe_to_finite a) = a.
Proof. intro a; apply fe_eq_ext; reflexivity. Qed.
Lemma finite_point_surjective : forall a, on_curve a -> exists b, finite_point_to_raw b = a.
Proof.
  intros [|x y] Ha.
  - exists (SMain.inf_elt _ _ _ _ _); reflexivity.
  - apply on_curve_iff in Ha.
    assert (Hcurve : SMain.pow (ZEll.pkI _) (@ZEll.pkmul _) (fe_to_finite y) 2 =
      ZEll.pkplus (ZEll.pkplus (SMain.pow (ZEll.pkI _) (@ZEll.pkmul _) (fe_to_finite x) 3)
        (ZEll.pkmul (ZEll.pA 0 _) (fe_to_finite x))) (ZEll.pB 7 _)).
    { apply finite_to_fe_injective.
      finite_operations.
      rewrite !finite_fe_roundtrip; exact Ha. }
    exists (SMain.curve_elt _ _ _ _ _ _ _ Hcurve).
    cbn [finite_point_to_raw]; rewrite !finite_fe_roundtrip; reflexivity.
Qed.
Lemma finite_point_injective : forall a b, finite_point_to_raw a = finite_point_to_raw b -> a = b.
Proof.
  intros [|x y H] [|x' y' H']; cbn [finite_point_to_raw]; intro He; try discriminate; try reflexivity.
  injection He; intros Hy Hx.
  assert (Ex : x = x') by (apply finite_to_fe_injective; apply fe_eq_ext; exact Hx).
  assert (Ey : y = y') by (apply finite_to_fe_injective; apply fe_eq_ext; exact Hy).
  subst x' y'.
  f_equal.
  apply Eqdep_dec.UIP_dec.
  intros [u Hu] [v Hv]; destruct (Z.eq_dec u v) as [Hdec|Hdec].
  - left; apply GZnZ.zirr; exact Hdec.
  - right; intro Huv; apply Hdec; exact (f_equal (GZnZ.val _) Huv).
Qed.
Lemma finite_curve_member : forall a, List.In a (FGroup.s finite_curve_group).
Proof. intro a; apply SMain.FELLK_in. Qed.
Lemma finite_smul : forall n a, 0 <= n ->
  finite_point_to_raw (EGroup.gpow a finite_curve_group n) = smul n (finite_point_to_raw a).
Proof.
  intros n a Hn.
  replace n with (Z.of_nat (Z.to_nat n)) by (rewrite Z2Nat.id; lia).
  generalize (Z.to_nat n); intro k; induction k as [|k IH].
  - reflexivity.
  - replace (Z.of_nat (S k)) with (1 + Z.of_nat k) by lia.
    rewrite EGroup.gpow_add by (try apply finite_curve_member; lia).
    rewrite EGroup.gpow_1 by apply finite_curve_member.
    rewrite <- finite_point_add, IH.
    rewrite smul_add by apply finite_point_on_curve.
    reflexivity.
Qed.
Definition finite_G : FiniteCurve.
Proof.
  refine (SMain.curve_elt _ _ _ _ _ (fe_to_finite G_x) (fe_to_finite G_y) _).
  apply finite_to_fe_injective; finite_operations.
  rewrite !finite_fe_roundtrip.
  exact (proj1 (on_curve_iff G_x G_y) on_curve_G).
Defined.
Lemma finite_G_coordinates : finite_point_to_raw finite_G = G.
Proof. cbn [finite_G finite_point_to_raw]; rewrite !finite_fe_roundtrip; reflexivity. Qed.
Lemma projective_G_equiv : ZEll.equiv (ZEll.ntriple (fe_val G_x) (fe_val G_y) 1) finite_G.
Proof.
  constructor; apply GZnZ.zirr; vm_compute; reflexivity.
Qed.

End finite.
(* end hide *)


(* begin hide *)
Module certificates.
Import Math.field Math.scalar.
Import Math.raw Math.law.
Import Math.finite.
Import Math.field_prime.
Open Scope Z_scope.
Lemma generator_order_calculation :
  ZEll.scal secp256k1_P 0 1 (ZEll.ntriple (fe_val G_x) (fe_val G_y) 1)
    (Z.to_pos secp256k1_N) =
  (ZEll.nzero, 40652197283142301817317977020831535490410136607393541790709587164595674890204).
Proof. vm_compute; reflexivity. Qed.
Lemma generator_lambda_calculation :
  ZEll.scal secp256k1_P 0 1 (ZEll.ntriple (fe_val G_x) (fe_val G_y) 1)
    (Z.to_pos secp256k1_lambda) =
  (ZEll.ntriple
    15091048217591931286746058935427757887613366953760552008905463030098560752195
    102517693688301059111829673296514806705423811769754934132628372672649441911333
    43838397238382059971907911701270738026387978526640000628695345912996830955192, 1).
Proof. vm_compute; reflexivity. Qed.

End certificates.
(* end hide *)


(* begin hide *)
Module cardinality.
Import Math.algebra Math.field.
Import Math.fermat.
Import Math.residues.
Import Math.field_prime.
Import Math.raw.
Import Math.ell.
Import Math.finite.
(** The curve has odd cardinality because every affine point has a distinct negation. *)


Open Scope Z_scope.

Lemma negative_seven_non_cube_certificate :
  Z.eqb (pow_mod (-7) ((secp256k1_P - 1) / 3) secp256k1_P) 1 = false.
Proof.
  vm_compute.
  reflexivity.
Qed.

Local Opaque Z.pow pow_mod.

Lemma negative_seven_not_cube (x : Z) :
  0 <= x < secp256k1_P -> x ^ 3 mod secp256k1_P <> (-7) mod secp256k1_P.
Proof.
  intros Hrange Hcube.
  assert (Hnonzero : x <> 0).
  { intro Hz.
    subst x.
    vm_compute in Hcube.
    discriminate. }
  assert (Hfermat : x ^ (secp256k1_P - 1) mod secp256k1_P = 1).
  { apply fermat_little.
    - exact secp256k1_P_prime.
    - apply rel_prime_of_range.
      + exact secp256k1_P_prime.
      + lia. }
  set (exponent := ((secp256k1_P - 1) / 3)).
  assert (Hexponent : 0 <= exponent).
  { unfold exponent, secp256k1_P.
    vm_compute.
    discriminate. }
  apply (f_equal (fun a => a ^ exponent mod secp256k1_P)) in Hcube.
  rewrite !Z.mod_pow_l, <- Z.pow_mul_r in Hcube by lia.
  replace (3 * exponent) with (secp256k1_P - 1) in Hcube
    by (unfold exponent, secp256k1_P; vm_compute; reflexivity).
  rewrite Hfermat in Hcube.
  rewrite <- pow_mod_spec in Hcube by exact Hexponent.
  unfold exponent in Hcube.
  pose proof negative_seven_non_cube_certificate as Hcertificate.
  rewrite <- Hcube, Z.eqb_refl in Hcertificate.
  discriminate.
Qed.

Lemma curve_rhs_nonzero (x : Fe) :
  fe_add (fe_mul (fe_mul x x) x) curve_b <> fe_zero.
Proof.
  intro Hzero.
  assert (Hcube : fe_mul (fe_mul x x) x = fe_negate curve_b).
  { replace (fe_mul (fe_mul x x) x) with
      (fe_add (fe_add (fe_mul (fe_mul x x) x) curve_b) (fe_negate curve_b)) by ring.
    rewrite Hzero.
    ring. }
  apply (f_equal fe_val) in Hcube.
  cbn [fe_mul fe_negate fe_val curve_b fe_reduce] in Hcube.
  rewrite Zmult_mod_idemp_l in Hcube.
  replace (fe_val x * fe_val x * fe_val x) with (fe_val x ^ 3) in Hcube by ring.
  rewrite sub_P_mod in Hcube.
  apply (negative_seven_not_cube (fe_val x) (fe_range x)).
  exact Hcube.
Qed.

Lemma affine_ordinate_nonzero (x y : Fe) :
  on_curve (PAff x y) -> y <> fe_zero.
Proof.
  intros Hcurve Hz.
  subst y.
  apply (curve_rhs_nonzero x).
  symmetry.
  change (fe_mul fe_zero fe_zero = fe_add (fe_mul (fe_mul x x) x) curve_b) in Hcurve.
  replace (fe_mul fe_zero fe_zero) with fe_zero in Hcurve by ring.
  exact Hcurve.
Qed.

Lemma finite_curve_rhs_nonzero (x : FiniteField) :
  ZEll.pkplus
    (ZEll.pkplus (SMain.pow (ZEll.pkI _) (@ZEll.pkmul _) x 3)
      (ZEll.pkmul (ZEll.pA 0 _) x)) (ZEll.pB 7 _) <> ZEll.pkO _.
Proof.
  intro Hzero.
  apply (f_equal finite_to_fe) in Hzero.
  finite_operations.
  cbn [SMain.pow] in Hzero.
  unfold fe_a, fe_b in Hzero.
  apply (curve_rhs_nonzero (finite_to_fe x)).
  replace (fe_add (fe_mul (fe_mul (finite_to_fe x) (finite_to_fe x)) (finite_to_fe x)) curve_b)
    with (fe_add (fe_add (fe_mul (finite_to_fe x) (fe_mul (finite_to_fe x) (finite_to_fe x)))
      (fe_mul fe_zero (finite_to_fe x))) curve_b) by ring.
  exact Hzero.
Qed.


Lemma finite_affine_count_even (roots candidates : list FiniteField) :
  Nat.Even (length (SMain.EKa (ZEll.pkO _) (ZEll.pkI _) (@ZEll.pkplus _)
    (@ZEll.pkmul _) (@ZEll.pksub _) (@ZEll.pkopp _)
    (ZEll.pA 0 _) (ZEll.pB 7 _) (@ZEll.pis_zero _) roots candidates)).
Proof.
  induction candidates as [|x candidates [half Hhalf]].
  - exists 0%nat.
    reflexivity.
  - cbn [SMain.EKa].
    set (rhs := ZEll.pkplus
      (ZEll.pkplus (SMain.pow (ZEll.pkI _) (@ZEll.pkmul _) x 3)
        (ZEll.pkmul (ZEll.pA 0 _) x)) (ZEll.pB 7 _)).
    pose proof (SMain.Kfind_root_root finite_ell_theory rhs roots) as Hroot.
    unfold SMain.KLroot.
    destruct (SMain.Kfind_root (@ZEll.pkmul _) (@ZEll.pksub _)
      (@ZEll.pis_zero _) rhs roots) as [y|] eqn:Hfound.
    + destruct (ZEll.pis_zero y) eqn:Hzero.
      * apply (@ZEll.pis_zero_correct secp256k1_P secp256k1_P_prime) in Hzero.
        subst y.
        exfalso.
        apply (finite_curve_rhs_nonzero x).
        change (rhs = ZEll.pkO _).
        rewrite <- Hroot.
        apply finite_to_fe_injective.
        finite_operations.
        ring.
      * exists (S half).
        cbn [length].
        lia.
    + exists half.
      exact Hhalf.
Qed.

Lemma finite_curve_order_odd : Z.Odd (FGroup.g_order finite_curve_group).
Proof.
  unfold FGroup.g_order, finite_curve_group, ZEll.pG, SMain.EFGroup.
  cbn [FGroup.s].
  unfold SMain.FELLK.
  cbn [length].
  rewrite SMain.mk_lelt_length.
  unfold SMain.ELK.
  match goal with
  | |- Z.Odd (Z.of_nat (S (length ?points))) =>
      assert (Heven : Nat.Even (length points)) by apply finite_affine_count_even
  end.
  destruct Heven as [half Hhalf].
  exists (Z.of_nat half).
  rewrite Hhalf, Nat2Z.inj_succ, Nat2Z.inj_mul.
  lia.
Qed.

End cardinality.
(* end hide *)


(* begin hide *)
Module endomorphism.
Import Math.raw.
Import Math.ell.
Import Math.law.
Import Math.residues.
(** Multiplication of the x coordinate by beta preserves the curve group law. *)


Open Scope Z_scope.
Local Opaque beta.

Lemma beta_cube_product : fe_mul (fe_mul beta beta) beta = fe_one.
Proof.
  exact (proj1 beta_cube_root_unity).
Qed.

Lemma beta_scale_product (a b : Fe) :
  fe_mul (fe_mul (fe_mul a beta) beta) (fe_mul b beta) = fe_mul a b.
Proof.
  replace (fe_mul (fe_mul (fe_mul a beta) beta) (fe_mul b beta)) with
    (fe_mul (fe_mul a b) (fe_mul (fe_mul beta beta) beta)) by ring.
  rewrite beta_cube_product.
  ring.
Qed.

Lemma beta_scale_square (a : Fe) :
  fe_mul (fe_mul (fe_mul a beta) beta) (fe_mul (fe_mul a beta) beta) =
  fe_mul (fe_mul a a) beta.
Proof.
  rewrite beta_scale_product.
  ring.
Qed.

Lemma beta_scale_injective (a b : Fe) :
  fe_mul a beta = fe_mul b beta -> a = b.
Proof.
  intro Hequal.
  apply (f_equal (fun z => fe_mul (fe_mul z beta) beta)) in Hequal.
  replace (fe_mul (fe_mul (fe_mul a beta) beta) beta) with a in Hequal.
  - replace (fe_mul (fe_mul (fe_mul b beta) beta) beta) with b in Hequal.
    + exact Hequal.
    + replace beta with (fe_mul fe_one beta) at 3 by ring.
      rewrite beta_scale_product.
      ring.
  - replace beta with (fe_mul fe_one beta) at 3 by ring.
    rewrite beta_scale_product.
    ring.
Qed.

Lemma beta_scale_nonzero (a : Fe) :
  a <> fe_zero -> fe_mul a beta <> fe_zero.
Proof.
  intros Ha Hzero.
  apply Ha.
  apply beta_scale_injective.
  rewrite Hzero.
  ring.
Qed.

Lemma beta_scale_inverse (a : Fe) :
  a <> fe_zero ->
  fe_inv (fe_mul a beta) = fe_mul (fe_mul (fe_inv a) beta) beta.
Proof.
  intro Ha.
  apply (fe_inv_unique _ _ (fe_mul a beta)).
  - apply fe_inv_l.
    apply beta_scale_nonzero.
    exact Ha.
  - rewrite beta_scale_product.
    apply fe_inv_l.
    exact Ha.
Qed.

Lemma pmul_lambda_on_curve (a : Point) :
  on_curve a -> on_curve (pmul_lambda a).
Proof.
  destruct a as [|x y].
  - exact (fun H => H).
  - intro Hcurve.
    change (fe_mul y y =
      fe_add (fe_mul (fe_mul (fe_mul x beta) (fe_mul x beta)) (fe_mul x beta)) curve_b).
    replace (fe_mul (fe_mul (fe_mul x beta) (fe_mul x beta)) (fe_mul x beta)) with
      (fe_mul (fe_mul (fe_mul x x) x) (fe_mul (fe_mul beta beta) beta)) by ring.
    rewrite beta_cube_product.
    replace (fe_mul (fe_mul (fe_mul x x) x) fe_one) with (fe_mul (fe_mul x x) x) by ring.
    exact Hcurve.
Qed.

Definition slope_sum_coordinates (slope x1 x2 y1 : Fe) : Point :=
  let result_x := fe_add (fe_mul slope slope) (fe_negate (fe_add x1 x2)) in
  PAff result_x
    (fe_add (fe_mul slope (fe_add x1 (fe_negate result_x))) (fe_negate y1)).

Lemma pmul_lambda_slope (slope x1 x2 y1 : Fe) :
  pmul_lambda (slope_sum_coordinates slope x1 x2 y1) =
  slope_sum_coordinates (fe_mul (fe_mul slope beta) beta)
    (fe_mul x1 beta) (fe_mul x2 beta) y1.
Proof.
  unfold slope_sum_coordinates.
  cbn [pmul_lambda].
  rewrite beta_scale_square.
  replace (fe_add (fe_mul (fe_mul slope slope) beta)
    (fe_negate (fe_add (fe_mul x1 beta) (fe_mul x2 beta)))) with
    (fe_mul (fe_add (fe_mul slope slope) (fe_negate (fe_add x1 x2))) beta) by ring.
  f_equal.
  replace (fe_add (fe_mul x1 beta)
    (fe_negate (fe_mul (fe_add (fe_mul slope slope) (fe_negate (fe_add x1 x2))) beta)))
    with (fe_mul (fe_add x1
      (fe_negate (fe_add (fe_mul slope slope) (fe_negate (fe_add x1 x2))))) beta) by ring.
  rewrite beta_scale_product.
  reflexivity.
Qed.

Lemma pmul_lambda_double (a : Point) :
  pmul_lambda (pdouble a) = pdouble (pmul_lambda a).
Proof.
  destruct a as [|x y].
  - reflexivity.
  - destruct (Z.eq_dec (fe_val y) 0) as [Hzero|Hnonzero].
    + unfold pdouble, pmul_lambda, fe_is_zero.
      rewrite Hzero.
      reflexivity.
    + change (pmul_lambda (pdouble (PAff x y)) = pdouble (PAff (fe_mul x beta) y)).
      rewrite !pdouble_aff by exact Hnonzero.
      set (slope := fe_mul (fe_add (fe_add (fe_mul x x) (fe_mul x x)) (fe_mul x x))
        (fe_inv (fe_add y y))).
      replace (fe_mul
        (fe_add (fe_add (fe_mul (fe_mul x beta) (fe_mul x beta))
          (fe_mul (fe_mul x beta) (fe_mul x beta)))
          (fe_mul (fe_mul x beta) (fe_mul x beta))) (fe_inv (fe_add y y)))
        with (fe_mul (fe_mul slope beta) beta) by (unfold slope; ring).
      apply pmul_lambda_slope.
Qed.

Lemma pmul_lambda_add (a b : Point) :
  on_curve a -> on_curve b ->
  pmul_lambda (padd a b) = padd (pmul_lambda a) (pmul_lambda b).
Proof.
  intros Ha Hb.
  destruct a as [|x1 y1], b as [|x2 y2].
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - destruct (Z.eq_dec (fe_val x1) (fe_val x2)) as [Hxequal|Hxdifferent].
    + assert (Hx : x1 = x2) by (apply fe_eq_ext; exact Hxequal).
      subst x2.
      change (pmul_lambda (padd (PAff x1 y1) (PAff x1 y2)) =
        padd (PAff (fe_mul x1 beta) y1) (PAff (fe_mul x1 beta) y2)).
      unfold padd, eqb, Fe_eqb, fe_eqb.
      rewrite !Z.eqb_refl.
      destruct (Z.eqb (fe_val y1) (fe_val y2)).
      * apply pmul_lambda_double.
      * reflexivity.
    + assert (Hscaled : fe_val (fe_mul x1 beta) <> fe_val (fe_mul x2 beta)).
      { intro Hsame.
        apply Hxdifferent.
        apply (f_equal fe_val).
        apply beta_scale_injective.
        apply fe_eq_ext.
        exact Hsame. }
      change (pmul_lambda (padd (PAff x1 y1) (PAff x2 y2)) =
        padd (PAff (fe_mul x1 beta) y1) (PAff (fe_mul x2 beta) y2)).
      rewrite !padd_gen by assumption.
      replace (fe_add (fe_mul x2 beta) (fe_negate (fe_mul x1 beta))) with
        (fe_mul (fe_add x2 (fe_negate x1)) beta) by ring.
      rewrite beta_scale_inverse by (apply fe_sub_nonzero; congruence).
      set (slope := fe_mul (fe_add y2 (fe_negate y1)) (fe_inv (fe_add x2 (fe_negate x1)))).
      replace (fe_mul (fe_add y2 (fe_negate y1))
        (fe_mul (fe_mul (fe_inv (fe_add x2 (fe_negate x1))) beta) beta)) with
        (fe_mul (fe_mul slope beta) beta) by (unfold slope; ring).
      apply pmul_lambda_slope.
Qed.

End endomorphism.
(* end hide *)


(* begin hide *)
Module group.
Export Math.algebra.
Export Math.field.
Export Math.scalar.
Import Math.residues.
Import Math.ell.
Import Math.law.
Import Math.raw.
(* end hide *)
(** * 5. The Curve Group *)

(** Elliptic curve cryptography turns curve points into a group.
    Multiplying a known point by an integer is practical. Recovering
    that integer from the result is believed to be infeasible for the
    parameters used here. This difference is the basis of the later
    signature construction.

    Our equation is [y^2 = x^3 + 7] over the coordinate field. The
    constant term is seven and the coefficient of [x] is zero. Points
    admit an _identity_, _negation_, and _addition_. Repeated addition
    gives _scalar multiplication_.

    Over the real numbers, a line through two points meets the curve
    again. Reflecting the third intersection gives the sum. A finite
    field has discrete points instead of a continuous curve, but the
    same algebraic formulas define addition. The difficult proof is
    associativity, including equal points, opposite points, and the
    identity. The supporting curve theory checks these cases. *)

(* begin hide *)


Open Scope Z_scope.
Local Open Scope math_scope.
(* end hide *)

(* ================================================================= *)
(** ** 5.1 Points and the Curve Equation *)

(** #<div class="spec-figure" data-figure="curve"></div># *)

(** The curve equation is [y * y = x * x * x + curve_b]. A point is
    either the identity [PInf] or coordinates [x] and [y] with
    evidence of this equation. [Inductive] lists these constructors.
    The argument [valid] contains evidence, not extra coordinate
    data. *)

Definition curve_b : Fe := mkFe 7 (fe_range raw.curve_b).

Inductive Point :=
| PInf
| PAff (x y : Fe) (valid : y * y = x * x * x + curve_b).

(** Unlike a pair of field elements, a [Point] cannot describe an
    off-curve coordinate pair. C stores coordinates without this
    evidence. Its representation predicates must therefore establish
    the same equation when connecting memory to a [Point]. *)

(* begin hide *)
Definition point_coordinates (a : Point) : raw.Point :=
  match a with
  | PInf => raw.PInf
  | PAff x y _ => raw.PAff x y
  end.

Coercion point_coordinates : Point >-> raw.Point.

Definition point_valid (a : Point) : raw.on_curve (point_coordinates a) :=
  match a with
  | PInf => I
  | PAff _ _ valid => valid
  end.

(* end hide *)

(** Internal coordinates may be arbitrary field pairs. The projection
    [point_coordinates] forgets validity evidence. The constructor below
    requires that evidence when returning to the public [Point] type.
    Its checked companion tests the equation and can return [None]. *)

Definition point_of_coordinates (a : raw.Point)
    (valid : raw.on_curve a) : Point :=
  match a return raw.on_curve a -> Point with
  | raw.PInf => fun _ => PInf
  | raw.PAff x y => fun valid => PAff x y valid
  end valid.

Definition point_of_coordinates_checked (a : raw.Point) : option Point :=
  match a with
  | raw.PInf => Some PInf
  | raw.PAff x y =>
      match fe_eq_dec (y * y) (x * x * x + curve_b) with
      | left valid => Some (PAff x y valid)
      | right _ => None
      end
  end.

(* begin hide *)
Lemma point_coordinates_of_coordinates a valid :
  point_coordinates (point_of_coordinates a valid) = a.
Proof.
  destruct a; reflexivity.
Qed.

Lemma point_eq_ext (a b : Point) :
  point_coordinates a = point_coordinates b -> a = b.
Proof.
  destruct a as [|x y Ha], b as [|u v Hb].
  - (* Both points are the identity. *)
    reflexivity.
  - (* An affine point cannot be the identity. *)
    discriminate.
  - (* The identity cannot have affine coordinates. *)
    discriminate.
  - (* Coordinate equality determines the validity evidence as well. *)
    intro H.
    injection H as Hx Hy.
    subst u v.
    f_equal.
    apply (on_curve_irrel (raw.PAff x y)).
Qed.
(* end hide *)

(* ================================================================= *)
(** ** 5.2 Observing a Point *)

(** Proofs use equality as a proposition. Executable code uses a
    boolean test. [point_eqb] compares the coordinates and distinguishes
    the identity from every affine point. Validity evidence does not
    affect equality. The lemma [point_eqb_eq] connects a successful
    computation to propositional equality, so later proofs can justify
    branches selected by the boolean test. *)

Definition affine_coordinates (a : Point) : option (Fe * Fe) :=
  match a with
  | PInf => None
  | PAff x y _ => Some (x, y)
  end.

Definition point_eqb (a b : Point) : bool :=
  match a, b with
  | PInf, PInf => true
  | PAff x1 y1 _, PAff x2 y2 _ => (x1 =? x2) && (y1 =? y2)
  | _, _ => false
  end.

Definition Point_eqb : Eqb Point := point_eqb.
(* begin hide *)
#[export] Existing Instance Point_eqb.
(* end hide *)

Lemma point_eqb_eq (a b : Point) :
  point_eqb a b = true <-> a = b.
Proof.
  assert (Htest : point_eqb a b =
    raw.point_eqb (point_coordinates a) (point_coordinates b)).
  { destruct a, b; reflexivity. }
  rewrite Htest.
  rewrite residues.point_eqb_eq.
  split.
  - (* Equality of coordinates determines the point. *)
    apply point_eq_ext.
  - (* Equal points have equal coordinates. *)
    intro H.
    now subst b.
Qed.

(* ================================================================= *)
(** ** 5.3 The Group Law *)

(** _Negation_ reflects a point across the x axis. The x coordinate
    stays fixed and [y] becomes [-y]. _Addition_ uses the chord slope
    [(y2 - y1) / (x2 - x1)]. _Doubling_ uses the tangent slope
    [3x^2 / 2y]. For either slope [s], the new coordinates are
    [x3 = s^2 - x1 - x2] and [y3 = s * (x1 - x3) - y1].

    The coordinate formulas also handle the identity and vertical
    lines, whose result is [PInf]. Their closure proofs establish that
    negation, doubling and addition preserve the curve equation.
    [point_of_coordinates] packages each computed result with that
    evidence. The hidden closure proofs justify packaging the
    computed coordinates as valid points. *)

Definition pneg (a : Point) : Point :=
  let coordinates :=
    match point_coordinates a with
    | raw.PInf => raw.PInf
    | raw.PAff x y => raw.PAff x (- y)
    end in
  point_of_coordinates coordinates (pneg_on_curve _ (point_valid a)).

Definition pdouble (a : Point) : Point :=
  let coordinates :=
    match point_coordinates a with
    | raw.PInf => raw.PInf
    | raw.PAff x y =>
        if fe_is_zero y then raw.PInf
        else
          let slope := fe_mul_int (fe_sqr x) 3 / fe_mul_int y 2 in
          let x3 := fe_sqr slope - fe_mul_int x 2 in
          let y3 := slope * (x - x3) - y in
          raw.PAff x3 y3
    end in
  point_of_coordinates coordinates
    (pdouble_on_curve _ (point_valid a)).

Definition padd (a b : Point) : Point :=
  let coordinates :=
    match point_coordinates a, point_coordinates b with
    | raw.PInf, _ => point_coordinates b
    | _, raw.PInf => point_coordinates a
    | raw.PAff x1 y1, raw.PAff x2 y2 =>
        if x1 =? x2 then
          (if y1 =? y2 then raw.pdouble (point_coordinates a)
           else raw.PInf)
        else
          let slope := (y2 - y1) / (x2 - x1) in
          let x3 := fe_sqr slope - (x1 + x2) in
          let y3 := slope * (x1 - x3) - y1 in
          raw.PAff x3 y3
    end in
  point_of_coordinates coordinates
    (padd_on_curve _ _ (point_valid a) (point_valid b)).

Definition Point_add : Add Point := padd.
Definition Point_neg : Neg Point := pneg.
Definition Point_zero : Zero Point := PInf.
(* begin hide *)
#[export] Existing Instance Point_add.
#[export] Existing Instance Point_neg.
#[export] Existing Instance Point_zero.

Lemma point_coordinates_add a b :
  point_coordinates (padd a b) =
  raw.padd (point_coordinates a) (point_coordinates b).
Proof. apply point_coordinates_of_coordinates. Qed.

Lemma point_coordinates_neg a :
  point_coordinates (pneg a) = raw.pneg (point_coordinates a).
Proof. apply point_coordinates_of_coordinates. Qed.

Lemma point_coordinates_double a :
  point_coordinates (pdouble a) = raw.pdouble (point_coordinates a).
Proof. apply point_coordinates_of_coordinates. Qed.
(* end hide *)

(** The group laws now apply to every [Point], without an additional
    on-curve precondition. Coordinate equality lets us reuse the
    algebraic proofs for the formulas. *)

Lemma padd_assoc (a b c : Point) :
  padd (padd a b) c = padd a (padd b c).
Proof.
  apply point_eq_ext.
  rewrite !point_coordinates_add.
  apply law.padd_assoc; apply point_valid.
Qed.

Lemma padd_comm (a b : Point) :
  padd a b = padd b a.
Proof.
  apply point_eq_ext.
  rewrite !point_coordinates_add.
  apply law.padd_comm.
Qed.

Lemma padd_PInf_l (a : Point) :
  padd PInf a = a.
Proof.
  apply point_eq_ext.
  rewrite point_coordinates_add.
  reflexivity.
Qed.

Lemma padd_PInf_r (a : Point) :
  padd a PInf = a.
Proof.
  rewrite padd_comm.
  apply padd_PInf_l.
Qed.

Lemma padd_pneg_l (a : Point) :
  padd (pneg a) a = PInf.
Proof.
  apply point_eq_ext.
  rewrite point_coordinates_add, point_coordinates_neg.
  apply law.padd_pneg_l.
Qed.

Definition point_group : Group Point := {|
  group_add_assoc := fun a b c => eq_sym (padd_assoc a b c);
  group_add_zero := padd_PInf_l;
  group_add_inverse := padd_pneg_l
|}.
(* begin hide *)
#[export] Existing Instance point_group.
(* end hide *)

(* ================================================================= *)
(** ** 5.4 Scalar Multiplication *)

(** Multiplication by a natural number means repeated addition.
    [O] is zero and [S n] is the successor of [n]. These two cases
    describe the operation without choosing an efficient algorithm. *)

Fixpoint repeat_addition (n : nat) (a : Point) : Point :=
  match n with
  | O => PInf
  | S m => padd a (repeat_addition m a)
  end.

(** Zero gives the identity. A negative multiplier negates the
    corresponding positive multiple. *)

Definition smul (n : Z) (a : Point) : Point :=
  match n with
  | Z0 => PInf
  | Zpos m => repeat_addition (Pos.to_nat m) a
  | Zneg m => pneg (repeat_addition (Pos.to_nat m) a)
  end.

(** Binary doubling and addition computes the same result with one
    recursive step per binary digit. An even multiplier doubles the
    smaller result. An odd multiplier adds one more copy of [a]. *)

Fixpoint repeat_addition' (n : positive) (a : Point) : Point :=
  match n with
  | xH => a
  | xO m => pdouble (repeat_addition' m a)
  | xI m => padd a (pdouble (repeat_addition' m a))
  end.

Definition smul' (n : Z) (a : Point) : Point :=
  match n with
  | Z0 => PInf
  | Zpos m => repeat_addition' m a
  | Zneg m => pneg (repeat_addition' m a)
  end.

(** The binary algorithm replaces two copies of a shorter sum by one
    doubling step. The next lemma shows that doubling is exactly
    [padd a a]. It is the link needed to compare binary
    multiplication with repeated addition. *)

Lemma pdouble_add (a : Point) :
  pdouble a = padd a a.
Proof.
  apply point_eq_ext.
  rewrite point_coordinates_double, point_coordinates_add.
  destruct (point_coordinates a) as [|x y].
  - (* Doubling the identity returns the identity. *)
    reflexivity.
  - (* Equal coordinates select the tangent case of addition. *)
    cbv [raw.padd eqb Fe_eqb fe_eqb].
    rewrite !Z.eqb_refl.
    reflexivity.
Qed.

Lemma repeat_addition_add (m n : nat) (a : Point) :
  repeat_addition (m + n) a = padd (repeat_addition m a) (repeat_addition n a).
Proof.
  induction m as [|m IH].
  - (* Zero contributes the identity. *)
    simpl.
    symmetry.
    apply padd_PInf_l.
  - (* One more copy can be regrouped by associativity. *)
    simpl.
    rewrite IH, padd_assoc.
    reflexivity.
Qed.

Lemma repeat_addition_binary_eq_nat (n : positive) (a : Point) :
  repeat_addition' n a = repeat_addition (Pos.to_nat n) a.
Proof.
  induction n as [n IH|n IH|].
  - (* An odd multiplier is one plus two equal halves. *)
    cbn [repeat_addition'].
    rewrite pdouble_add, IH, <- repeat_addition_add.
    rewrite Pos2Nat.inj_xI.
    replace (2 * Pos.to_nat n)%nat with
      (Pos.to_nat n + Pos.to_nat n)%nat by lia.
    reflexivity.
  - (* An even multiplier consists of two equal halves. *)
    cbn [repeat_addition'].
    rewrite pdouble_add, IH, <- repeat_addition_add.
    rewrite Pos2Nat.inj_xO.
    f_equal.
    lia.
  - (* Multiplication by one adds one copy to the identity. *)
    simpl.
    symmetry.
    apply padd_PInf_r.
Qed.

(** This equality connects the readable definition to the efficient
    implementation. It covers negative multipliers as well as zero
    and positive ones. *)

Lemma smul'_eq_smul (n : Z) (a : Point) :
  smul' n a = smul n a.
Proof.
  destruct n as [|n|n].
  - (* Zero selects the identity in both definitions. *)
    reflexivity.
  - (* Positive multipliers agree by binary induction. *)
    apply repeat_addition_binary_eq_nat.
  - (* Negation preserves equality of the positive multiples. *)
    unfold smul', smul.
    rewrite repeat_addition_binary_eq_nat.
    reflexivity.
Qed.

(** Executable equations use the efficient operation. The equality
    above guarantees that [k * a] still means repeated addition. *)

Definition Point_smul : Mul Z Point Point := smul'.
Definition Point_smul_scalar : Mul Scalar Point Point :=
  fun k a => smul' (scalar_val k) a.
(* begin hide *)
#[export] Existing Instance Point_smul.
#[export] Existing Instance Point_smul_scalar.

Lemma point_coordinates_smul_pos n a :
  point_coordinates (repeat_addition' n a) = raw.repeat_addition' n (point_coordinates a).
Proof.
  induction n as [n IH|n IH|].
  - (* The odd step preserves the coordinate addition formula. *)
    cbn [repeat_addition' raw.repeat_addition'].
    rewrite point_coordinates_add, point_coordinates_double, IH.
    reflexivity.
  - (* The even step preserves the coordinate doubling formula. *)
    cbn [repeat_addition' raw.repeat_addition'].
    rewrite point_coordinates_double, IH.
    reflexivity.
  - (* The initial multiple is the input point. *)
    reflexivity.
Qed.

Lemma point_coordinates_smul n a :
  point_coordinates (smul' n a) = raw.smul n (point_coordinates a).
Proof.
  destruct n as [|n|n].
  - (* Both zero multiples are the identity. *)
    reflexivity.
  - (* Positive multiplication follows the binary bridge. *)
    apply point_coordinates_smul_pos.
  - (* Negative multiplication also preserves coordinate negation. *)
    cbn [smul' raw.smul].
    rewrite point_coordinates_neg, point_coordinates_smul_pos.
    reflexivity.
Qed.
(* end hide *)

(* ================================================================= *)
(** ** 5.5 The Generator *)

(** The generator [G] is the point fixed by
    {{https://www.secg.org/sec2-v2.pdf#page=13}SEC 2 section 2.4.1}.
    Its coordinate literals are shown here so they can be compared
    directly with the standard. Its _order_ is [n], meaning that
    adding [G] to itself [n] times gives [PInf], while no smaller
    positive number of copies does. Constructing [G] also checks the
    curve equation. *)

(* begin hide *)
Local Obligation Tactic := intros.
(* end hide *)

Program Definition G_x : Fe :=
  mkFe 0x79BE667EF9DCBBAC55A06295CE870B07029BFCDB2DCE28D959F2815B16F81798 _.
(* begin hide *)
Next Obligation.
  exact (fe_range raw.G_x).
Defined.
(* end hide *)
Program Definition G_y : Fe :=
  mkFe 0x483ADA7726A3C4655DA4FBFC0E1108A8FD17B448A68554199C47D08FFB10D4B8 _.
(* begin hide *)
Next Obligation.
  exact (fe_range raw.G_y).
Defined.
(* end hide *)

Program Definition G : Point := PAff G_x G_y _.
(* begin hide *)
Next Obligation.
  exact raw.on_curve_G.
Qed.
(* end hide *)

(* ================================================================= *)
(** ** 5.6 The GLV Endomorphism *)

(** The _GLV endomorphism_ replaces one large scalar multiplication
    with two smaller ones. The map [(x,y) -> (beta*x,y)] costs one field
    multiplication. It has the same effect as multiplying the point
    by a particular scalar [lambda]. Splitting [k] into
    [k1 + lambda*k2] therefore turns [k*P] into
    [k1*P + k2*(beta*x,y)]. The two shorter multiplications can share
    their doubling work.

    The constant [beta] is a nontrivial cube root of one. Consequently
    multiplying x by [beta] leaves [x^3 + 7] unchanged. *)

Program Definition beta : Fe :=
  mkFe 0x7AE96A2B657C07106E64479EAC3434E99CF0497512F58995C1396C28719501EE _.
(* begin hide *)
Next Obligation.
  exact (fe_range raw.beta).
Defined.
(* end hide *)
Definition secp256k1_lambda : Z :=
  0x5363AD4CC05C30E0A5261C028812645A122E22EA20816678DF02967C1B23BD72.

Lemma beta_cube_root_unity : beta * beta * beta = 1%F /\ beta <> 1%F.
Proof.
  split.
  - (* The cube of beta is the multiplicative identity. *)
    apply fe_eq_ext.
    vm_compute.
    reflexivity.
  - (* Beta itself is not the identity, so the map is nontrivial. *)
    intro H.
    apply (f_equal fe_val) in H.
    vm_compute in H.
    discriminate.
Qed.

(* begin hide *)
Lemma pmul_lambda_valid x y :
  y * y = x * x * x + curve_b ->
  y * y = (x * beta) * (x * beta) * (x * beta) + curve_b.
Proof.
  intro H.
  rewrite H.
  change (fe_add (fe_mul (fe_mul x x) x) curve_b =
    fe_add (fe_mul (fe_mul (fe_mul x beta) (fe_mul x beta))
      (fe_mul x beta)) curve_b).
  replace (fe_mul (fe_mul (fe_mul x beta) (fe_mul x beta))
      (fe_mul x beta)) with
    (fe_mul (fe_mul (fe_mul x x) x) (fe_mul (fe_mul beta beta) beta))
    by ring.
  change (x * x * x + curve_b = x * x * x * (beta * beta * beta) + curve_b).
  rewrite (proj1 beta_cube_root_unity).
  change (fe_add (fe_mul (fe_mul x x) x) curve_b =
    fe_add (fe_mul (fe_mul (fe_mul x x) x) fe_one) curve_b).
  ring.
Qed.
(* end hide *)

Definition pmul_lambda (a : Point) : Point :=
  match a with
  | PInf => PInf
  | PAff x y valid => PAff (x * beta) y (pmul_lambda_valid x y valid)
  end.

(** {{#Math.curve_results.glv_preserves_multiplication}The preservation
    theorem} below proves that this map equals scalar multiplication
    by [lambda]. It justifies the shortcut for every valid point. *)

(* ================================================================= *)
(** ** 5.7 X-only Points *)

(** {{https://bips.dev/340/}BIP-340} publishes only the x coordinate.
    Of the two points sharing that coordinate, it chooses the one
    with even y. If [x^3 + 7] has no square root, no point has that
    x coordinate and the lift fails. Otherwise parity selects a root.
    [checked_sqrt] retains the equation checked by [fe_sqrt] alongside
    its successful root. *)

(* begin hide *)
Lemma fe_sqrt_valid a y : fe_sqrt a = Some y -> y * y = a.
Proof.
  unfold fe_sqrt, pow, Power_N.
  remember (power' a fe_sqrt_exponent) as r eqn:Hcandidate.
  clear Hcandidate.
  destruct (r * r =? a) eqn:Hroot.
  - (* A successful candidate passed the squared-value equality test. *)
    intro H.
    injection H as <-.
    apply fe_eq_ext.
    apply Z.eqb_eq.
    exact Hroot.
  - (* A failed equality test cannot return a square root. *)
    discriminate.
Qed.

Lemma negated_root_valid x y :
  y * y = x * x * x + curve_b ->
  (- y) * (- y) = x * x * x + curve_b.
Proof.
  intro H.
  exact (pneg_on_curve (raw.PAff x y) H).
Qed.
(* end hide *)

(* begin hide *)
Definition checked_sqrt (a : Fe) : option {y : Fe | y * y = a} :=
  match fe_sqrt a as root return
    fe_sqrt a = root -> option {y : Fe | y * y = a} with
  | None => fun _ => None
  | Some y => fun valid => Some (exist _ y (fe_sqrt_valid a y valid))
  end eq_refl.
(* end hide *)

Definition lift_x_even (x : Fe) : option Point :=
  match checked_sqrt (x * x * x + curve_b) with
  | None => None
  | Some (exist _ y valid) =>
      match fe_is_odd y with
      | true => Some (PAff x (- y) (negated_root_valid x y valid))
      | false => Some (PAff x y valid)
      end
  end.

(** Both successful cases construct a valid point. Negating an odd
    root preserves its square and chooses the even root. *)

(* begin hide *)
End group.
(* end hide *)


(* begin hide *)
Module order.
Import Math.algebra.
Import Math.cardinality.
Import Math.endomorphism.
Import Math.field Math.scalar.
Import Math.raw Math.law.
Import Math.finite Math.certificates.
Import Math.field_prime Math.order_prime.
Import Math.residues.
(** * The generator order, cofactor and scalar endomorphism. *)
(** Copyright (C) 2026 remix7531
    SPDX-License-Identifier: MIT *)

(** The projective certificates establish the generator order and the GLV
    identity at the generator. The finite curve has odd cardinality, divisible
    by the prime generator order and less than three times that order. Its
    cardinality is therefore the generator order, so every curve point is a
    generator multiple and the GLV identity extends to every curve point. *)

Open Scope Z_scope.
Lemma generator_order_inversible :
  ZEll.nInversible secp256k1_P
    (ZEll.scal secp256k1_P 0 1 (ZEll.ntriple (fe_val G_x) (fe_val G_y) 1) (Z.to_pos secp256k1_N)).
Proof.
  rewrite generator_order_calculation; constructor.
  exists 16323067822870963867408806670269306356315395086599762522219025068684972525506.
  vm_compute; reflexivity.
Qed.
Lemma projective_zero_unique : forall a : FiniteCurve,
  ZEll.equiv ZEll.nzero a -> a = SMain.inf_elt _ _ _ _ _.
Proof. intros a H; inversion H; reflexivity. Qed.
Lemma finite_G_order_multiple : EGroup.gpow finite_G finite_curve_group secp256k1_N = FGroup.e finite_curve_group.
Proof.
  assert (Hp : 2 < secp256k1_P) by (vm_compute; reflexivity).
  pose proof (@ZEll.scal_correct secp256k1_P 0 7 Hp field_modulus_not_two
    curve_discriminant_coprime secp256k1_P secp256k1_P_prime
    (Z.divide_refl secp256k1_P) (Z.to_pos secp256k1_N) 1
    (ZEll.ntriple (fe_val G_x) (fe_val G_y) 1) finite_G
    projective_G_equiv generator_order_inversible) as H.
  rewrite generator_order_calculation in H.
  cbn [fst] in H.
  exact (projective_zero_unique _ H).
Qed.
Lemma finite_G_order_exact : EGroup.e_order (SMain.ceqb finite_ell_theory) finite_G finite_curve_group = secp256k1_N.
Proof.
  pose proof (@EGroup.e_order_divide_gpow _ (SMain.ceqb finite_ell_theory) _ finite_G finite_curve_group
    (finite_curve_member finite_G) secp256k1_N) as Hd.
  assert (Hn : 0 < secp256k1_N) by (pose proof secp256k1_N_range; lia).
  specialize (Hd ltac:(lia) finite_G_order_multiple).
  pose proof (@EGroup.e_order_pos _ (SMain.ceqb finite_ell_theory) _ finite_G finite_curve_group) as Hpos.
  destruct (prime_divisors secp256k1_N secp256k1_N_prime _ Hd) as [H|[H|[H|H]]]; try lia.
  pose proof (@EGroup.gpow_e_order_is_e _ (SMain.ceqb finite_ell_theory) _ finite_G finite_curve_group
    (finite_curve_member finite_G)) as He.
  rewrite H, EGroup.gpow_1 in He by apply finite_curve_member.
  apply (f_equal finite_point_to_raw) in He.
  rewrite finite_G_coordinates in He.
  discriminate He.
Qed.
Lemma G_order : smul secp256k1_N G = PInf /\
  (forall k, 0 < k < secp256k1_N -> smul k G <> PInf).
Proof.
  split.
  - pose proof (f_equal finite_point_to_raw finite_G_order_multiple) as H.
    rewrite finite_smul, finite_G_coordinates in H by (pose proof secp256k1_N_range; lia).
    exact H.
  - intros k Hk Hzero.
    pose proof (@EGroup.gpow_e_order_lt_is_not_e _ (SMain.ceqb finite_ell_theory) _ finite_G
      finite_curve_group (finite_curve_member finite_G) k) as H.
    rewrite finite_G_order_exact in H.
    apply H; [lia|].
    apply finite_point_injective.
    rewrite finite_smul, finite_G_coordinates by lia.
    exact Hzero.
Qed.
Definition finite_lambda_G : FiniteCurve.
Proof.
  refine (SMain.curve_elt _ _ _ _ _ (fe_to_finite (fe_mul beta G_x)) (fe_to_finite G_y) _).
  apply GZnZ.zirr; vm_compute; reflexivity.
Defined.
Lemma finite_lambda_G_coordinates : finite_point_to_raw finite_lambda_G = pmul_lambda G.
Proof. cbn [finite_lambda_G finite_point_to_raw]; rewrite !finite_fe_roundtrip; reflexivity. Qed.
Lemma generator_lambda_inversible :
  ZEll.nInversible secp256k1_P
    (ZEll.scal secp256k1_P 0 1 (ZEll.ntriple (fe_val G_x) (fe_val G_y) 1) (Z.to_pos secp256k1_lambda)).
Proof.
  rewrite generator_lambda_calculation; constructor.
  exists 2911573354486332737357518002210141896920230377734704960474012737986752476486.
  vm_compute; reflexivity.
Qed.
Lemma projective_lambda_G_equiv :
  ZEll.equiv (ZEll.ntriple
    15091048217591931286746058935427757887613366953760552008905463030098560752195
    102517693688301059111829673296514806705423811769754934132628372672649441911333
    43838397238382059971907911701270738026387978526640000628695345912996830955192) finite_lambda_G.
Proof. constructor; apply GZnZ.zirr; vm_compute; reflexivity. Qed.
Lemma projective_equiv_unique : forall t (a b : FiniteCurve),
  ZEll.equiv t a -> ZEll.equiv t b -> a = b.
Proof.
  intros t a b Ha Hb.
  inversion Ha; subst.
  - apply projective_zero_unique in Hb; symmetry; exact Hb.
  - inversion Hb; subst.
    apply finite_point_injective; cbn [finite_point_to_raw].
    reflexivity.
Qed.
Lemma lambda_G_certificate : pmul_lambda G = smul secp256k1_lambda G.
Proof.
  assert (Hp : 2 < secp256k1_P) by (vm_compute; reflexivity).
  pose proof (@ZEll.scal_correct secp256k1_P 0 7 Hp field_modulus_not_two
    curve_discriminant_coprime secp256k1_P secp256k1_P_prime
    (Z.divide_refl secp256k1_P) (Z.to_pos secp256k1_lambda) 1
    (ZEll.ntriple (fe_val G_x) (fe_val G_y) 1) finite_G
    projective_G_equiv generator_lambda_inversible) as H.
  rewrite generator_lambda_calculation in H; cbn [fst] in H.
  pose proof (projective_equiv_unique _ _ _ projective_lambda_G_equiv H) as He.
  apply (f_equal finite_point_to_raw) in He.
  rewrite finite_lambda_G_coordinates, finite_smul, finite_G_coordinates in He by (unfold secp256k1_lambda; lia).
  exact He.
Qed.
Lemma finite_curve_order : FGroup.g_order finite_curve_group = secp256k1_N.
Proof.
  pose proof (@EGroup.e_order_divide_g_order _ (SMain.ceqb finite_ell_theory) _ finite_G
    finite_curve_group (finite_curve_member finite_G)) as Hdiv.
  rewrite finite_G_order_exact in Hdiv.
  destruct Hdiv as [q Hq].
  pose proof (ZEll.gorder_pG 0 7 field_modulus_not_two curve_discriminant_coprime
    secp256k1_P_prime (Z.divide_refl secp256k1_P)) as Hbound.
  change (FGroup.g_order finite_curve_group <= 2*secp256k1_P+1) in Hbound.
  pose proof finite_curve_order_odd as [r Hr].
  assert (Hn : 0 < secp256k1_N) by (pose proof secp256k1_N_range; lia).
  assert (Hthree : 2 * secp256k1_P + 1 < 3 * secp256k1_N) by (vm_compute; reflexivity).
  assert (Hnonneg : 0 <= FGroup.g_order finite_curve_group).
  { unfold FGroup.g_order; lia. }
  assert (Hqlim : 0 <= q < 3) by nia.
  assert (Hnodd : Z.Odd secp256k1_N).
  { apply Z.odd_spec; vm_compute; reflexivity. }
  destruct Hnodd as [s Hs].
  assert (q = 1) by nia.
  subst q; lia.
Qed.
Lemma cofactor_one : forall a, on_curve a -> smul secp256k1_N a = PInf.
Proof.
  intros a Ha.
  destruct (finite_point_surjective a Ha) as [b Hb].
  pose proof (@EGroup.fermat_gen _ (SMain.ceqb finite_ell_theory) _ b finite_curve_group
    (finite_curve_member b)) as H.
  rewrite finite_curve_order in H.
  apply (f_equal finite_point_to_raw) in H.
  rewrite finite_smul, Hb in H by (pose proof secp256k1_N_range; lia).
  exact H.
Qed.
Local Opaque finite_curve_group finite_G.
Lemma finite_list_full : forall (A : Set) (dec : forall a b : A, {a=b}+{a<>b}) (l1 l2 : list A),
  UList.ulist l1 -> incl l1 l2 -> length l1 = length l2 -> incl l2 l1.
Proof.
  intros A dec l1 l2 Hu Hi Hl a Ha.
  destruct (in_dec dec a l1) as [H|H]; [exact H|].
  exfalso.
  assert (Hu' : UList.ulist (a::l1)) by (constructor; assumption).
  assert (Hi' : incl (a::l1) l2).
  { intros b [Hb|Hb]; [subst; exact Ha|apply Hi; exact Hb]. }
  pose proof (UList.ulist_incl_length A _ _ Hu' Hi') as Hbad.
  cbn [length] in Hbad; lia.
Qed.
Lemma finite_G_generates : forall a : FiniteCurve,
  exists k, 0 <= k < secp256k1_N /\ a = EGroup.gpow finite_G finite_curve_group k.
Proof.
  intro a.
  assert (Hlen : length (EGroup.support (SMain.ceqb finite_ell_theory) finite_G finite_curve_group) =
    length (FGroup.s finite_curve_group)).
  { pose proof (eq_trans finite_G_order_exact (eq_sym finite_curve_order)) as H.
    unfold EGroup.e_order, FGroup.g_order in H.
    apply Nat2Z.inj in H; exact H. }
  assert (Hin : In a (EGroup.support (SMain.ceqb finite_ell_theory) finite_G finite_curve_group)).
  { exact (finite_list_full FiniteCurve (SMain.ceqb finite_ell_theory)
      (EGroup.support (SMain.ceqb finite_ell_theory) finite_G finite_curve_group)
      (FGroup.s finite_curve_group)
      (@EGroup.support_ulist _ (SMain.ceqb finite_ell_theory) _ finite_G finite_curve_group
        (finite_curve_member finite_G))
      (@EGroup.support_incl_G _ (SMain.ceqb finite_ell_theory) _ finite_G finite_curve_group
        (finite_curve_member finite_G)) Hlen a (finite_curve_member a)). }
  pose proof (@EGroup.support_gpow _ (SMain.ceqb finite_ell_theory) _ finite_G finite_curve_group
    (finite_curve_member finite_G) a Hin) as H.
  pose proof finite_G_order_exact as Horder.
  unfold EGroup.e_order in Horder.
  rewrite Horder in H; exact H.
Qed.
Lemma G_generates : forall a, on_curve a -> exists k, 0 <= k < secp256k1_N /\ a = smul k G.
Proof.
  intros a Ha; destruct (finite_point_surjective a Ha) as [b Hb].
  destruct (finite_G_generates b) as [k [Hk Hpow]].
  exists k; split; [exact Hk|].
  apply (f_equal finite_point_to_raw) in Hpow.
  rewrite finite_smul, finite_G_coordinates, Hb in Hpow by lia.
  exact Hpow.
Qed.
Lemma pmul_lambda_smul_pos : forall k a, on_curve a ->
  pmul_lambda (repeat_addition' k a) = repeat_addition' k (pmul_lambda a).
Proof.
  induction k as [k IH|k IH|]; intros a Ha; cbn [repeat_addition'].
  - change (pmul_lambda (padd a (pdouble (repeat_addition' k a))) =
      padd (pmul_lambda a) (pdouble (repeat_addition' k (pmul_lambda a)))).
    rewrite pmul_lambda_add by auto using pdouble_on_curve, repeat_addition_binary_on_curve.
    rewrite pmul_lambda_double, IH by exact Ha.
    reflexivity.
  - rewrite pmul_lambda_double, IH by exact Ha.
    reflexivity.
  - reflexivity.
Qed.
Lemma pmul_lambda_smul_nonnegative : forall k a, 0 <= k -> on_curve a ->
  pmul_lambda (smul k a) = smul k (pmul_lambda a).
Proof.
  intros [|k|k] a Hk Ha; cbn [smul].
  - reflexivity.
  - apply pmul_lambda_smul_pos; exact Ha.
  - lia.
Qed.
Lemma lambda_endo : forall a, on_curve a -> pmul_lambda a = smul secp256k1_lambda a.
Proof.
  intros a Ha.
  destruct (G_generates a Ha) as [k [Hk Hpoint]].
  rewrite Hpoint.
  rewrite pmul_lambda_smul_nonnegative by (try lia; exact on_curve_G).
  rewrite lambda_G_certificate.
  rewrite <- !smul_mul by exact on_curve_G.
  rewrite Z.mul_comm.
  reflexivity.
Qed.

(** [k |-> k * G], from the scalars into the curve.  Its codomain is the
    curve group of [law], closure being
    [smul_on_curve] at [G]. *)
Definition scalar_to_curve (k : Scalar) : CurvePoint :=
  exist _ (smul (scalar_val k) G) (smul_on_curve (scalar_val k) G on_curve_G).

(** Multiplying [G] only sees the scalar mod [n]: write [k = n*q + r], then
    [k*G = q*(n*G) + r*G = r*G] because [n*G] is the identity ([G_order]). *)
Lemma smul_G_mod : forall k : Z, smul (k mod secp256k1_N) G = smul k G.
Proof.
  intros k.
  pose proof secp256k1_N_range as Hn.
  rewrite (Z.div_mod k secp256k1_N) at 2 by lia.
  rewrite smul_add by exact on_curve_G.
  rewrite (Z.mul_comm secp256k1_N).
  rewrite smul_mul by exact on_curve_G.
  rewrite (proj1 G_order).
  rewrite smul_PInf.
  rewrite padd_PInf_l.
  reflexivity.
Qed.

(** The map is a homomorphism from the additive group of scalars into the
    curve group: [(x + y) * G = x*G + y*G].  This is the whole of the
    scheme's correctness argument, [s*G = k*G + e*(d*G)] in
    [correct].
    See https://wuille.net/posts/secp256k1-tutorial/#23-isomorphism-between-scalars-and-points *)
Lemma scalar_to_curve_hom : Homomorphism scalar_to_curve.
Proof.
  intros x y.
  apply curve_point_eq.
  cbn [add CurvePoint_add Scalar_add scalar_to_curve cp_add proj1_sig scalar_val scalar_add scalar_reduce].
  rewrite smul_G_mod.
  apply smul_add.
  exact on_curve_G.
Qed.

(** The public scalar action reaches the same coordinates as the
    internal representation. Its result already carries validity. *)

#[local] Existing Instance group.Point_zero.
#[local] Existing Instance group.Point_add.
#[local] Existing Instance group.Point_neg.
#[local] Existing Instance group.point_group.

Definition scalar_to_point (k : Scalar) : group.Point :=
  group.smul' (scalar_val k) group.G.

Lemma scalar_to_point_hom : Homomorphism scalar_to_point.
Proof.
  intros x y.
  apply group.point_eq_ext.
  unfold scalar_to_point.
  change (group.point_coordinates
    (group.smul' (scalar_val (scalar_add x y)) group.G) =
    group.point_coordinates (group.padd
      (group.smul' (scalar_val x) group.G)
      (group.smul' (scalar_val y) group.G))).
  rewrite group.point_coordinates_add, !group.point_coordinates_smul.
  change (smul (scalar_val (scalar_add x y)) G =
    padd (smul (scalar_val x) G) (smul (scalar_val y) G)).
  cbn [scalar_val scalar_add scalar_reduce].
  rewrite smul_G_mod.
  apply smul_add.
  exact on_curve_G.
Qed.

End order.
(* end hide *)

(** ** 5.8 Certified Curve Results *)

(** The generator order is [n]. The first equation states that [n]
    copies give the identity. The second states that fewer positive
    copies cannot do so. The hidden proof uses a checked projective
    calculation and the primality of [n]. *)

(* begin hide *)
Module curve_results.
Import Math.algebra Math.field Math.scalar.
Local Open Scope Z_scope.
(* end hide *)

Lemma generator_order :
  group.smul' secp256k1_N group.G = group.PInf /\
  forall k : Z, (0 < k < secp256k1_N)%Z ->
    group.smul' k group.G <> group.PInf.
Proof.
  split.
  - apply group.point_eq_ext.
    rewrite group.point_coordinates_smul.
    exact (proj1 order.G_order).
  - intros k Hk H.
    apply (f_equal group.point_coordinates) in H.
    rewrite group.point_coordinates_smul in H.
    exact (proj2 order.G_order k Hk H).
Qed.

(** Multiplying any valid point by [n] gives the identity. The proof
    shows that the whole curve group has exactly [n] points. *)

Lemma curve_cofactor_one (a : group.Point) :
  group.smul' secp256k1_N a = group.PInf.
Proof.
  apply group.point_eq_ext.
  rewrite group.point_coordinates_smul.
  apply order.cofactor_one.
  exact (group.point_valid a).
Qed.

(** The coordinate map has exactly the same result as multiplication
    by [lambda]. The proof first certifies the map on [G], then uses
    preservation of addition and generation by [G] to cover every
    point. *)

Lemma glv_preserves_multiplication (a : group.Point) :
  group.pmul_lambda a = group.smul' group.secp256k1_lambda a.
Proof.
  apply group.point_eq_ext.
  rewrite group.point_coordinates_smul.
  assert (Hmap : group.point_coordinates (group.pmul_lambda a) =
    raw.pmul_lambda (group.point_coordinates a)).
  { destruct a; reflexivity. }
  rewrite Hmap.
  apply order.lambda_endo.
  exact (group.point_valid a).
Qed.

(* begin hide *)
End curve_results.
(* end hide *)



(* begin hide *)
Module roots.
Import Math.fermat.
Import Math.field_prime.
Import Math.residues.
Import Math.ell.
Import Math.group.
(** Square root completeness and the even representative of a curve point. *)

Open Scope Z_scope.
Local Open Scope math_scope.

Lemma fe_power_value a exponent :
  fe_val (power' a exponent) =
  (fe_val a ^ Z.of_N exponent mod secp256k1_P)%Z.
Proof.
  apply (pow_hom Fe Fe_mul Fe_one fe_val secp256k1_P).
  - exact P_pos.
  - apply fe_range.
  - reflexivity.
  - intros x y. reflexivity.
Qed.

Lemma fe_sqrt_square_candidate (y : Fe) :
  let r := power' (y * y) fe_sqrt_exponent in r * r = y * y.
Proof.
  cbn zeta.
  apply fe_eq_ext.
  cbn [mul Fe_mul fe_mul fe_val fe_reduce].
  rewrite !fe_power_value, fe_sqrt_exponent_spec.
  cbn [mul Fe_mul fe_mul fe_val fe_reduce].
  rewrite !Z.mod_pow_l, Zmult_mod_idemp_l, Zmult_mod_idemp_r.
  set (q := ((secp256k1_P + 1) / 4)%Z).
  assert (Hq : (0 <= q)%Z) by (unfold q, secp256k1_P; vm_compute; discriminate).
  replace (fe_val y * fe_val y)%Z with (fe_val y ^ 2)%Z by ring.
  rewrite <- Z.pow_add_r by lia.
  rewrite <- Z.pow_mul_r by lia.
  replace (2 * (q + q))%Z with ((secp256k1_P - 1) + 2)%Z
    by (unfold q, secp256k1_P; vm_compute; reflexivity).
  destruct (Z.eq_dec (fe_val y) 0) as [Hz|Hz].
  - rewrite Hz, !Z.pow_0_l by (unfold secp256k1_P; lia).
    reflexivity.
  - rewrite Z.pow_add_r by (unfold secp256k1_P; lia).
    rewrite Z.mul_mod by (pose proof P_pos; lia).
    rewrite (fermat_little secp256k1_P (fe_val y)).
    + rewrite Z.mul_1_l, Z.mod_mod by (pose proof P_pos; lia). reflexivity.
    + exact secp256k1_P_prime.
    + apply rel_prime_of_range.
      * exact secp256k1_P_prime.
      * pose proof (fe_range y). lia.
Qed.

Lemma fe_sqrt_complete (a y : Fe) :
  y * y = a -> exists r, fe_sqrt a = Some r.
Proof.
  intros <-.
  unfold fe_sqrt, pow, Power_N.
  pose proof (fe_sqrt_square_candidate y) as Hsquare.
  cbn zeta in Hsquare.
  rewrite Hsquare.
  change (exists r, (if Z.eqb (fe_val (y * y)) (fe_val (y * y))
    then Some (power' (y * y) fe_sqrt_exponent) else None) = Some r).
  rewrite Z.eqb_refl.
  eexists. reflexivity.
Qed.

Lemma fe_product_zero (a b : Fe) :
  a * b = 0%F -> a = 0%F \/ b = 0%F.
Proof.
  intro Hproduct.
  destruct (fe_eq_dec a 0%F) as [Hz|Hz].
  - left. exact Hz.
  - right.
    change (fe_mul a b = fe_zero) in Hproduct.
    replace b with (fe_mul (fe_inv a) (fe_mul a b)).
    + rewrite Hproduct. ring.
    + replace (fe_mul (fe_inv a) (fe_mul a b)) with
        (fe_mul (fe_mul (fe_inv a) a) b) by ring.
      rewrite fe_inv_l by exact Hz. ring.
Qed.

Lemma fe_square_roots (a b : Fe) :
  a * a = b * b -> a = b \/ a = - b.
Proof.
  intro Hsquare.
  change (fe_mul a a = fe_mul b b) in Hsquare.
  assert (Hproduct : fe_mul (fe_add a (fe_negate b)) (fe_add a b) = fe_zero).
  { replace (fe_mul (fe_add a (fe_negate b)) (fe_add a b)) with
      (fe_add (fe_mul a a) (fe_negate (fe_mul b b))) by ring.
    rewrite Hsquare. ring. }
  destruct (fe_product_zero _ _ Hproduct) as [Heq|Heq].
  - left.
    replace a with (fe_add (fe_add a (fe_negate b)) b) by ring.
    rewrite Heq. ring.
  - right.
    change (a = fe_negate b).
    replace a with (fe_add (fe_add a b) (fe_negate b)) by ring.
    rewrite Heq. ring.
Qed.

Lemma fe_is_odd_negate (a : Fe) :
  a <> 0%F -> fe_is_odd (- a) = negb (fe_is_odd a).
Proof.
  intro Hnonzero.
  assert (Hvalue : fe_val a <> 0)
    by (intro Hz; apply Hnonzero, fe_eq_ext; exact Hz).
  pose proof (fe_range a) as Hrange.
  unfold fe_is_odd.
  change (Z.odd ((secp256k1_P - fe_val a) mod secp256k1_P) =
    negb (Z.odd (fe_val a))).
  rewrite Z.mod_small by lia.
  rewrite Z.odd_sub.
  assert (Hpodd : Z.odd secp256k1_P = true) by (vm_compute; reflexivity).
  rewrite Hpodd.
  destruct (Z.odd (fe_val a)); reflexivity.
Qed.

Lemma fe_negate_odd_is_even (a : Fe) :
  fe_is_odd a = true -> fe_is_odd (- a) = false.
Proof.
  intro Hodd.
  rewrite fe_is_odd_negate.
  - rewrite Hodd. reflexivity.
  - intro Hz. subst a. discriminate Hodd.
Qed.

Lemma fe_even_root_unique (a b : Fe) :
  a * a = b * b ->
  fe_is_odd a = false -> fe_is_odd b = false -> a = b.
Proof.
  intros Hsquare Ha Hb.
  destruct (fe_square_roots a b Hsquare) as [Heq|Heq].
  - exact Heq.
  - destruct (fe_eq_dec b 0%F) as [Hz|Hz].
    + subst b. rewrite Heq. apply fe_eq_ext. reflexivity.
    + rewrite Heq, fe_is_odd_negate, Hb in Ha by exact Hz.
      discriminate.
Qed.

Lemma checked_sqrt_value (a : Fe) :
  option_map (@proj1_sig Fe (fun y => y * y = a)) (checked_sqrt a) = fe_sqrt a.
Proof.
  unfold checked_sqrt.
  generalize (fe_sqrt_valid a).
  generalize (fe_sqrt a).
  intros [r|] Hvalid; reflexivity.
Qed.

Lemma lift_x_even_complete (x y : Fe) (valid : y * y = x * x * x + curve_b) :
  fe_is_odd y = false -> lift_x_even x = Some (PAff x y valid).
Proof.
  intro Heven.
  destruct (fe_sqrt_complete _ y valid) as [r Hroot].
  pose proof (checked_sqrt_value (x * x * x + curve_b)) as Hchecked.
  unfold lift_x_even.
  destruct (checked_sqrt (x * x * x + curve_b)) as [[z Hz]|].
  - destruct (fe_is_odd z) eqn:Hzodd.
    + f_equal. apply point_eq_ext. cbn [point_coordinates].
      f_equal. apply fe_even_root_unique.
      * etransitivity. apply negated_root_valid. exact Hz. symmetry. exact valid.
      * apply fe_negate_odd_is_even. exact Hzodd.
      * exact Heven.
    + f_equal. apply point_eq_ext. cbn [point_coordinates].
      f_equal. apply fe_even_root_unique.
      * rewrite Hz, valid. reflexivity.
      * exact Hzodd.
      * exact Heven.
  - cbn [option_map] in Hchecked.
    rewrite Hroot in Hchecked.
    discriminate.
Qed.


End roots.
(* end hide *)


(* begin hide *)
Module sha256.
Import Math.bytes.
(* end hide *)
(** * 6. SHA-256 *)

(** SHA256 maps a byte message to a 32-byte digest. The same input
    gives the same digest. The hash has no secret key and does not
    encrypt the message.

    The input must contain fewer than [2^61] bytes, so its bit length
    fits below [2^64]. The largest permitted byte length is
    [2^61 - 1]. This limit comes from the padding rule in
    {{https://nvlpubs.nist.gov/nistpubs/FIPS/NIST.FIPS.180-4.pdf}FIPS
    180-4 section 5.1.1}.

    The algorithm first pads the input into 64-byte blocks. Each
    block gives sixteen 32-bit words. A recurrence expands them to 64
    schedule words. The rounds mix these into eight state words,
    which form the final digest.

    The definitions make these stages executable and comparable with
    test vectors. The word and array operations are described in the
    {{#appendix-word-operations}appendix}. *)

(* begin hide *)


Open Scope Z_scope.
Local Open Scope word_scope.

Declare Scope array_scope.
Delimit Scope array_scope with array.
Notation "left ++ right" := (array_app left right)
  (at level 60, right associativity) : array_scope.
Local Open Scope array_scope.
(* end hide *)

(** [sha256_length_valid] names the input limit above. It accepts a
    natural-number byte count and compares its integer value with
    [2^61]. *)
Definition sha256_length_valid (n : nat) : Prop :=
  Z.of_nat n < 2 ^ 61.
(* begin hide *)
Arguments sha256_length_valid n /.
(* end hide *)

(* ================================================================= *)
(** ** 6.1 Words and Logical Functions *)

(** A bit is one binary digit, either zero or one. A [Word 32] holds
    exactly 32 bit positions and an integer between zero and [2^32-1].
    The operators [and], [xor] and [not] act independently at every
    position. A {{https://en.wikipedia.org/wiki/Bitwise_operation}
    visual overview} illustrates these rules.

    Addition uses [word_add], which reduces the integer sum modulo
    [2^32]. An overflow therefore wraps around just as it does in a
    32-bit machine word. A right shift, [shr], discards low bits. A
    right rotation, [rotr], moves them around to the high end instead.
    Every shift count below carries proof that it is less than 32. *)

(** The _choice function_ uses each bit of [x] to select between the
    corresponding bits of [y] and [z]. Where [x] is one, the result
    takes [y]. Where [x] is zero, it takes [z], FIPS equation 4.2: *)
Definition Ch (x y z : Word 32) : Word 32 :=
  (x and y) xor ((not x) and z).

(** The _majority function_ returns the value held by at least two of
    its three input bits. At each position, zero, one or three of the
    pairwise conjunctions are set. Their xor is exactly the majority
    bit, FIPS equation 4.3: *)
Definition Maj (x y z : Word 32) : Word 32 :=
  (x and y) xor (x and z) xor (y and z).

(** The first large sigma function mixes three rotated views of [x]
    without dropping bits. A compression round applies it to working
    word [a], FIPS equation 4.4: *)
Program Definition Sigma0 (x : Word 32) : Word 32 :=
  (x rotr 2) xor (x rotr 13) xor (x rotr 22).
(* begin hide *)
Solve Obligations with
  (intros; (* Each rotation count is less than 32. *) lia).
(* end hide *)

(** The second large sigma function uses three different rotations.
    A compression round applies it to working word [e], FIPS equation
    4.5: *)
Program Definition Sigma1 (x : Word 32) : Word 32 :=
  (x rotr 6) xor (x rotr 11) xor (x rotr 25).
(* begin hide *)
Solve Obligations with
  (intros; (* Each rotation count is less than 32. *) lia).
(* end hide *)

(** The first small sigma function helps derive new schedule words.
    Its rotations rearrange all bits, while its right shift drops
    three low bits and introduces zeros, FIPS equation 4.6: *)
Program Definition sigma0 (x : Word 32) : Word 32 :=
  (x rotr 7) xor (x rotr 18) xor (x shr 3).
(* begin hide *)
Solve Obligations with
  (intros; (* Each shift or rotation count is less than 32. *) lia).
(* end hide *)

(** The second small sigma function completes the schedule recurrence
    with different distances, FIPS equation 4.7: *)
Program Definition sigma1 (x : Word 32) : Word 32 :=
  (x rotr 17) xor (x rotr 19) xor (x shr 10).
(* begin hide *)
Solve Obligations with
  (intros; (* Each shift or rotation count is less than 32. *) lia).
(* end hide *)

(* ================================================================= *)
(** ** 6.2 Constants and State *)

(** SHA-256 assigns a public constant to each of its 64 rounds.
    {{https://nvlpubs.nist.gov/nistpubs/FIPS/NIST.FIPS.180-4.pdf}FIPS
    180-4 section 4.2.2} derives them from the fractional parts of cube
    roots of primes, fixing one reproducible table. The array type
    ensures that one valid [Word 32] is available for every round: *)
Program Definition sha256_k : Array (Word 32) 64 :=
  @words 32
    [ 0x428a2f98; 0x71374491; 0xb5c0fbcf; 0xe9b5dba5;
      0x3956c25b; 0x59f111f1; 0x923f82a4; 0xab1c5ed5;
      0xd807aa98; 0x12835b01; 0x243185be; 0x550c7dc3;
      0x72be5d74; 0x80deb1fe; 0x9bdc06a7; 0xc19bf174;
      0xe49b69c1; 0xefbe4786; 0x0fc19dc6; 0x240ca1cc;
      0x2de92c6f; 0x4a7484aa; 0x5cb0a9dc; 0x76f988da;
      0x983e5152; 0xa831c66d; 0xb00327c8; 0xbf597fc7;
      0xc6e00bf3; 0xd5a79147; 0x06ca6351; 0x14292967;
      0x27b70a85; 0x2e1b2138; 0x4d2c6dfc; 0x53380d13;
      0x650a7354; 0x766a0abb; 0x81c2c92e; 0x92722c85;
      0xa2bfe8a1; 0xa81a664b; 0xc24b8b70; 0xc76c51a3;
      0xd192e819; 0xd6990624; 0xf40e3585; 0x106aa070;
      0x19a4c116; 0x1e376c08; 0x2748774c; 0x34b0bcb5;
      0x391c0cb3; 0x4ed8aa4a; 0x5b9cca4f; 0x682e6ff3;
      0x748f82ee; 0x78a5636f; 0x84c87814; 0x8cc70208;
      0x90befffa; 0xa4506ceb; 0xbef9a3f7; 0xc67178f2 ] _.
(* begin hide *)
Next Obligation.
  (* Every literal is in the range of a 32-bit word. *)
  repeat constructor; lia.
Qed.
(* end hide *)

(** A hash needs a small memory that one block can update and pass to
    the next block. SHA-256 calls that memory its hash value. It is
    eight 32-bit words, which together account for the 256 bits in the
    name of the algorithm. Named fields expose the working variables
    [a] through [h] used by the standard in every round. Between blocks
    the record is the running hash value. During a block the same
    fields hold the working variables: *)
Record Sha256_state := mkSha256_state {
  sha256_a : Word 32;
  sha256_b : Word 32;
  sha256_c : Word 32;
  sha256_d : Word 32;
  sha256_e : Word 32;
  sha256_f : Word 32;
  sha256_g : Word 32;
  sha256_h : Word 32
}.

(** The first block has no earlier state to inherit. FIPS section
    5.3.3 therefore fixes eight public initial words, derived from the
    fractional parts of square roots of primes. The spelling and order
    below match the standard. This initial state is fixed, and the
    input blocks determine each subsequent state: *)
Program Definition sha256_iv : Sha256_state :=
  mkSha256_state
    (word_of_Z 32 0x6a09e667 _)
    (word_of_Z 32 0xbb67ae85 _)
    (word_of_Z 32 0x3c6ef372 _)
    (word_of_Z 32 0xa54ff53a _)
    (word_of_Z 32 0x510e527f _)
    (word_of_Z 32 0x9b05688c _)
    (word_of_Z 32 0x1f83d9ab _)
    (word_of_Z 32 0x5be0cd19 _).
(* begin hide *)
Solve Obligations with
  (intros; (* Every IV literal is a valid 32-bit word. *) lia).
(* end hide *)

(* ================================================================= *)
(** ** 6.3 Padding *)

(** _Padding_ turns a message into complete 64-byte blocks for
    compression while recording its original length. It appends a
    marker byte, some zero bytes, then the message length in bits as
    eight big-endian bytes.

    The marker [0x80], hexadecimal for 128, is binary one followed by
    seven zeros. It is the first one bit required by FIPS, completed
    to a byte. The zero bytes then stop at position 56 in a block,
    leaving positions 56 through 63 for the eight-byte length field.
    If position 56 has passed, padding continues into a new block. The
    length field separates message bytes from zeros added by padding. *)

(** For a message of [n] bytes, [(55-n) mod 64] is the smallest
    non-negative number of zero bytes between the marker and the
    length field. The message, marker and zeros then occupy 56 byte
    positions modulo 64, leaving eight for the length: *)
Definition sha256_padzeros (n : Z) : Z := (55 - n) mod 64.

(** FIPS states padding in bits. For byte messages, each zero byte
    contributes eight zero bits, and the marker contributes seven
    more after its leading one. Together with that leading one, the
    length field begins at bit position 448 modulo 512. *)
(* begin hide *)
Definition sha256_padbits (n : Z) : Z :=
  8 * sha256_padzeros n + 7.

(** A remainder modulo 64 is always between zero and 63. Establishing
    that range also proves that conversion to a natural-number
    repetition count preserves its value: *)
Lemma sha256_padzeros_range (n : Z) :
  0 <= sha256_padzeros n < 64.
Proof.
  (* A remainder modulo 64 is its non-negative representative. *)
  apply Z.mod_pos_bound.
  lia.
Qed.

(** The next result connects the byte formula to FIPS section 5.1.1.
    It says that [sha256_padbits n] is non-negative, reaches bit
    position 448 modulo 512, and is no larger than any other
    non-negative solution. The proof first establishes the range and
    congruence. Minimality then follows because congruent solutions
    differ by complete 512-bit periods: *)
Lemma sha256_padbits_spec (n : Z) :
  0 <= n ->
  0 <= sha256_padbits n /\
  (8 * n + 1 + sha256_padbits n) mod 512 = 448 /\
  (forall k, 0 <= k ->
    (8 * n + 1 + k) mod 512 = 448 -> sha256_padbits n <= k).
Proof.
  intros nonnegative.
  pose proof (sha256_padzeros_range n) as padzeros_range.
  assert (padbits_range : 0 <= sha256_padbits n < 512).
  { (* Scaling at most 63 zero bytes gives fewer than 512 bits. *)
    unfold sha256_padbits.
    lia. }
  assert (congruence :
    (8 * n + 1 + sha256_padbits n) mod 512 = 448).
  { (* Factor eight so the byte remainder is taken modulo 64. *)
    unfold sha256_padbits, sha256_padzeros.
    replace (8 * n + 1 + (8 * ((55 - n) mod 64) + 7))
      with (8 * ((55 - n) mod 64 + (n + 1))) by lia.
    replace 512 with (8 * 64) by lia.
    rewrite Z.mul_mod_distr_l by lia.
    rewrite Z.add_mod_idemp_l by lia.
    replace (55 - n + (n + 1)) with 56 by lia.
    reflexivity. }
  split.
  { (* The range proof already establishes non-negativity. *)
    lia. }
  split.
  { (* The preceding modular calculation is the FIPS congruence. *)
    exact congruence. }
  intros k k_nonnegative k_congruence.
  pose proof (Z.div_mod (8 * n + 1 + k) 512 ltac:(lia)) as k_divmod.
  pose proof
    (Z.div_mod (8 * n + 1 + sha256_padbits n) 512 ltac:(lia))
    as pad_divmod.
  rewrite k_congruence in k_divmod.
  rewrite congruence in pad_divmod.
  (* Congruent non-negative values differ by whole periods. The one
     in the first period is therefore minimal. *)
  lia.
Qed.
(* end hide *)

(** Adding the message, marker, zero bytes and length field gives the
    exact preprocessed size. Its four terms follow that appended
    order: *)
Definition sha256_padded_length (n : nat) : nat :=
  n + 1 + Z.to_nat (sha256_padzeros (Z.of_nat n)) + 8.

(** Integer arithmetic is more convenient for the divisibility proof.
    This bridge restates the natural-number length as an integer: *)
Lemma sha256_padded_length_Z (n : nat) :
  Z.of_nat (sha256_padded_length n) =
  Z.of_nat n + 1 + sha256_padzeros (Z.of_nat n) + 8.
(* begin hide *)
Proof.
  unfold sha256_padded_length.
  repeat rewrite Nat2Z.inj_add.
  rewrite Z2Nat.id.
  { (* Conversion preserves the non-negative padding length. *)
    lia. }
  (* The remainder definition makes the padding length non-negative. *)
  pose proof (sha256_padzeros_range (Z.of_nat n)).
  lia.
Qed.
(* end hide *)

(** The padded message always contains a whole number of blocks. *)
Lemma sha256_padded_length_block (n : nat) :
  (sha256_padded_length n mod 64 = 0)%nat.
(* begin hide *)
Proof.
  apply Nat2Z.inj.
  rewrite Nat2Z.inj_mod.
  rewrite sha256_padded_length_Z.
  unfold sha256_padzeros.
  replace
    (Z.of_nat n + 1 + (55 - Z.of_nat n) mod 64 + 8)
    with (Z.of_nat n + 9 + (55 - Z.of_nat n) mod 64) by lia.
  rewrite Z.add_mod_idemp_r by lia.
  replace (Z.of_nat n + 9 + (55 - Z.of_nat n)) with 64 by lia.
  reflexivity.
Qed.
(* end hide *)

(** Padding appends its pieces in the order specified by FIPS.
    The names [marker], [zeros] and [bit_length] expose its three
    pieces before they are appended to [msg]. The input bound
    [n < 2^61] proves that [8*n] fits in the 64-bit length field.
    Checked constructors reject an invalid marker, zero byte or
    length: *)
Program Definition sha256_pad {n : nat} (msg : Array (Word 8) n)
    (length_bound : sha256_length_valid n)
  : Array (Word 8) (sha256_padded_length n) :=
  let marker : Array (Word 8) 1 :=
    array_of_list [(word_of_Z 8) 128 _] in
  let zeros := array_repeat ((word_of_Z 8) 0 _)
      (Z.to_nat (sha256_padzeros (Z.of_nat n))) in
  let bit_length : Array (Word 8) 8 :=
    bytes_of_Z (8 * Z.of_nat n) 8 _ in
  ((msg ++ marker) ++ zeros) ++ bit_length.
(* begin hide *)
Next Obligation.
  (* The marker byte is in the byte range. *)
  lia.
Qed.
Next Obligation.
  split.
  { (* The repeated zero byte is non-negative. *)
    lia. }
  (* Zero is strictly below the byte modulus. *)
  lia.
Qed.
Next Obligation.
  (* The 2^61 byte bound makes the bit length fit in eight bytes. *)
  change (Z.of_nat n < 2305843009213693952) in length_bound.
  change (0 <= 8 * Z.of_nat n < 18446744073709551616).
  lia.
Qed.
(* end hide *)

(** Dividing the padded length by 64 gives its number of blocks: *)
Definition sha256_block_count (n : nat) : nat :=
  (sha256_padded_length n / 64)%nat.

(** The zero remainder above means multiplication recovers the exact
    padded length, so chunking cannot discard any bytes. The proof uses
    the quotient and remainder law: *)
Lemma sha256_block_count_exact (n : nat) :
  (sha256_block_count n * 64 = sha256_padded_length n)%nat.
(* begin hide *)
Proof.
  pose proof (Nat.div_mod (sha256_padded_length n) 64 ltac:(lia))
    as quotient_remainder.
  rewrite sha256_padded_length_block in quotient_remainder.
  unfold sha256_block_count.
  (* The zero remainder leaves exactly the quotient times 64. *)
  lia.
Qed.
(* end hide *)

(** A complete SHA-256 message block contains 64 bytes, or 512 bits.
    Giving compression this input type rules out a short block: *)
Definition Sha256_block : Type := Array (Word 8) 64.

(** Preprocessing finishes by reshaping the padded byte array into the
    exact number of complete blocks proved above. [array_chunks]
    preserves every byte and its order: *)
Definition sha256_blocks {n : nat} (msg : Array (Word 8) n)
    (length_bound : sha256_length_valid n)
  : Array Sha256_block (sha256_block_count n) :=
  array_chunks (sha256_block_count n) 64
    (array_cast (eq_sym (sha256_block_count_exact n))
      (sha256_pad msg length_bound)).

(* ================================================================= *)
(** ** 6.4 Parsing and the Message Schedule *)

(** A block arrives as bytes, but the round functions operate on
    32-bit words. Parsing cuts the 64 bytes into sixteen groups of
    four. [word_of_bytes] reads each group in big-endian order, so
    the first byte supplies the most significant eight bits. The
    result type rules out a partial group or a different word count: *)
Definition sha256_words_of_block (block : Sha256_block)
  : Array (Word 32) 16 :=
  array_map (@word_of_bytes 4) (array_chunks 16 4 block).

(** The _message schedule_ supplies one word to each of the 64 rounds.
    Rather than repeat the sixteen input words, SHA-256 expands them.
    For index [i] from 16 onward, FIPS combines words at [i-2], [i-7],
    [i-15] and [i-16]. The two small sigma functions spread changes
    from earlier words into later ones.

    One step appends that recurrence to a schedule prefix. The prefix
    has at least sixteen words, which proves all four backward indices
    refer to existing entries. Each [array_get] carries that proof, so
    no missing predecessor can be replaced by a default word. The
    recurrence adds words modulo [2^32] with [word_add]: *)
Program Definition sha256_schedule_step {i : nat}
    (lower : (16 <= i)%nat) (schedule : Array (Word 32) i)
  : Array (Word 32) (S i) :=
  let W2 := array_get schedule (i - 2) _ in
  let W7 := array_get schedule (i - 7) _ in
  let W15 := array_get schedule (i - 15) _ in
  let W16 := array_get schedule (i - 16) _ in
  array_snoc schedule
    (word_add (word_add (word_add (sigma1 W2) W7) (sigma0 W15)) W16).
(* begin hide *)
Next Obligation.
  (* Since i is at least sixteen, W at i minus two exists. *)
  lia.
Qed.
Next Obligation.
  (* Since i is at least sixteen, W at i minus seven exists. *)
  lia.
Qed.
Next Obligation.
  (* Since i is at least sixteen, W at i minus fifteen exists. *)
  lia.
Qed.
Next Obligation.
  (* Since i is at least sixteen, W at i minus sixteen exists. *)
  lia.
Qed.
(* end hide *)

(** The recursive helper repeats a valid step [count] times while
    carrying the growing length in its result type. Each call consumes
    one requested step and appends one word: *)
Program Fixpoint sha256_schedule_extend (count i : nat)
    (lower : (16 <= i)%nat) (schedule : Array (Word 32) i) {struct count}
  : Array (Word 32) (i + count) :=
  match count with
  | O => array_cast _ schedule
  | S remaining =>
      array_cast _
        (sha256_schedule_extend remaining (S i) _
          (sha256_schedule_step lower schedule))
  end.

(** Starting from sixteen parsed words and appending 48 derived words
    produces the schedule required by FIPS section 6.2.2 step 1. Its
    type fixes the length at 64, ready to pair with all 64 constants: *)
Program Definition sha256_schedule (block_words : Array (Word 32) 16)
  : Array (Word 32) 64 :=
  sha256_schedule_extend 48 16 _ block_words.

(* ================================================================= *)
(** ** 6.5 Compression *)

(** _Compression_ is the mixing core. One round takes the current eight
    working words, one public constant [Kt], and one schedule word
    [Wt]. [T1] combines [h], [Sigma1 e], [Ch e f g], [Kt] and [Wt].
    [T2] combines [Sigma0 a] and [Maj a b c]. The new [a] is [T1+T2],
    the new [e] is [d+T1], and the other six words move one position.
    Every addition wraps modulo [2^32], FIPS section 6.2.2 step 3: *)
Definition sha256_round (state : Sha256_state) (Kt Wt : Word 32)
  : Sha256_state :=
  let a := sha256_a state in
  let b := sha256_b state in
  let c := sha256_c state in
  let d := sha256_d state in
  let e := sha256_e state in
  let f := sha256_f state in
  let g := sha256_g state in
  let h := sha256_h state in
  let T1 := word_add
    (word_add (word_add (word_add h (Sigma1 e)) (Ch e f g)) Kt) Wt in
  let T2 := word_add (Sigma0 a) (Maj a b c) in
  mkSha256_state (word_add T1 T2) a b c (word_add d T1) e f g.

(** A complete block runs 64 rounds. Zipping the constant table with
    the schedule pairs entries at the same index, then [fold_left]
    passes each resulting state into the next round. Both arrays have
    length 64, so the zip cannot stop early: *)
Definition sha256_rounds (state : Sha256_state)
    (schedule : Array (Word 32) 64) : Sha256_state :=
  fold_left
    (fun current pair => sha256_round current (fst pair) (snd pair))
    (array_list (array_zip sha256_k schedule)) state.

(** After the rounds, FIPS section 6.2.2 step 4 adds each original
    state word to the working result in the same position. This
    feed-forward result becomes the incoming state for the next
    block: *)
Definition sha256_add_state (left right : Sha256_state)
  : Sha256_state :=
  mkSha256_state
    (word_add (sha256_a left) (sha256_a right))
    (word_add (sha256_b left) (sha256_b right))
    (word_add (sha256_c left) (sha256_c right))
    (word_add (sha256_d left) (sha256_d right))
    (word_add (sha256_e left) (sha256_e right))
    (word_add (sha256_f left) (sha256_f right))
    (word_add (sha256_g left) (sha256_g right))
    (word_add (sha256_h left) (sha256_h right)).

(** One application of compression is now the full FIPS sequence.
    Parse a block, expand its schedule, run its rounds, then add the
    incoming state back. Fixed intermediate sizes leave no malformed
    length case: *)
Definition sha256_compress (state : Sha256_state) (block : Sha256_block)
  : Sha256_state :=
  let schedule := sha256_schedule (sha256_words_of_block block) in
  sha256_add_state state (sha256_rounds state schedule).

(** A multi-block message chains compression in order. Each block sees
    the state produced by every block before it. The typed array itself
    supplies the block count, so no separate count can disagree: *)
Definition sha256_transform {n : nat} (state : Sha256_state)
    (blocks : Array Sha256_block n) : Sha256_state :=
  fold_left sha256_compress (array_list blocks) state.

(** Applications that repeatedly hash the same complete prefix can
    save the state after that prefix. Such a midstate starts at the
    standard initial value and transforms only the supplied blocks.
    The result can seed later calls to [sha256_transform]: *)
Definition sha256_midstate {n : nat} (blocks : Array Sha256_block n)
  : Sha256_state :=
  sha256_transform sha256_iv blocks.

(* ================================================================= *)
(** ** 6.6 Digest and Tagged Hashing *)

(** Compression leaves eight words in the state. FIPS fixes their
    output order as [a] through [h], the same order used throughout
    the computation. Collecting them in one typed array lets encoding
    map one operation over all eight: *)
Definition sha256_state_words (state : Sha256_state)
  : Array (Word 32) 8 :=
  array_of_list
    [ sha256_a state; sha256_b state; sha256_c state; sha256_d state;
      sha256_e state; sha256_f state; sha256_g state; sha256_h state ].

(** Each [Word 32] becomes four big-endian bytes. Flattening eight
    four-byte arrays produces the promised 32-byte digest. Its length
    follows directly from eight times four in the result type: *)
Definition sha256_bytes_of_state (state : Sha256_state)
  : Array (Word 8) 32 :=
  array_concat
    (array_map (@word_to_bytes 4) (sha256_state_words state)).

(** SHA-256 now composes the complete path. It pads the message, splits
    it into blocks, transforms those blocks from [sha256_iv], and
    encodes the final state. The length bound exists because FIPS
    reserves only 64 bits for the original bit length. All internal
    widths and lengths are carried by types: *)
Definition sha256 {n : nat} (msg : Array (Word 8) n)
    (length_bound : sha256_length_valid n) : Array (Word 8) 32 :=
  sha256_bytes_of_state
    (sha256_transform sha256_iv (sha256_blocks msg length_bound)).

(** A protocol may use SHA-256 for several purposes. _Tagged hashing_
    keeps those purposes apart by choosing a descriptive byte string
    [tag]. It hashes the tag once, repeats that 32-byte digest twice,
    then places the message after the resulting 64-byte prefix. The
    outer input is therefore two copies of [sha256 tag], followed by
    [msg]. This tag-derived prefix separates the intended uses.
    [tag_bound] checks the inner hash, and [outer_bound] checks the
    64-byte prefix followed by [msg]: *)
Definition tagged_hash {t n : nat} (tag : Array (Word 8) t)
    (msg : Array (Word 8) n) (tag_bound : sha256_length_valid t)
    (outer_bound : sha256_length_valid (64 + n)) : Array (Word 8) 32 :=
  let tag_digest := sha256 tag tag_bound in
  sha256 ((tag_digest ++ tag_digest) ++ msg) outer_bound.

(* begin hide *)
End sha256.
(* end hide *)


(* begin hide *)
Module schnorr.
Import Math.bytes.
Import Math.group.
Import Math.sha256.
(* end hide *)
(** * 7. Schnorr Signatures on secp256k1 *)

(** A BIP340 signature lets a verifier check authorization by the
    holder of a secret key. The construction combines the fields,
    curve points, and hash already defined.

    Signing follows these steps:
    - The secret scalar [d] selects the public point [P = d * G]. Its
      x coordinate is the public key.
    - A nonce scalar [k] selects [R = k * G]. The public and nonce
      points are normalized to even y coordinates.
    - Hashing the encoded coordinates and message gives a _challenge_
      [e].
    - The _response_ is [s = k + e * d]. The signature contains the x
      coordinate [r] of [R] and the scalar [s].

    Verification recomputes [s * G - e * P] and checks its x
    coordinate and even parity.

    Substitution gives [(k + e*d) * G - e * (d*G) = k * G]. The
    correctness statement below includes this argument together with
    normalization, encoding, and rejection cases. The
    {{https://bips.dev/340/}BIP340 specification} fixes these
    details. *)

(* begin hide *)


Open Scope Z_scope.
Local Open Scope math_scope.
Local Open Scope array_scope.
Local Open Scope char_scope.
Local Open Scope bytes_scope.
Local Obligation Tactic := intros.
(* end hide *)

(* ================================================================= *)
(** ** 7.1 Domain Tags *)

(** #<div class="spec-figure" data-figure="schnorr"></div># *)

(** A tag gives each hash a distinct purpose. [tagged_hash] prefixes
    the input with two copies of the tag hash. These prefixes
    distinguish the intended purposes of auxiliary masking, challenge
    creation and nonce derivation. BIP-340 assigns these ASCII tags: *)

(** ["BIP0340/aux"]. *)
Definition tag_bip340_aux : Array (Word 8) 11 :=
  chars ["B"; "I"; "P"; "0"; "3"; "4"; "0"; "/"; "a"; "u"; "x"].

(** ["BIP0340/challenge"]. *)
Definition tag_bip340_challenge : Array (Word 8) 17 :=
  chars ["B"; "I"; "P"; "0"; "3"; "4"; "0"; "/"; "c"; "h"; "a"; "l"; "l";
         "e"; "n"; "g"; "e"].

(** ["BIP0340/nonce"]. *)
Definition tag_bip340_nonce : Array (Word 8) 13 :=
  chars ["B"; "I"; "P"; "0"; "3"; "4"; "0"; "/"; "n"; "o"; "n"; "c"; "e"].

(* begin hide *)
Local Close Scope char_scope.
(* end hide *)

(** The tags separate the three hash uses even if their inputs happen
    to contain the same bytes. *)

(* ================================================================= *)
(** ** 7.2 Byte Inputs *)

(** A message is an [Array (Word 8) n]. The index [n] records its exact
    length in the type. SHA-256 appends the bit length in an unsigned
    64-bit field, which places the following bound on a complete
    challenge or nonce transcript: *)

Definition message_length_valid (n : nat) : Prop :=
  sha256_length_valid (128 + n).

(** The transcript adds 128 bytes to the message. They consist of the
    64-byte tagged hash prefix and two 32-byte values. Thus the
    message can contain at most [2^61 - 129] bytes. The proof
    argument checks this bound at every hash call. *)

(** Auxiliary randomness is the 32-byte value mixed into the nonce. *)
Definition AuxRand : Type := Array (Word 8) 32.

(** BIP-340 recommends fresh randomness to resist faults and side
    channels, and permits 32 zero bytes when none is available. The
    signing equation always receives one 32-byte value. *)

(* ================================================================= *)
(** ** 7.3 Hashing to a Scalar *)

(** SHA-256 returns 32 bytes, while group equations need a scalar.
    BIP-340 interprets the digest as a big-endian integer and reduces
    it modulo the group order. [hash_to_scalar] performs those steps
    after checking the tag and transcript length bounds: *)

Definition hash_to_scalar {t n : nat}
    (tag : Array (Word 8) t) (msg : Array (Word 8) n)
    (Htag : sha256_length_valid t)
    (Houter : sha256_length_valid (64 + n)) : Scalar :=
  scalar_of_bytes (tagged_hash tag msg Htag Houter).

(** Reduction is intentional here. Every digest must produce a
    scalar, so values above the group order wrap instead of causing a
    decoding failure. *)

(* ================================================================= *)
(** ** 7.4 Signatures *)

(** A Schnorr signature has two components. [sig_r] is the x
    coordinate of the nonce point [R]. [sig_s] is the response
    [k + e*d] reduced modulo the group order: *)

Record Signature : Type := mkSignature {
  sig_r : Fe;
  sig_s : Scalar
}.

(** A secret key already has type [Scalar]. An x-only public key is an
    [Fe] that can be lifted to a curve point with even y. [Signature]
    needs a record because it combines one value of each type. The
    expression [sig_r sig] selects field [sig_r] from record [sig]. A
    record expression such as [{| sig_r := r; sig_s := s |}] supplies
    both named fields. *)

(* ================================================================= *)
(** ** 7.5 The Challenge *)

(** The _challenge_ binds the signature to one public key and one
    message. It hashes the encoded nonce coordinate [r], the encoded
    public key coordinate [px], and the message, in that order. The
    result is reduced to a scalar [e]: *)

Program Definition challenge {n : nat}
    (r px : Fe) (m : Array (Word 8) n)
    (Hm : message_length_valid n) : Scalar :=
  hash_to_scalar tag_bip340_challenge (encode r ++ encode px ++ m) _ _.
(* begin hide *)
Next Obligation. vm_compute; reflexivity. Qed.
Next Obligation.
  unfold message_length_valid, sha256_length_valid in *.
  rewrite !Nat2Z.inj_add in *.
  lia.
Qed.
(* end hide *)

(* ================================================================= *)
(** ** 7.6 Nonce Derivation *)

(** Reusing one _nonce_ with different challenges exposes the secret
    key. From [s1 = k + e1*d] and [s2 = k + e2*d], an observer can
    eliminate [k] and solve for [d]. BIP-340 therefore derives [k]
    from the secret key, public key, message and auxiliary randomness.
    Repeated identical inputs may repeat the same nonce, and hash
    collisions remain theoretically possible. Security requires that
    one nonce is not used with distinct challenges.

    First hash the auxiliary randomness and xor that mask with the
    encoded secret scalar. Then hash the masked secret, public key and
    message under the nonce tag: *)

Program Definition nonce {n : nat}
    (d : Scalar) (px : Fe) (m : Array (Word 8) n) (aux : AuxRand)
    (Hm : message_length_valid n) : Scalar :=
  let mask := tagged_hash tag_bip340_aux aux _ _ in
  hash_to_scalar tag_bip340_nonce
    ((mask xor encode d) ++ encode px ++ m) _ _.
(* begin hide *)
Next Obligation. vm_compute; reflexivity. Qed.
Next Obligation. vm_compute; reflexivity. Qed.
Next Obligation. vm_compute; reflexivity. Qed.
Next Obligation.
  unfold message_length_valid, sha256_length_valid in *.
  rewrite !Nat2Z.inj_add in *.
  lia.
Qed.
(* end hide *)

(** The [xor] operation is bytewise and both operands have length 32.
    Parentheses keep that masked value together before concatenation. *)

(* ================================================================= *)
(** ** 7.7 Key Generation *)

(** Key generation computes [P = d * G]. Only [x(P)] is published.
    BIP-340 requires the implicit point behind that coordinate to have
    even y. If [P] has odd y, replacing [d] with [-d] replaces [P]
    with [-P], which keeps x and flips the parity of y: *)

Definition keygen (d : Scalar) : option (Scalar * Fe) :=
  match d * G with
  | PInf => None
  | PAff x y _ =>
      match fe_is_odd y with
      | true => Some (- d, x)
      | false => Some (d, x)
      end
  end.

(** [None] rejects any key whose multiple of [G] is [PInf], including
    the zero secret key. The generator has order [n], so a nonzero
    secret scalar below [n] selects an affine point. *)

(* ================================================================= *)
(** ** 7.8 Signing *)

(** Signing follows five steps:

    - Normalize the secret key to [d'] and its even-y public point.
    - Derive the nonce candidate [k0] from all signer inputs.
    - Compute [R = k0 * G], rejecting the identity.
    - Negate [k0] when [R] has odd y, so the adjusted [k] selects the
      even-y point with the same x coordinate.
    - Compute [e] and return [(x(R), k + e*d')]. *)

Definition sign {n : nat}
    (d : Scalar) (m : Array (Word 8) n) (aux : AuxRand)
    (Hm : message_length_valid n) : option Signature :=
  let* (d', px) := keygen d in
  let k0 := nonce d' px m aux Hm in
  match k0 * G with
  | PInf => None
  | PAff rx ry _ =>
      let k := if fe_is_odd ry then - k0 else k0 in
      let e := challenge rx px m Hm in
      Some {| sig_r := rx; sig_s := k + e * d' |}
  end.

(** [let*] propagates failure from [keygen]. The second [None] handles
    a zero derived nonce. The generator order ensures that a nonzero
    nonce selects an affine point. *)

(* ================================================================= *)
(** ** 7.9 Verification *)

(** Verification follows four steps:

    - Lift [px] to its unique even-y point [P], rejecting an invalid x
      coordinate.
    - Recompute the challenge [e].
    - Reconstruct the nonce point as [R = s * G - e * P].
    - Accept only when [R] is affine, has even y, and has x coordinate
      [sig_r sig]. *)

Definition verify {n : nat}
    (px : Fe) (m : Array (Word 8) n) (sig : Signature)
    (Hm : message_length_valid n) : bool :=
  match lift_x_even px with
  | None => false
  | Some P =>
      let e := challenge (sig_r sig) px m Hm in
      match sig_s sig * G - e * P with
      | PInf => false
      | PAff rx ry _ => negb (fe_is_odd ry) && (rx =? sig_r sig)
      end
  end.

(** For an honest signature, substitution explains the check:
    [s * G - e * P = (k + e*d') * G - e * (d' * G) = k * G].
    The scalar action laws justify these rearrangements. Parity
    normalization ensures that the signer and verifier select the
    same nonce point.

    The recovered point must be affine, have even y, and have x
    coordinate [sig_r sig]. *)

(* ================================================================= *)
(** ** 7.10 Encodings *)

(** The wire format concatenates the 32-byte encoding of [r] with the
    32-byte encoding of [s]. Encoding is total because both values
    already carry their bounds: *)

Definition Signature_encode : Encode Signature 64 := {|
  encode sig := array_app (encode (sig_r sig)) (encode (sig_s sig))
|}.
(* begin hide *)
#[export] Existing Instance Signature_encode.
(* end hide *)

Definition Signature_decode : Decode Signature 64 := {|
  decode sig64 :=
    let '(r32, s32) := array_split 32 32 sig64 in
    let* r := decode r32 in
    let* s := decode s32 in
    Some {| sig_r := r; sig_s := s |}
|}.
(* begin hide *)
#[export] Existing Instance Signature_decode.
(* end hide *)

(** Decoding first splits the input at the fixed boundary. The field
    decoder rejects [r] values at or above the coordinate modulus.
    The scalar decoder rejects [s] values at or above the group order.
    These are the range checks required by BIP-340 before group
    arithmetic.

    Decoding an x-only public key adds one geometric check to field
    decoding: *)

Definition xonly_decode (input32 : Array (Word 8) 32) : option Fe :=
  let* x := decode input32 in
  let* _ := lift_x_even x in
  Some x.

(** First, [decode] checks that the bytes denote a field element.
    Second, [lift_x_even] checks that the coordinate belongs to some
    curve point. The recovered point is discarded because the public
    representation retains only x.

    A secret key uses the scalar decoder directly. [keygen] then
    rejects zero. Custom nonce functions belong to the surrounding API
    and are outside this fixed BIP-340 nonce construction. *)

(* begin hide *)
End schnorr.
(* end hide *)


(* begin hide *)
Module correct.
Import Math.roots.
Import Math.group.
Import Math.scalar.
Import Math.order.
Import Math.law.
Import Math.schnorr.
Import Math.bytes.

(** A successfully produced Schnorr signature verifies against its public key. *)


Local Open Scope math_scope.
#[local] Existing Instance group.Point_zero.
#[local] Existing Instance group.Point_add.
#[local] Existing Instance group.Point_neg.
#[local] Existing Instance group.point_group.
#[local] Existing Instance group.Point_smul_scalar.

Lemma scalar_generator_add (a b : Scalar) :
  (a + b) * G = a * G + b * G.
Proof.
  exact (scalar_to_point_hom a b).
Qed.

Lemma scalar_generator_mul (a b : Scalar) :
  (a * b) * G = a * (b * G).
Proof.
  apply point_eq_ext.
  change (point_coordinates (group.smul' (scalar_val (scalar_mul a b)) group.G) =
    point_coordinates (group.smul' (scalar_val a)
      (group.smul' (scalar_val b) group.G))).
  rewrite !point_coordinates_smul.
  change (raw.smul ((scalar_val a * scalar_val b) mod secp256k1_N) raw.G =
    raw.smul (scalar_val a) (raw.smul (scalar_val b) raw.G)).
  rewrite smul_G_mod.
  apply law.smul_mul.
  exact raw.on_curve_G.
Qed.

Lemma scalar_generator_negate (a : Scalar) :
  (- a) * G = pneg (a * G).
Proof.
  pose proof (scalar_generator_add (- a) a) as Hsum.
  rewrite group_add_inverse in Hsum.
  change (PInf = padd ((- a) * G) (a * G)) in Hsum.
  apply (f_equal (fun p => padd p (pneg (a * G)))) in Hsum.
  rewrite group.padd_PInf_l, group.padd_assoc,
    (group.padd_comm (a * G) (pneg (a * G))),
    group.padd_pneg_l, group.padd_PInf_r in Hsum.
  symmetry. exact Hsum.
Qed.

Lemma keygen_lift (d normalized : Scalar) (x : Fe) :
  keygen d = Some (normalized, x) ->
  lift_x_even x = Some (normalized * G).
Proof.
  unfold keygen.
  destruct (d * G) as [|px py valid] eqn:Hpoint.
  - discriminate.
  - destruct (fe_is_odd py) eqn:Hodd.
    + intro Hkey. injection Hkey as <- <-.
      rewrite scalar_generator_negate, Hpoint.
      replace (pneg (PAff px py valid)) with
        (PAff px (- py) (negated_root_valid px py valid)).
      * apply lift_x_even_complete. apply fe_negate_odd_is_even. exact Hodd.
      * apply point_eq_ext. rewrite point_coordinates_neg. reflexivity.
    + intro Hkey. injection Hkey as <- <-.
      rewrite Hpoint. apply lift_x_even_complete. exact Hodd.
Qed.

Lemma schnorr_equation (k e d : Scalar) :
  (k + e * d) * G - e * (d * G) = k * G.
Proof.
  rewrite scalar_generator_add, scalar_generator_mul.
  change (padd (padd (k * G) (e * (d * G))) (pneg (e * (d * G))) = k * G).
  rewrite group.padd_assoc,
    (group.padd_comm (e * (d * G)) (pneg (e * (d * G)))),
    group.padd_pneg_l, group.padd_PInf_r.
  reflexivity.
Qed.

Local Opaque nonce challenge.

(* end hide *)

(** ** 7.11 Successful Signatures Verify *)

(** Scalar addition and multiplication give the verification equation.
    The root lemmas recover the even public point. Together these facts
    prove that every successful signing result verifies for the public
    key returned by key generation. *)

Lemma schnorr_verify_sign (n : nat) (d normalized : Scalar) (px : Fe)
    (m : Array (Word 8) n) (aux : AuxRand) (sig : Signature)
    (Hm : message_length_valid n) :
  keygen d = Some (normalized, px) ->
  sign d m aux Hm = Some sig ->
  verify px m sig Hm = true.
Proof.
  intros Hkey Hsign.
  unfold sign in Hsign.
  rewrite Hkey in Hsign.
  cbn [option_bind] in Hsign.
  remember (nonce normalized px m aux Hm) as k eqn:Hnonce.
  destruct (k * G) as [|rx ry valid] eqn:Hnonce_point.
  - discriminate.
  - injection Hsign as <-.
    unfold verify.
    rewrite (keygen_lift d normalized px Hkey).
    cbn [sig_r sig_s].
    rewrite schnorr_equation.
    destruct (fe_is_odd ry) eqn:Hodd.
    + rewrite scalar_generator_negate, Hnonce_point.
      change (negb (fe_is_odd (- ry)) && (rx =? rx) = true).
      rewrite fe_negate_odd_is_even by exact Hodd.
      change (Z.eqb (fe_val rx) (fe_val rx) = true).
      apply Z.eqb_refl.
    + rewrite Hnonce_point.
      change (negb (fe_is_odd ry) && (rx =? rx) = true).
      rewrite Hodd.
      change (Z.eqb (fe_val rx) (fe_val rx) = true).
      apply Z.eqb_refl.
Qed.

(* begin hide *)
End correct.
(* end hide *)


(* begin hide *)
Module generator_context.
Import Math.scalar Math.raw Math.residues.
Open Scope Z_scope.
Local Obligation Tactic := intros.
Definition comb_spacing_of (range blocks teeth : Z) : Z :=
  1 + (range - 1) / (blocks * teeth).

Definition comb_bits_of (blocks teeth spacing : Z) : Z := blocks * teeth * spacing.

Definition comb_range : Z := 256.

Definition comb_blocks : Z := 11.

Definition comb_teeth : Z := 6.

Definition comb_spacing : Z := comb_spacing_of comb_range comb_blocks comb_teeth.

Definition comb_bits : Z := comb_bits_of comb_blocks comb_teeth comb_spacing.

Program Definition ecmult_gen_scalar_diff : Scalar :=
  mkScalar (((2 ^ comb_bits - 1) * ((secp256k1_N + 1) / 2)) mod secp256k1_N) _.
Next Obligation.
  apply Z.mod_pos_bound.
  pose proof secp256k1_N_range.
  lia.
Qed.

Record GenBlind := mkGenBlind {
  gb_scalar_offset : Scalar;
  gb_ge_offset : Point
}.

Definition gb_wf (gb : GenBlind) : Prop :=
  gb_ge_offset gb <> PInf /\
  exists b : Z,
    scalar_val (gb_scalar_offset gb)
      = (scalar_val ecmult_gen_scalar_diff - b) mod secp256k1_N /\
    gb_ge_offset gb = smul b G.
End generator_context.
End Math.
Export Math.algebra Math.bytes Math.field Math.scalar Math.group Math.sha256 Math.schnorr.
(* end hide *)


(* begin hide *)
Module api.
Import CProofFramework.
Import Math.
Import Math.algebra.
Import Math.bytes.
Import Math.field.
Import Math.generator_context.
Import Math.scalar.
Import Math.sha256.
Import Math.group.
Import Math.schnorr.
(* end hide *)
(* begin hide *)
(** * The Schnorr C interface *)
(** Copyright (C) 2026 remix7531
    SPDX-License-Identifier: MIT *)

(** These contracts connect mathematical values to the bytes owned by a
    caller. A valid keypair stores the original secret, before the parity
    adjustment used by signing. Public key objects contain native storage
    words. Their serialized form instead uses big-endian coordinates. *)


Open Scope Z_scope.

#[local] Instance ApiCompSpecs : compspecs.
Proof. make_compspecs extraction.prog. Defined.

Definition t_api_context := Tstruct _secp256k1_context_struct noattr.
Definition t_api_keypair := Tstruct _secp256k1_keypair noattr.
Definition t_api_xonly := Tstruct _secp256k1_xonly_pubkey noattr.

Lemma api_object_sizes :
  sizeof t_api_keypair = 96 /\ sizeof t_api_xonly = 64.
Proof. split; reflexivity. Qed.


(* end hide *)
(* Copyright (C) 2026 remix7531. SPDX-License-Identifier: MIT *)
(** * 8. From Mathematics to C *)

(** The definitions now describe the bytes accepted by Schnorr and the
    signatures it produces. This chapter connects those definitions to
    C functions that read and write memory. A proof of a contract shows
    that every call satisfying its precondition computes the stated
    result and has defined behavior under CompCert C semantics. The
    contract covers memory access, alignment, object bounds, and the
    other conditions needed to rule out undefined behavior.

    The signing contract names [sign]. The verification contract decodes
    its input and names [verify]. Proving the contracts therefore
    connects the C functions directly to the definitions in the
    preceding chapters. *)

(* begin hide *)
#[local] Existing Instance ApiCompSpecs.
(* end hide *)

(* ================================================================= *)
(** ** 8.1 Reading a C Contract *)

(** A Hoare triple has a precondition, a command, and a postcondition.
    The precondition states what a caller must provide. The
    postcondition states what the command returns and what remains true.
    See
    {{https://softwarefoundations.cis.upenn.edu/plf-current/Hoare.html}
    Hoare Logic} for a short introduction.

    Separation logic adds precise ownership of memory. Its separating
    conjunction requires assertions to describe disjoint resources. This
    lets a contract state which buffers a function may read or write
    without claiming unrelated memory. See
    {{https://softwarefoundations.cis.upenn.edu/slf-current/Hprop.html}
    Separation Logic Foundations} for the underlying rules.

    VST, the Verified Software Toolchain, expresses these contracts in
    Rocq. Its model of C uses CompCert semantics. A VST [funspec] has
    these parts:

    - [WITH] introduces logical values used to describe one call. They
      are not extra C arguments.
    - [PRE] gives the C argument types. [PARAMS] gives the argument
      values.
    - [PROP] states ordinary facts, including read and write
      permissions.
    - [SEP] states ownership and contents of separate memory regions.
    - [POST] gives the return type. [RETURN] and the final [SEP] state
      the result and memory after the call.

    The assertion [data_at sh t value p] says that address [p] contains
    [value] with C type [t] and permission [sh]. A readable share
    permits reads. A writable share permits writes. [data_at_] requires
    valid, correctly sized, and aligned storage without fixing its
    initial value. These assertions describe memory. They do not
    allocate it. *)

(** *** 8.1.1 Byte Arrays *)

(** [bytes_to_vals] maps mathematical bytes to CompCert integer values.
    [byte_array_at] states that an [Array (Word 8) n] occupies an
    array of unsigned C characters at a given address. [zero_vals]
    describes cleared output storage. *)

Definition bytes_to_vals {n : nat} (a : Array (Word 8) n) : list val :=
  map (fun b => Vint (Int.repr (word_val b))) (array_list a).

Definition byte_array_at {n : nat} (sh : share) (a : Array (Word 8) n)
    (p : val) : mpred :=
  data_at sh (tarray tuchar (Z.of_nat n)) (bytes_to_vals a) p.

Definition zero_vals (n : nat) : list val :=
  repeat (Vint Int.zero) n.

(** *** 8.1.2 Native Key Objects *)

(** External encodings and native objects have different layouts. An
    encoded scalar or coordinate uses big-endian bytes. A C key object
    stores each coordinate as four native 64-bit words.
    [point_storage_vals] describes that native layout.

    [keypair_at] relates a keypair object to a nonzero scalar [d] and
    the point [d * G]. [xonly_pubkey_at] relates a public key object to
    the even point recovered from its x coordinate. The conditions
    before [&&] are mathematical facts. The [data_at] condition after
    it owns the C object. [EX] introduces coordinates that witness both
    parts. *)

(* begin hide *)


(** Storage uses four native 64-bit words for each coordinate. The
    target endianness comes from CompCert, including the byte order
    within each word copied by the C implementation. *)
Definition coordinate_storage_vals (x : Fe) : list val :=
  flat_map (fun limb =>
    let octets := map (fun j =>
      Vint (Int.repr ((fe_val x / 2 ^ (64 * Z.of_nat limb)
                        / 2 ^ (8 * Z.of_nat j)) mod 256))) (seq 0 8) in
    if Archi.big_endian then rev octets else octets) (seq 0 4).

Definition point_storage_vals (x y : Fe) : list val :=
  coordinate_storage_vals x ++ coordinate_storage_vals y.


(* end hide *)

Definition has_affine_coordinates (p : Point) (x y : Fe) : Prop :=
  affine_coordinates p = Some (x, y).

Definition xonly_pubkey_at (sh : share) (x : Fe) (p : val) : mpred :=
  EX y : Fe,
    !! (has_affine_coordinates (match lift_x_even x with
                   | Some q => q | None => PInf end) x y /\
        fe_val x <> 0) &&
    data_at sh t_api_xonly (point_storage_vals x y) p.

Definition keypair_at (sh : share) (d : Scalar) (p : val) : mpred :=
  EX x : Fe, EX y : Fe,
    !! (scalar_val d <> 0 /\ has_affine_coordinates (d * G)%M x y /\
        fe_val x <> 0) &&
    data_at sh t_api_keypair
      (bytes_to_vals (encode d) ++ point_storage_vals x y) p.

(** The distinction matters at interface boundaries. Serialization
    writes the big-endian encoding of [x]. It does not copy the native
    coordinate words from an x-only public key object.

    [context_at] owns the complete context layout and its callback
    pointers. When [built = true], it also requires valid generator
    blinding data and a nonzero projective scale. Keypair creation and
    signing require this case. Other calls accept either value of
    [built]. The compression callback must satisfy the SHA256 transition
    contract.

    [api_global_resources gv] owns initialized global tables, constants,
    and function pointers. The static context object is excluded because
    [context_at] owns it separately. This prevents the two predicates
    from claiming the same memory. The
    {{specification.v}complete source}
    contains the context and callback definitions. *)

(* ================================================================= *)
(* begin hide *)


Definition api_words (xs : list Z) : list val :=
  map (fun x => Vlong (Int64.repr x)) xs.

Definition api_limbs_value (width : Z) (xs : list Z) : Z :=
  fold_right (fun limb tail => limb + 2 ^ width * tail) 0 xs.

Definition api_field_limbs (magnitude : Z) (xs : list Z) (x : Fe) : Prop :=
  length xs = 5%nat /\
  (forall i, (i < 5)%nat ->
    0 <= nth i xs 0 <=
      2 * magnitude * (2 ^ (if Nat.eqb i 4 then 48 else 52) - 1)) /\
  api_limbs_value 52 xs mod secp256k1_P = fe_val x.

Definition api_scalar_limbs (xs : list Z) (d : Scalar) : Prop :=
  length xs = 4%nat /\
  Forall (fun limb => 0 <= limb < 2 ^ 64) xs /\
  api_limbs_value 64 xs = scalar_val d.

(** Global resources are the actual initialized objects of the
    implementation, including precomputed curve tables, hash constants
    and function-pointer constants. Passing this concrete list also
    accounts for static data read by the compression callback. *)
Section Api.
Variable api_global_definitions :
  list (ident * AST.globdef (Ctypes.fundef Clight.function) type).

(** The static context object is owned separately by [context_at].
    Excluding it here permits callers to use the library static context
    without demanding two disjoint copies of the same memory. *)
Definition api_static_context_storage : ident :=
  ltac:(let id := eval compute in
    (ident_of_string "secp256k1_context_static_") in exact id).

Definition api_global_resources (gv : globals) : mpred :=
  InitGPred
    (filter (fun entry => negb (Pos.eqb (fst entry)
      api_static_context_storage)) api_global_definitions) gv.

(** Compression callbacks must implement the same SHA256 transition
    used by Schnorr. Owning a function pointer alone would say nothing
    about the hash computed through that pointer. *)
Definition api_compression_spec : funspec :=
  WITH gv : globals, state_ptr : val, input_ptr : val, state : Sha256_state,
       blocks : { count : nat & Array Sha256_block count },
       state_share : share, input_share : share
  PRE [ tptr tuint, tptr tuchar, tulong ]
    PROP (writable_share state_share;
          readable_share input_share;
          0 < Z.of_nat (projT1 blocks) <= Ptrofs.max_unsigned / 64)
    PARAMS (state_ptr; input_ptr;
            Vlong (Int64.repr (Z.of_nat (projT1 blocks))))
    GLOBALS (gv)
    SEP (api_global_resources gv;
         data_at state_share (tarray tuint 8)
          (map (fun w => Vint (Int.repr (word_val w)))
            (array_list (sha256_state_words state))) state_ptr;
         data_at input_share (tarray tuchar (64 * Z.of_nat (projT1 blocks)))
          (flat_map bytes_to_vals (array_list (projT2 blocks))) input_ptr)
  POST [ tvoid ]
    PROP () RETURN ()
    SEP (api_global_resources gv;
         data_at state_share (tarray tuint 8)
          (map (fun w => Vint (Int.repr (word_val w)))
            (array_list (sha256_state_words
              (sha256_transform state (projT2 blocks))))) state_ptr;
         data_at input_share (tarray tuchar (64 * Z.of_nat (projT1 blocks)))
          (flat_map bytes_to_vals (array_list (projT2 blocks))) input_ptr).

(** The full context layout is generated from C. A built context carries
    the generator blinding invariant and a nonzero projective scale.
    Verification also accepts an unbuilt context. Callback fields remain
    owned, but valid API arguments do not invoke the illegal callback. *)
Definition context_at (sh : share) (built : bool) (p : val) : mpred :=
  EX scalar_offset : Scalar, EX offset_x : Fe, EX offset_y : Fe,
  EX projective_blind : Fe, EX scalar_words : list Z,
  EX x_words : list Z, EX y_words : list Z, EX blind_words : list Z,
  EX offset : Point, EX hash_fn : val,
  EX illegal_fn : val, EX illegal_data : val,
  EX error_fn : val, EX error_data : val,
  !! (built = true ->
      api_scalar_limbs scalar_words scalar_offset /\
      api_field_limbs 4 x_words offset_x /\
      api_field_limbs 3 y_words offset_y /\
      api_field_limbs 1 blind_words projective_blind /\
      has_affine_coordinates offset offset_x offset_y /\
      fe_val projective_blind <> 0 /\
      gb_wf (mkGenBlind scalar_offset (point_coordinates offset))) &&
  (data_at sh t_api_context
    ((Vint (if built then Int.one else Int.zero),
      (api_words scalar_words,
       ((api_words x_words, (api_words y_words, Vint Int.zero)),
        api_words blind_words))),
     (hash_fn, ((illegal_fn, illegal_data),
       ((error_fn, error_data), Vint Int.zero)))) p *
   func_ptr' api_compression_spec hash_fn).


(* end hide *)

(** ** 8.2 Contracts for the Public Interface *)

(** The six contracts below use the same pattern. [PRE] connects C
    pointers to mathematical inputs. [POST] fixes the return value and
    output memory, then returns ownership of inputs, the context, and
    global resources. The signatures come from the
    {{https://github.com/bitcoin-core/secp256k1/blob/v0.8.0/include/secp256k1_extrakeys.h}
    extra keys header} and the
    {{https://github.com/bitcoin-core/secp256k1/blob/v0.8.0/include/secp256k1_schnorrsig.h}
    Schnorr header}. *)

(** *** 8.2.1 Creating a Keypair *)

(** [api_secret] decodes the 32 input bytes as a canonical scalar and
    rejects zero. [return_status] maps success to the C integer one and
    rejection to zero. *)

Definition api_secret (input : Array (Word 8) 32) : option Scalar :=
  match decode input with
  | None => None
  | Some d => if Z.eqb (scalar_val d) 0 then None else Some d
  end.

Definition return_status {A : Type} (r : option A) : val :=
  Vint (match r with Some _ => Int.one | None => Int.zero end).

(** The postcondition binds [result] once. [RETURN] uses it for the
    status. The matching [SEP] branch either establishes [keypair_at]
    for the decoded scalar or requires a cleared 96-byte object. The
    input bytes, context, globals, and their permissions return in both
    cases. *)

Definition spec_secp256k1_keypair_create : ident * funspec :=
  DECLARE _secp256k1_keypair_create
  (* The logical secret is related to the C input pointer by byte_array_at. *)
  WITH gv : globals, ctx : val, output : val, input : val, secret : Array (Word 8) 32,
       ctx_share : share, output_share : share, input_share : share
  PRE [ tptr t_api_context, tptr t_api_keypair, tptr tuchar ]
    PROP (readable_share ctx_share;
          writable_share output_share;
          readable_share input_share)
    PARAMS (ctx; output; input)
    GLOBALS (gv)
    (* The output owns writable storage with no required initial value. *)
    SEP (api_global_resources gv;
         context_at ctx_share true ctx;
         data_at_ output_share t_api_keypair output;
         byte_array_at input_share secret input)
  POST [ tint ]
    let result := api_secret secret in
    PROP () RETURN (return_status result)
    SEP (api_global_resources gv;
         context_at ctx_share true ctx;
         match result with
         | Some d => keypair_at output_share d output
         | None => data_at output_share t_api_keypair (zero_vals 96) output
         end;
         byte_array_at input_share secret input).

(** An invalid secret is an ordinary rejection because the
    precondition accepts every 32-byte array. An invalid pointer, short
    allocation, or unbuilt context violates the precondition, so the
    contract makes no promise for such a call. *)

(** *** 8.2.2 Obtaining an X-Only Public Key *)

(** The input is a valid keypair. The parity output may be null.
    [optional_int_at] owns an integer cell only when its pointer is
    nonnull. [None] leaves the initial integer unspecified. [Some v]
    fixes its final value. *)

Definition optional_int_at (sh : share) (p : val) (value : option val)
    : mpred :=
  if eq_dec p nullval then emp else
    match value with
    | None => data_at_ sh tint p
    | Some v => data_at sh tint v p
    end.

(** The logical coordinates [x] and [y] identify [d * G]. The output
    stores its even-y representative. The optional integer reports
    whether the original [y] was odd. The input keypair remains
    unchanged. *)

Definition spec_secp256k1_keypair_xonly_pub : ident * funspec :=
  DECLARE _secp256k1_keypair_xonly_pub
  WITH gv : globals, ctx : val, output : val, parity : val, input : val,
       d : Scalar, x : Fe, y : Fe, built : bool,
       ctx_share : share, output_share : share, parity_share : share,
       input_share : share
  PRE [ tptr t_api_context, tptr t_api_xonly, tptr tint, tptr t_api_keypair ]
    PROP (readable_share ctx_share;
          writable_share output_share;
          writable_share parity_share;
          readable_share input_share;
          has_affine_coordinates (d * G)%M x y)
    PARAMS (ctx; output; parity; input)
    GLOBALS (gv)
    SEP (api_global_resources gv;
         context_at ctx_share built ctx;
         data_at_ output_share t_api_xonly output;
         optional_int_at parity_share parity None;
         keypair_at input_share d input)
  POST [ tint ]
    PROP () RETURN (Vint Int.one)
    SEP (api_global_resources gv;
         context_at ctx_share built ctx;
         xonly_pubkey_at output_share x output;
         (* Report the original point parity before choosing even y. *)
         optional_int_at parity_share parity
           (Some (Vint (if fe_is_odd y then Int.one else Int.zero)));
         keypair_at input_share d input).

(** *** 8.2.3 Parsing a Public Key *)

(** Parsing accepts arbitrary 32-byte input. [xonly_decode] rejects a
    noncanonical field encoding or an x coordinate that has no curve
    point. The postcondition binds this result once. Success creates an
    [xonly_pubkey_at] object. Failure clears all 64 output bytes. Both
    the return status and output branch use the same result. *)

Definition spec_secp256k1_xonly_pubkey_parse : ident * funspec :=
  DECLARE _secp256k1_xonly_pubkey_parse
  WITH gv : globals, ctx : val, output : val, input : val, encoded : Array (Word 8) 32,
       built : bool, ctx_share : share, output_share : share, input_share : share
  PRE [ tptr t_api_context, tptr t_api_xonly, tptr tuchar ]
    PROP (readable_share ctx_share;
          writable_share output_share;
          readable_share input_share)
    PARAMS (ctx; output; input)
    GLOBALS (gv)
    SEP (api_global_resources gv;
         context_at ctx_share built ctx;
         data_at_ output_share t_api_xonly output;
         byte_array_at input_share encoded input)
  POST [ tint ]
    let result := xonly_decode encoded in
    PROP () RETURN (return_status result)
    SEP (api_global_resources gv;
         context_at ctx_share built ctx;
         match result with
         | Some x => xonly_pubkey_at output_share x output
         | None => data_at output_share t_api_xonly (zero_vals 64) output
         end;
         byte_array_at input_share encoded input).

(** *** 8.2.4 Serializing a Public Key *)

(** Serialization requires a valid [xonly_pubkey_at] object. It writes
    the unique 32-byte big-endian encoding of [x]. This contract always
    returns one because invalid object bytes cannot satisfy its
    precondition. Parsing checks untrusted bytes. *)

Definition spec_secp256k1_xonly_pubkey_serialize : ident * funspec :=
  DECLARE _secp256k1_xonly_pubkey_serialize
  WITH gv : globals, ctx : val, output : val, input : val, x : Fe,
       built : bool, ctx_share : share, output_share : share, input_share : share
  PRE [ tptr t_api_context, tptr tuchar, tptr t_api_xonly ]
    PROP (readable_share ctx_share;
          writable_share output_share;
          readable_share input_share)
    PARAMS (ctx; output; input)
    GLOBALS (gv)
    SEP (api_global_resources gv;
         context_at ctx_share built ctx;
         data_at_ output_share (tarray tuchar 32) output;
         xonly_pubkey_at input_share x input)
  POST [ tint ]
    (* The valid object required by PRE makes serialization succeed. *)
    PROP () RETURN (Vint Int.one)
    SEP (api_global_resources gv;
         context_at ctx_share built ctx;
         byte_array_at output_share (encode x) output;
         xonly_pubkey_at input_share x input).

(** *** 8.2.5 Signing a Message *)

(** Signing uses a valid keypair, a 32-byte message, and auxiliary
    randomness. A null auxiliary pointer selects 32 zero bytes.
    [api_message32_valid] is proof that this fixed message length
    satisfies the transcript bound. It is an argument to [sign], with
    no corresponding C argument. *)

Definition api_message32_valid : message_length_valid 32.
Proof. vm_compute. reflexivity. Qed.

Definition aux_rand_at (sh : share) (p : val) (aux : AuxRand) : mpred :=
  if eq_dec p nullval then !! (bytes_to_vals aux = zero_vals 32)
  else byte_array_at sh aux p.

(** The postcondition binds the result of [sign] once. [RETURN] maps it
    to zero or one. The output [data_at] stores [encode signature] after
    success and 64 zero bytes after failure. Message, keypair, auxiliary
    input, context, and global predicates return unchanged.

    This contract selects standard BIP340 nonce construction. It does
    not specify custom nonce callbacks, variable-length signing, final
    self-verification, or physical fault detection. *)

Definition spec_secp256k1_schnorrsig_sign32 : ident * funspec :=
  DECLARE _secp256k1_schnorrsig_sign32
  WITH gv : globals, ctx : val, output : val, message : val, keypair : val, aux_ptr : val,
       d : Scalar, msg : Array (Word 8) 32, aux : AuxRand,
       ctx_share : share, output_share : share, message_share : share,
       keypair_share : share, aux_share : share
  PRE [ tptr t_api_context, tptr tuchar, tptr tuchar,
        tptr t_api_keypair, tptr tuchar ]
    PROP (readable_share ctx_share;
          writable_share output_share;
          readable_share message_share;
          readable_share keypair_share;
          readable_share aux_share)
    PARAMS (ctx; output; message; keypair; aux_ptr)
    GLOBALS (gv)
    SEP (api_global_resources gv;
         (* Signing needs the generator blinding invariant. *)
         context_at ctx_share true ctx;
         data_at_ output_share (tarray tuchar 64) output;
         byte_array_at message_share msg message;
         keypair_at keypair_share d keypair;
         aux_rand_at aux_share aux_ptr aux)
  POST [ tint ]
    let result := sign d msg aux api_message32_valid in
    PROP () RETURN (return_status result)
    SEP (api_global_resources gv;
         context_at ctx_share true ctx;
         data_at output_share (tarray tuchar 64)
           (match result with
            | Some signature => bytes_to_vals (encode signature)
            | None => zero_vals 64
            end) output;
         byte_array_at message_share msg message;
         keypair_at keypair_share d keypair;
         aux_rand_at aux_share aux_ptr aux).

(** *** 8.2.6 Verifying a Signature *)

(** [api_verify] decodes the 64 signature bytes, then calls [verify]. A
    malformed encoding returns false before the curve equation is
    checked.

    Verification accepts any message length within the transcript bound.
    [api_message_input] is a dependent record. Its byte array length is
    the value in [api_message_length], and [api_message_valid] proves
    that same length satisfies the bound. [message_at] permits a null
    message pointer only when that length is zero. *)

Definition api_verify {n : nat} (x : Fe) (msg : Array (Word 8) n)
    (signature : Array (Word 8) 64) (valid : message_length_valid n) : bool :=
  match decode signature with
  | None => false
  | Some s => verify x msg s valid
  end.

Definition message_at {n : nat} (sh : share) (msg : Array (Word 8) n)
    (p : val) : mpred :=
  if eq_dec p nullval then !! (n = 0%nat) else byte_array_at sh msg p.

Record api_message_input := {
  api_message_length : nat;
  api_message_bytes : Array (Word 8) api_message_length;
  api_message_valid : message_length_valid api_message_length
}.

(** [PARAMS] converts the record length to the C size argument. The
    [PROP] bound ensures that it fits the target address range. [SEP]
    uses the bytes from the same record. The return value is one exactly
    when [api_verify] succeeds. Signature, message, public key, context,
    and global resources keep their contents and permissions. *)

Definition spec_secp256k1_schnorrsig_verify : ident * funspec :=
  DECLARE _secp256k1_schnorrsig_verify
  WITH gv : globals, ctx : val, signature_ptr : val, message_ptr : val, pubkey : val,
       message_input : api_message_input, signature : Array (Word 8) 64, x : Fe,
       built : bool,
       ctx_share : share, signature_share : share,
       message_share : share, pubkey_share : share
  PRE [ tptr t_api_context, tptr tuchar, tptr tuchar, tulong,
        tptr t_api_xonly ]
    PROP (readable_share ctx_share;
          readable_share signature_share;
          readable_share message_share;
          readable_share pubkey_share;
          Z.of_nat (api_message_length message_input) <= Ptrofs.max_unsigned)
    PARAMS (ctx; signature_ptr; message_ptr;
            Vlong (Int64.repr
              (Z.of_nat (api_message_length message_input))); pubkey)
    GLOBALS (gv)
    SEP (api_global_resources gv;
         context_at ctx_share built ctx;
         byte_array_at signature_share signature signature_ptr;
         message_at message_share (api_message_bytes message_input) message_ptr;
         xonly_pubkey_at pubkey_share x pubkey)
  POST [ tint ]
    PROP ()
    (* Decoding failure and mathematical rejection both return zero. *)
    RETURN (Vint
      (if api_verify x (api_message_bytes message_input) signature
          (api_message_valid message_input)
       then Int.one else Int.zero))
    SEP (api_global_resources gv;
         context_at ctx_share built ctx;
         byte_array_at signature_share signature signature_ptr;
         message_at message_share (api_message_bytes message_input) message_ptr;
         xonly_pubkey_at pubkey_share x pubkey).



(* ================================================================= *)
(** ** 8.3 The Verification Goal *)

(** [schnorr_contracts] is the complete exported contract list. Keeping
    one named list makes the six functions in the claim explicit. *)

Definition schnorr_contracts : funspecs := [
  spec_secp256k1_keypair_create;
  spec_secp256k1_keypair_xonly_pub;
  spec_secp256k1_xonly_pubkey_parse;
  spec_secp256k1_xonly_pubkey_serialize;
  spec_secp256k1_schnorrsig_sign32;
  spec_secp256k1_schnorrsig_verify
].

(* begin hide *)
End Api.
(* end hide *)

(* begin hide *)
Definition schnorr_program : QP.program Clight.function :=
  ltac:(QPprog extraction.prog).
(* end hide *)

(** A _Verified Software Unit_, or VSU, packages a Clight program with
    proofs of its contracts. [schnorr_program] is the library implementation
    extracted from C with the extrakeys and Schnorr modules enabled,
    including the production precomputed tables.
    [Vardefs schnorr_program] supplies its global definitions to the
    contracts and their initial memory predicate.

    [Espec] is the VST parameter for external interactions. The two [nil]
    arguments mean that this unit assumes no external or imported contract
    lists. The final function describes initialized global memory.

    [implements_schnorr] states the proof target for this program. Its
    proof must justify every internal function and establish the
    mathematical return values, memory conditions, and defined C behavior
    promised by [schnorr_contracts]. *)

Definition implements_schnorr {Espec : OracleKind} : Prop :=
  @VSU Espec nil nil schnorr_program
    (schnorr_contracts (Vardefs schnorr_program))
    (fun gv => InitGPred (Vardefs schnorr_program) gv).

(* ================================================================= *)
(** ** 8.4 Detecting Interface Drift *)

(** These two lemmas check the interface by computation. The first
    fixes the exported names and their order. The second compares every
    contract argument and return types with the extracted C function
    bodies. A changed name, pointer type, or argument order
    breaks these proofs.

    These checks do not prove function behavior. Behavior is the
    separate [VSU] obligation in [implements_schnorr]. *)

Lemma secp256k1_schnorr_exports definitions :
  map fst (schnorr_contracts definitions) =
    [_secp256k1_keypair_create; _secp256k1_keypair_xonly_pub;
     _secp256k1_xonly_pubkey_parse; _secp256k1_xonly_pubkey_serialize;
     _secp256k1_schnorrsig_sign32; _secp256k1_schnorrsig_verify].
Proof. reflexivity. Qed.

(* begin hide *)
Definition api_function_type (id : ident) : type :=
  match initial_world.find_id id extraction.global_definitions with
  | Some (AST.Gfun (Ctypes.Internal body)) => Clight.type_of_function body
  | _ => tvoid
  end.
(* end hide *)

Lemma secp256k1_schnorr_signatures definitions :
  map (fun '(id, specification) => (id, type_of_funspec specification))
      (schnorr_contracts definitions) =
  map (fun id => (id, api_function_type id))
      (map fst (schnorr_contracts definitions)).
Proof. reflexivity. Qed.

(* begin hide *)
End api.
(* end hide *)
