(** * model.modinv: the modular-inverse specification (and the Jacobi symbol). *)
(** Copyright (C) 2026 remix7531
    SPDX-License-Identifier: MIT *)

(** The trust-boundary spec of modular inversion: [is_modular_inverse a m r] says
    *what* the modular inverse is, with no reference to *how* it is computed -- a
    reviewer reads it as "[r] is the modular inverse of [a] modulo [m]".  The
    gcd / Bezout / safegcd construction that realizes it ([mod_inv]) is kept
    INDEPENDENT: there is no bridge lemma tying the two together, and the
    construction does not reuse this definition.

    This file also carries [jacobi_symbol], the spec target for
    [secp256k1_jacobi64_maybe_var]. *)

Require Import ZArith.
Require Import Coq.ZArith.Znumtheory.
Require Import Lia.

Open Scope Z_scope.

(* ================================================================= *)
(** ** Modular inverse -- [is_modular_inverse] (the spec). *)

(** [r] is the modular inverse of [a] modulo [m]: the reduced residue with
    [a*r = 1 (mod m)] when [a] is invertible (coprime to [m]), and [0]
    otherwise.  The three conjuncts are exactly what a caller relies on:
    - [0 <= r < m]     -- the result is a reduced residue;
    - [a = 0 -> r = 0]  -- zero has no inverse, so it maps to zero;
    - [rel_prime a m -> (a * r) mod m = 1] -- for invertible [a], [r] inverts it. *)
Definition is_modular_inverse (a m r : Z) : Prop :=
  0 <= r < m
  /\ (a = 0 -> r = 0)
  /\ (rel_prime a m -> (a * r) mod m = 1).

(* ================================================================= *)
(** ** Jacobi symbol -- [jacobi_symbol] (spec target for [jacobi64_maybe_var]). *)

(** The Jacobi symbol [(a | n)] for odd [n > 0], by the standard reduction:
    factor 2s out of [a] using the [(2|n)] supplement, then Euclid-style swap
    with quadratic reciprocity.  This is OUR own definition (not ported); it is
    purely the *specification target* for [secp256k1_jacobi64_maybe_var] -- no
    properties are proved about it, and its body proof is left [Admitted] (an
    explicit outstanding gap, deliberately NOT part of the audited trust base).
    [fuel] bounds the Euclid recursion; a generous [2*log2 n] always suffices. *)
Fixpoint jacobi_twos (fuel : nat) (a n s : Z) : Z * Z :=
  match fuel with
  | O => (a, s)
  | S f =>
      if Z.even a
      then jacobi_twos f (a / 2) n
             (if ((n mod 8 =? 3) || (n mod 8 =? 5))%bool then -s else s)
      else (a, s)
  end.

Fixpoint jacobi_loop (fuel : nat) (a n s : Z) : Z :=
  match fuel with
  | O => 0
  | S f =>
      if a =? 0 then (if n =? 1 then s else 0)
      else
        let '(a1, s1) := jacobi_twos fuel a n s in
        let s2 := if ((a1 mod 4 =? 3) && (n mod 4 =? 3))%bool then -s1 else s1 in
        jacobi_loop f (n mod a1) a1 s2
  end.

(** [jacobi_symbol a n]: for odd [n >= 1] and any [a], the Jacobi symbol
    [(a | n)] in [{-1, 0, 1}] ([0] exactly when [gcd(a,n) <> 1]). *)
Definition jacobi_symbol (a n : Z) : Z :=
  jacobi_loop (2 * S (Z.to_nat (Z.log2 (Z.abs n + 2)))) (a mod n) n 1.
