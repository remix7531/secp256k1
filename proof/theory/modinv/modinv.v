(** * theory.modinv.modinv: the modular-inverse specification (and the Jacobi symbol). *)
(** Copyright (C) 2026 remix7531
    SPDX-License-Identifier: MIT *)

(** [is_modular_inverse a m r] characterises the result of modular
    inversion. [jacobi_symbol] computes the Jacobi symbol used by
    [secp256k1_jacobi64_maybe_var]. *)

Require Import ZArith.
Require Import Coq.ZArith.Znumtheory.
Require Import Lia.

Open Scope Z_scope.

(* ================================================================= *)
(** ** Modular inverse -- [is_modular_inverse] (the spec). *)

(** [r] is reduced modulo [m], inverts [a] when [a] and [m] are coprime,
    and is zero when [a] is zero. For other noninvertible inputs, only the
    output range is constrained. *)
Definition is_modular_inverse (a m r : Z) : Prop :=
  0 <= r < m
  /\ (a = 0 -> r = 0)
  /\ (rel_prime a m -> (a * r) mod m = 1).

(* ================================================================= *)
(** ** Jacobi symbol -- [jacobi_symbol] (spec target for [jacobi64_maybe_var]). *)

(** The Jacobi symbol [(a | n)] for odd [n > 0], by the standard reduction:
    factor 2s out of [a] using the [(2|n)] supplement, then Euclid-style swap
    with quadratic reciprocity. Its mathematical properties are proved in
    [theory/modinv/jacobi_rules.v].
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
