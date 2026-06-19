(** * theory.modinv.divsteps.bound590: the 590-divstep convergence certificate for the constant-time (zeta) safegcd driver. *)
(** Copyright (C) 2026 remix7531
    SPDX-License-Identifier: MIT *)

Require Import ZArith.

Require Import secp256k1.theory.modinv.construction.divstep_zeta.

Open Scope Z_scope.

(* ================================================================= *)
(** ** 590-divstep convergence -- [example590]. *)

(** [example590] is the constant-time analogue of [example724]: 590 zeta-divsteps
   clear [g] for every 256-bit input, justifying the [for (i = 0; i < 10; ++i)]
   loop of 10 * 59 = 590 divsteps in the constant-time [secp256k1_modinv64] driver
   (after which [g = 0] and, when [x <> 0], [f = +/- gcd(m, x) = +/- 1], so [d]
   holds the inverse).  The zeta machine ([zstep] / [zstep_n]) runs the same H/S/D
   maps as the variable-time [step], differing only in the boundary test, so this
   is a SEPARATE convex-hull certificate from [example724].

   Kept an [Axiom] for the same scale reason as [example724] (see there), plus one
   specific to its shape: unlike [example724]'s ground term, [example590] is
   universally quantified over [m] and [x], so [vm_compute] cannot reduce it
   directly -- discharging it would first need a port of the constant-time (zeta)
   safegcd-bounds reflection, which this development does not carry. *)
Axiom example590 : forall m x (oddm : Zodd m),
  0 <= x < m ->
  m < 2^256 ->
  zg (fst (zstep_n 590 (zinit m x oddm))) = 0.
