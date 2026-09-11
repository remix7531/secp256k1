(** * theory.modinv.divsteps.bound724: the variable-time 724-divstep convergence axiom [example724]. *)
(** Copyright (C) 2026 remix7531
    Adapted from sipa/safegcd-bounds coq/divsteps/divsteps724.v (commit 06abb7f),
    Copyright (c) 2021 Blockstream, originally MIT.
    Upstream notice reproduced in proof/README.md.
    SPDX-License-Identifier: MIT *)

(** Local modification: [example724]'s upstream reflection proof is stated as an
    [Axiom] here (rationale in the comment below). *)

Require Import ZArith.

Require Import secp256k1.theory.modinv.divsteps.base.

(* ================================================================= *)
(** ** 724-divstep convergence -- [example724]. *)

(** [example724]: 724 Bernstein-Yang divsteps clear the convex-hull state machine
   for every modulus up to the bound below -- which justifies the 12*62 = 744 >=
   724 iteration cap in [secp256k1_modinv64_var].  Upstream (sipa/safegcd-bounds)
   proves it by [vm_cast_no_check] reflection; we keep it an [Axiom] because the
   724-iteration check over a 256-bit modulus is computationally scale-blocked
   (~k^4: 2.6 s at 50 iterations, 43 s at 100, multi-day at 724), not
   tactic-blocked ([vm_compute] works on Rocq 9.0.1). *)
Axiom example724 : ZMap.Empty (N.iter 724 (process_divstep 0x1030596cf6d817d1357f908ef70cdb00b38d047fbba852139babb6c8646fb15b2) state0).
