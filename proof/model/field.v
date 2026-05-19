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
Require Export secp256k1.model.types.

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

