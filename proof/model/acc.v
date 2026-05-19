(** * model.acc: the 192-bit scalar-multiply accumulator. *)
(** Copyright (C) 2026 remix7531
    SPDX-License-Identifier: MIT *)

(** The 3-limb, 192-bit accumulator [Acc] that backs the scalar-multiply /
    reduction inner loop (the C [secp256k1_uint128]-based [muladd] chain).  It is
    an implementation detail of that reduction, not one of the fundamental
    machine-word types of [model.int128] -- hence its own file. *)

Require Import ZArith.
Require Import Lia.
Require Import secp256k1.model.int128.

Open Scope Z_scope.

(** Deterministic obligation preprocessing: just [intros].  The default
    [program_simpl] auto-solver spins on the [(N - a) mod N] obligation
    shapes now that floyd (which used to override it) is no longer loaded. *)
Local Obligation Tactic := intros.

(** A 192-bit accumulator (c0, c1, c2). *)
Record Acc := mkAcc {
  acc_val : Z;
  acc_range : 0 <= acc_val < 2^192
}.

(** Add a*b to the accumulator: acc' = acc + a*b. *)
Program Definition acc_muladd (acc : Acc) (a b : UInt64)
  (H : acc_val acc + u64_val a * u64_val b < 2^192) : Acc :=
  mkAcc (acc_val acc + u64_val a * u64_val b) _.
Next Obligation.
  destruct acc as [v [Hv0 Hv1]].
  destruct a as [av [Ha0 Ha1]], b as [bv [Hb0 Hb1]].
  simpl in *.
  lia.
Qed.

(** Low 64 bits of an [Acc] (extracted limb). *)
Program Definition acc_lo (acc : Acc) : UInt64 :=
  mkUInt64 (acc_val acc mod 2^64) _.
Next Obligation.
  apply Z.mod_pos_bound.
  lia.
Qed.

(** Right-shift the accumulator by 64 bits. *)
Program Definition acc_shift (acc : Acc) : Acc :=
  mkAcc (acc_val acc / 2^64) _.
Next Obligation.
  destruct acc as [v [Hv0 Hv1]].
  simpl.
  split.
  - apply Z.div_pos; lia.
  - apply Z.div_lt_upper_bound; lia.
Qed.
