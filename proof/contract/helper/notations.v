(** * contract.helper.notations: spatial-predicate notation for the C
    representations (machine words + bytes -- FROZEN; each subsystem owns its
    further [_at] notations, e.g. [fe_at] in [contract.field]). *)
(** Copyright (C) 2026 remix7531
    SPDX-License-Identifier: MIT *)

(** Shorthand for the [data_at] resources used across the contract layer. Read
    [kind_at sh p x] as "buffer [p] (share [sh]) holds the [kind] value [x]",
    and [kind_at_ sh p] as "[p] holds uninitialised [kind] storage". These are
    plain [Notation] -- definitionally equal to the underlying [data_at] /
    [data_at_], so [forward], [forward_call], [cancel], and [entailer!] see
    straight through them and existing proofs are unaffected. A [data_at]
    (never [data_at_], which STYLE.md exempts as uninitialised storage) stays
    raw only where no shape here fits a single one-off site.

    Kept in their own file (re-exporting [repr], which supplies the [*_to_val]
    bridges these expand to) so the representation definitions and the surface
    notation stay separable. New representations get their bridge in [repr.v]
    and their [_at] notation here. *)

Require Import secp256k1.vst.base.
Require Import secp256k1.contract.helper.structs_int128.
Require Import secp256k1.contract.helper.structs_scalar.
Require Export secp256k1.contract.helper.repr.

(* ================================================================= *)
(** ** Unsigned-value notations -- [u64_at] / [u128_at] / [acc_at] / [u256_at] / [scalar_at] / [u512_at]. *)

Notation "'u64_at' sh p x" :=
  (data_at sh tulong (uint64_to_val x) p)
  (at level 20, sh at level 0, p at level 0, x at level 0).
Notation "'u64_at_' sh p" :=
  (data_at_ sh tulong p)
  (at level 20, sh at level 0, p at level 0).

Notation "'u128_at' sh p x" :=
  (data_at sh t_secp256k1_u128 (uint128_to_val x) p)
  (at level 20, sh at level 0, p at level 0, x at level 0).
Notation "'u128_at_' sh p" :=
  (data_at_ sh t_secp256k1_u128 p)
  (at level 20, sh at level 0, p at level 0).

Notation "'acc_at' sh p x" :=
  (data_at sh t_secp256k1_acc (acc_to_val x) p)
  (at level 20, sh at level 0, p at level 0, x at level 0).

Notation "'u256_at' sh p x" :=
  (data_at sh t_secp256k1_uint256 (uint256_to_val x) p)
  (at level 20, sh at level 0, p at level 0, x at level 0).
Notation "'u256_at_' sh p" :=
  (data_at_ sh t_secp256k1_uint256 p)
  (at level 20, sh at level 0, p at level 0).

(** A reduced [Scalar] held in a [uint256] slot: same C struct, but the
    value carries the [< N] refinement. Differs from [u256_at] only in
    the value function ([scalar_to_val] vs [uint256_to_val]), so the two
    never match the same term. *)
Notation "'scalar_at' sh p x" :=
  (data_at sh t_secp256k1_uint256 (scalar_to_val x) p)
  (at level 20, sh at level 0, p at level 0, x at level 0).

Notation "'u512_at' sh p x" :=
  (data_at sh (tarray tulong 8) (uint512_to_val x) p)
  (at level 20, sh at level 0, p at level 0, x at level 0).
Notation "'u512_at_' sh p" :=
  (data_at_ sh (tarray tulong 8) p)
  (at level 20, sh at level 0, p at level 0).

(* ================================================================= *)
(** ** Signed-value notations -- [i64_at] / [i128_at]. *)

Notation "'i64_at' sh p x" :=
  (data_at sh tlong (int64_to_val x) p)
  (at level 20, sh at level 0, p at level 0, x at level 0).
Notation "'i64_at_' sh p" :=
  (data_at_ sh tlong p)
  (at level 20, sh at level 0, p at level 0).

Notation "'i128_at' sh p x" :=
  (data_at sh t_secp256k1_u128 (int128_to_val x) p)
  (at level 20, sh at level 0, p at level 0, x at level 0).
Notation "'i128_at_' sh p" :=
  (data_at_ sh t_secp256k1_u128 p)
  (at level 20, sh at level 0, p at level 0).

(* ================================================================= *)
(** ** Byte-array notations -- [bytes32_at] / [bytes8_at] / [zeros_at]. *)

(** A 32-byte buffer holding the byte list [bs] (each byte in [[0,256)]) --
    the [set_b32] / [get_b32] buffer. *)
Notation "'bytes32_at' sh p bs" :=
  (data_at sh (tarray tuchar 32) (bytes_to_val bs) p)
  (at level 20, sh at level 0, p at level 0, bs at level 0).
Notation "'bytes32_at_' sh p" :=
  (data_at_ sh (tarray tuchar 32) p)
  (at level 20, sh at level 0, p at level 0).

(** An 8-byte buffer holding the byte list [bs] (each byte in [[0,256)]) --
    the [read_be64] / [write_be64] buffer. *)
Notation "'bytes8_at' sh p bs" :=
  (data_at sh (tarray tuchar 8) (bytes_to_val bs) p)
  (at level 20, sh at level 0, p at level 0, bs at level 0).
Notation "'bytes8_at_' sh p" :=
  (data_at_ sh (tarray tuchar 8) p)
  (at level 20, sh at level 0, p at level 0).

(** An [n]-byte all-zero buffer -- the [memzero_explicit] /
    [memclear_explicit] postcondition. *)
Notation "'zeros_at' sh p n" :=
  (data_at sh (tarray tuchar n) (Zrepeat (Vint Int.zero) n) p)
  (at level 20, sh at level 0, p at level 0, n at level 0).
