(** * Verif_u128_mul: Proof of body_secp256k1_u128_mul *)
(** Copyright (C) 2026 remix7531
    SPDX-License-Identifier: MIT *)

Require Import secp256k1.vst.base.
Require Import secp256k1.contract.helper.structs_int128.
Require Import secp256k1.contract.helper.notations.
Require Import secp256k1.contract.gprog.int128.
Require Import secp256k1.tactics.core.
Require Import secp256k1.tactics.int128.

(* ================================================================= *)
(** ** secp256k1_u128_mul -- [*r = (u64)a * (u64)b]. *)

(** Plumbing around the [umul128] spec: split the struct, call [umul128]
    for the low word, and store. *)

Lemma body_secp256k1_u128_mul:
  semax_body Vprog Gprog
    f_secp256k1_u128_mul spec_secp256k1_u128_mul.
Proof.
  start_function.

  (* Decompose uninitialised struct into .lo and .hi fields *)
  unfold data_at_, field_at_.
  unfold_data_at (field_at sh t_secp256k1_u128 [] _ r_ptr).
  assert_PROP (field_compatible t_secp256k1_u128 [StructField _hi] r_ptr)
    as Hfc by entailer!.
  rewrite (field_at_data_at sh _ [StructField _hi]) by reflexivity.

  (* r->lo = secp256k1_umul128(a, b, &r->hi) *)
  forward_call_umul128 a b
    (field_address t_secp256k1_u128 [StructField _hi] r_ptr) sh vret Hvret.

  (* r->lo = _t'1 *)
  forward.

  (* Provide witness and reassemble struct *)
  Exists vret.
  entailer!.
  unfold uint128_to_val.
  unfold_data_at (data_at sh t_secp256k1_u128 _ r_ptr).
  rewrite (field_at_data_at sh _ [StructField _hi]) by reflexivity.
  cancel.
Qed.
