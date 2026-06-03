(** * Verif_sumadd: Proof of body_secp256k1_scalar_sumadd *)
(** Copyright (C) 2026 remix7531
    SPDX-License-Identifier: MIT *)

Require Import secp256k1.vst.base.
Require Import secp256k1.contract.helper.notations.
Require Import secp256k1.contract.gprog.scalar.
Require Import secp256k1.contract.impl.scalar.
Require Import secp256k1.tactics.core.
Require Import secp256k1.tactics.int128.
Require Import secp256k1.tactics.scalar.

(* ================================================================= *)
(** ** sumadd -- [acc += a]. *)

Lemma body_secp256k1_scalar_sumadd:
  semax_body Vprog Gprog f_secp256k1_scalar_sumadd spec_secp256k1_scalar_sumadd.
Proof.
  start_function.

  (* acc->c0 += a *)
  forward. (* _t'5 = acc->c0 *)
  forward. (* acc->c0 = _t'5 + a *)

  (* over = (acc->c0 < a) *)
  forward. (* _t'4 = acc->c0 *)
  forward. (* over = (_t'4 < a) *)

  (* acc->c1 += over *)
  forward. (* _t'3 = acc->c1 *)
  forward. (* acc->c1 = _t'3 + over *)

  (* acc->c2 += (acc->c1 < over) *)
  forward. (* _t'1 = acc->c2 *)
  forward. (* _t'2 = acc->c1 *)
  forward. (* acc->c2 = _t'1 + (_t'2 < over) *)

  Exists (mkAcc (acc_val acc + u64_val a) ltac:(rep_lia)).
  entailer!.

  unfold acc_to_val.
  apply derives_refl'.
  simpl.
  fold_limb.
  do 3 f_equal.
  + apply Int64.eqm_samerepr.
    apply sumadd_limb0; rep_lia.
  + f_equal. apply Int64.eqm_samerepr.
    rewrite Int.unsigned_repr
      by (unfold Z.b2z; destruct (Int64.ltu _ _); rep_lia).
    apply sumadd_limb1; rep_lia.
  + f_equal. apply Int64.eqm_samerepr.
    apply sumadd_limb2; rep_lia.
Qed.
