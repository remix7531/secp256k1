(** * Verif_sumadd_fast: Proof of body_secp256k1_scalar_sumadd_fast *)
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
(** ** sumadd_fast -- [acc += a], into (c0,c1). *)

Lemma body_secp256k1_scalar_sumadd_fast:
  semax_body Vprog Gprog f_secp256k1_scalar_sumadd_fast spec_secp256k1_scalar_sumadd_fast.
Proof.
  start_function.

  (* acc->c0 += a *)
  forward. (* _t'3 = acc->c0 *)
  forward. (* acc->c0 = _t'3 + a *)

  (* acc->c1 += (acc->c0 < a) *)
  forward. (* _t'1 = acc->c1 *)
  forward. (* _t'2 = acc->c0 *)
  forward. (* acc->c1 = _t'1 + (_t'2 < a) *)

  Exists (mkAcc (acc_val acc + u64_val a) ltac:(rep_lia)).

  entailer!.

  apply derives_refl'.
  unfold acc_to_val.
  simpl.
  fold_limb.
  do 3 f_equal.
  + apply Int64.eqm_samerepr.
    apply sumadd_limb0; rep_lia.
  + f_equal. apply Int64.eqm_samerepr.
    rewrite Int.signed_repr
      by (unfold Z.b2z; destruct (Int64.ltu _ _); rep_lia).
    apply sumadd_limb1; rep_lia.
  + (* limb 2: acc + a < 2^128 so both sides are 0 *)
    f_equal. apply Int64.eqm_samerepr.
    unfold limb. change ((2^64)^Z.of_nat 2) with (2^128).
    unfold Int64.eqm.
    rewrite !Z.div_small by rep_lia.
    apply Zbits.eqmod_refl.
Qed.
