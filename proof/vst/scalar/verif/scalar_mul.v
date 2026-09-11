(** * Verif_scalar_mul: Proof of body_secp256k1_scalar_mul *)
(** Copyright (C) 2026 remix7531
    SPDX-License-Identifier: MIT *)

Require Import secp256k1.vst.base.
Require Import secp256k1.vst.helper.structs_scalar.
Require Import secp256k1.vst.helper.notations.
Require Import secp256k1.vst.gprog.
Require secp256k1.specification.
Import specification.Math.
Import specification.Math.residues.
Require Import secp256k1.vst.tactics.core.
Require Import secp256k1.vst.tactics.int128.
Require Import secp256k1.vst.tactics.scalar.

(* ================================================================= *)
(** ** secp256k1_scalar_mul -- [(a * b) mod N]. *)

Lemma body_secp256k1_scalar_mul:
  semax_body Vprog Gprog
    f_secp256k1_scalar_mul spec_secp256k1_scalar_mul.
Proof.
  start_function.

  (* Split on whether the result aliases the first input ([r_ptr = a_ptr]) *)
  destruct alias.

  (* ===== alias = true: in-place mul(r, r, b) (r_ptr = a_ptr) ===== *)

  (* One writable chunk at [r_ptr] holds [a]; [mul_512] reads it into the
     local [l] before [reduce_512] overwrites it, so the in-place use is
     sound and the single chunk suffices. *)
  - specialize (H eq_refl).
    subst a_ptr.
    rewrite !scalar_to_val_eq.
    change t_secp256k1_scalar with t_secp256k1_uint256.

    (* secp256k1_scalar_mul_512(l, r, b) -- reads the shared chunk as [a] *)
    forward_call_scalar_mul_512 v_l r_ptr b_ptr
      (scalar_to_u256 a) (scalar_to_u256 b)
      Tsh sh_r sh_b l Hl.
    cancel.

    (* secp256k1_scalar_reduce_512(r, l) -- the (still [a]) chunk weakens to data_at_ *)
    forward_call_scalar_reduce_512 r_ptr v_l l sh_r Tsh r Hr.

    (* ===== Postcondition: C result = scalar_mul a b ===== *)
    Exists r.
    entailer!.
    (* Scalar extensionality ([scalar_eq_ext]); the value equality is [Hr] *)
    apply scalar_eq_ext.
    rewrite Hr.
    reflexivity.

  (* ===== alias = false: the ordinary non-aliasing proof ===== *)

  - specialize (H0 eq_refl).
    clear H.
    rewrite !scalar_to_val_eq.
    change t_secp256k1_scalar with t_secp256k1_uint256.

    (* secp256k1_scalar_mul_512(l, a, b) *)
    forward_call_scalar_mul_512 v_l a_ptr b_ptr
      (scalar_to_u256 a) (scalar_to_u256 b)
      Tsh sh_a sh_b l Hl.
    cancel.

    (* secp256k1_scalar_reduce_512(r, l) *)
    forward_call_scalar_reduce_512 r_ptr v_l l sh_r Tsh r Hr.

    (* ===== Postcondition: C result = scalar_mul a b ===== *)
    Exists r.
    entailer!.
    (* Scalar extensionality ([scalar_eq_ext]); the value equality is [Hr] *)
    apply scalar_eq_ext.
    rewrite Hr.
    reflexivity.
Qed.
