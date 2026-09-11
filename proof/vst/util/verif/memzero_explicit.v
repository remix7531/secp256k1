(** * vst.util.verif.memzero_explicit: body proof for secp256k1_memzero_explicit *)
(** Copyright (C) 2026 remix7531
    SPDX-License-Identifier: MIT *)

Require Import secp256k1.vst.base.
Require Import secp256k1.vst.helper.notations.
Require Import secp256k1.vst.gprog.
Require Import secp256k1.vst.util.contract.
Require Import secp256k1.vst.tactics.core.

(* ================================================================= *)
(** ** secp256k1_memzero_explicit -- a pure-C byte-zeroing loop (no libc). *)

Lemma body_secp256k1_memzero_explicit:
  semax_body Vprog Gprog
    f_secp256k1_memzero_explicit spec_secp256k1_memzero_explicit.
Proof.
  start_function.

  (* ===== Setup: view the block as an uninitialized byte array ===== *)
  (* p = ptr -- view the pointer as a byte pointer *)
  forward.
  rewrite (memory_block_data_at__tarray_tuchar_eq sh p n) by rep_lia.

  (* ===== Loop: for (i = 0; i < len; i++) p[i] = 0 ===== *)
  (* invariant: the first [i] bytes are zeroed *)
  forward_for_simple_bound n
    (EX i:Z, PROP ()
      LOCAL (temp _p p; temp _ptr p; temp _len (Vlong (Int64.repr n)))
      SEP (data_at sh (tarray tuchar n)
             (Zrepeat (Vint Int.zero) i ++ Zrepeat (default_val tuchar) (n - i)) p)).
  - (* base: i = 0 -- the array is still wholly uninitialized *)
    entailer!.
    cancel.
  - (* step: store p[i] = 0, extending the zeroed prefix by one byte *)
    forward.
    entailer!; list_solve.
  - (* postcondition: i = n -- the array is fully zeroed *)
    entailer!; list_solve.
Qed.
