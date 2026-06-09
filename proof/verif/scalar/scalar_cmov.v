(** * verif.scalar.scalar_cmov: Proof of body_secp256k1_scalar_cmov. *)
(** Copyright (C) 2026 remix7531
    SPDX-License-Identifier: MIT *)

Require Import secp256k1.vst.base.
Require Import secp256k1.contract.helper.notations.
Require Import secp256k1.contract.gprog.scalar.
Require Import secp256k1.tactics.core.
Require Import secp256k1.tactics.int128.
Require Import secp256k1.tactics.scalar.

(* ================================================================= *)
(** ** secp256k1_scalar_cmov -- [*r := flag ? a : r0]. *)

(** [*r := flag ? a : r0] by constant-time masking. The extraction unit
    [#define]s [volatile] away (the [volatile int vflag] hardening hint becomes
    a plain temp and the [do{}while(0)] fence a no-op loop -- no [EF_vstore] /
    [EF_vload] builtins), so the bitwise-select goes through: [mask0 = vflag - 1],
    [mask1 = ~mask0], and each limb [(r_i & mask0) | (a_i & mask1)] is [a_i] when
    [flag = 1] (mask0 = 0, mask1 = -1) and [r_i] when [flag = 0] (mask0 = -1,
    mask1 = 0). *)
Lemma body_secp256k1_scalar_cmov:
  semax_body Vprog Gprog
    f_secp256k1_scalar_cmov spec_secp256k1_scalar_cmov.
Proof.
  start_function.

  (* ===== Stage 0: vflag = flag, fence, mask0 = vflag - 1, mask1 = ~mask0 ===== *)

  (* vflag = flag (a plain temp -- volatile neutralized in the extraction) *)
  forward.
  (* empty do {} while (0) fence -- a no-op loop after volatile removal *)
  match goal with |- semax _ ?E _ _ => forward_loop E break: E end.
  1: entailer!!.
  1: forward.
  1: entailer!!.
  (* mask0 = vflag + ~0 (= vflag - 1) *)
  forward.
  (* mask1 = ~mask0 *)
  forward.

  (* ===== Stage 1: r->d[i] = (r->d[i] & mask0) | (a->d[i] & mask1), i = 0..3 ===== *)

  (* limb 0: load r->d[0] / a->d[0], mask-select, store *)
  forward.
  forward.
  forward.
  (* limb 1: load r->d[1] / a->d[1], mask-select, store *)
  forward. (* _t'5 = r->d[1] *)
  forward. (* _t'6 = a->d[1] *)
  forward. (* r->d[1] = (_t'5 & mask0) | (_t'6 & mask1) *)
  (* limb 2: load r->d[2] / a->d[2], mask-select, store *)
  forward. (* _t'3 = r->d[2] *)
  forward. (* _t'4 = a->d[2] *)
  forward. (* r->d[2] = (_t'3 & mask0) | (_t'4 & mask1) *)
  (* limb 3: load r->d[3] / a->d[3], mask-select, store *)
  forward. (* _t'1 = r->d[3] *)
  forward. (* _t'2 = a->d[3] *)
  forward. (* r->d[3] = (_t'1 & mask0) | (_t'2 & mask1) *)

  (* ===== Postcondition: select yields [a] (flag = 1) or [r0] (flag = 0) ===== *)

  Exists (if Z.eq_dec flag 1 then a else r0).
  entailer!!.
  apply derives_refl'.
  f_equal.
  destruct H as [Hf | Hf]; subst flag.
  - (* flag = 0: mask0 = -1, mask1 = 0, so each limb keeps r0 *)
    assert (Hm0 : Int64.add (Int64.repr 0) (Int64.not (Int64.repr 0)) = Int64.mone)
      by (apply Int64.same_if_eq; reflexivity).
    assert (Hnm : Int64.not Int64.mone = Int64.zero)
      by (apply Int64.same_if_eq; reflexivity).
    rewrite !Hm0, !Int64.and_mone, !Hnm, !Int64.and_zero, !Int64.or_zero.
    destruct (Z.eq_dec 0 1) as [E|_];[discriminate|].
    reflexivity.
  - (* flag = 1: mask0 = 0, mask1 = -1, so each limb takes a *)
    assert (Hm1 : Int64.add (Int64.repr 1) (Int64.not (Int64.repr 0)) = Int64.zero)
      by (apply Int64.same_if_eq; reflexivity).
    assert (Hnz : Int64.not Int64.zero = Int64.mone)
      by (apply Int64.same_if_eq; reflexivity).
    rewrite !Hm1, !Int64.and_zero, !Hnz, !Int64.and_mone, !Int64.or_zero_l.
    destruct (Z.eq_dec 1 1) as [_|E];[|contradiction].
    reflexivity.
Qed.
