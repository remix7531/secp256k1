(** * tactics.field: field-subsystem automation (the future prove_fe_linear home). *)
(** Copyright (C) 2026 remix7531
    SPDX-License-Identifier: MIT *)

(** The op-independent scaffolding factored out of the first field body proof
    (verif/field/fe_add).  Every carry-free 5x52 field linear op -- [fe_add] now,
    [fe_negate] / [fe_mul_int] / [fe_add_int] next -- needs these:

    - [fe_to_val_expand5]: expose the [fe_to_val] [map] as an explicit 5-element
      [Vlong] list, so VST's [forward] reads each limb as a concrete value.
      ([scalar_to_val] is already an explicit list; [fe_to_val] is a generic
      [map] over an arbitrary-length [list Z], so loads need this first.)
    - [fe_limb_mag_bound_add]: per-limb magnitude bounds add (the [fe_repr] post
      bound for [r := op(...)] with magnitude [mr + ma]).

    A full [prove_fe_linear] Ltac driver -- auto-running the load/store ripple
    and the [fe_repr] close -- is deliberately DEFERRED until a second linear op
    lands: an Ltac template is best factored from >= 2 concrete instances, and
    [fe_add] is the only field op in scope.  Until then this file is the shared
    lemma layer and verif/field/fe_add.v is the worked exemplar to clone from. *)

Require Import secp256k1.vst.base.
Require Import secp256k1.theory.field.field_bits.
Require Import secp256k1.contract.field.

(** [fe_to_val ls] (a [map]) as an explicit 5-[Vlong] list, given [Zlength ls = 5]. *)
Lemma fe_to_val_expand5 : forall ls, Zlength ls = 5 ->
  fe_to_val ls =
    Vlong (Int64.repr (Znth 0 ls)) :: Vlong (Int64.repr (Znth 1 ls))
    :: Vlong (Int64.repr (Znth 2 ls)) :: Vlong (Int64.repr (Znth 3 ls))
    :: Vlong (Int64.repr (Znth 4 ls)) :: nil.
Proof. intros ls H. unfold fe_to_val. list_solve. Qed.

(** Per-limb magnitude bounds are additive in the magnitude. *)
Lemma fe_limb_mag_bound_add : forall m1 m2 i,
  fe_limb_mag_bound m1 i + fe_limb_mag_bound m2 i = fe_limb_mag_bound (m1 + m2) i.
Proof. intros. unfold fe_limb_mag_bound. destruct (i <? 4)%nat; ring. Qed.
