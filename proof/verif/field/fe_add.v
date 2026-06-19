(** * verif.field.fe_add: body proof for secp256k1_fe_add (= fe_impl_add). *)
(** Copyright (C) 2026 remix7531
    SPDX-License-Identifier: MIT *)

(** The first field op, and the end-to-end validation of the field scaffolding
    (model/contract/extraction/Gprog/representation).  With VERIFY off,
    [secp256k1_fe_add] is the bare leaf [secp256k1_fe_impl_add]: 5 carry-free
    limb stores [r->n[i] += a->n[i]].  Magnitudes add ([mr + ma <= 32] keeps each
    sum below [2^64]); the residue becomes [(vr + va) mod p].  Both the disjoint
    and the in-place ([fe_add(r,r)]) calls are covered via the [alias] flag.

    The 5x52 struct is shape-identical to the scalar [{d[4]}], so the [r->n[i]]
    loads/stores go through [forward] like the scalar limb stores; the only field
    specifics are expanding [fe_to_val] to an explicit 5-list (so [forward] sees
    the limbs are [Vlong]s) and closing the value clause via [eval5_add]. *)

Require Import secp256k1.vst.base.
Require Import secp256k1.theory.arithmetic.
Require Import secp256k1.theory.field.field_bits.
Require Import secp256k1.contract.helper.notations.
Require Import secp256k1.contract.gprog.field.
Require Import secp256k1.model.field.
Require Import secp256k1.contract.field.
Require Import secp256k1.tactics.core.
Require Import secp256k1.tactics.field.

Lemma body_secp256k1_fe_impl_add :
  semax_body Vprog Gprog
    f_secp256k1_fe_impl_add spec_secp256k1_fe_impl_add.
Proof.
  start_function.

  (* Shared field-linear-op scaffolding (see tactics/field.v):
     [HE] re-expresses [fe_to_val] as an explicit 5-list (so [forward] reads each
     limb), [Hbadd] is the magnitude-bound additivity for the [fe_repr] post. *)
  pose proof fe_to_val_expand5 as HE.
  pose proof fe_limb_mag_bound_add as Hbadd.

  destruct H2 as (Hlrlen & Hlrb & Hlrv).
  destruct H3 as (Hlalen & Hlab & Hlav).

  destruct alias.
  - (* alias = true: in-place doubling fe_add(r, r). *)
    destruct (H4 eq_refl) as (Hpa & Hll & Hmm & Hvv). subst.
    rewrite (HE lr Hlrlen).

    (* limb 0: r->n[0] += a->n[0] -- a is r here, so both loads read r->n[0] *)
    forward. (* _t'9 = r->n[0] *)
    forward. (* _t'10 = a->n[0] *)
    forward. (* r->n[0] = _t'9 + _t'10 *)
    (* limb 1: r->n[1] += a->n[1] *)
    forward. (* _t'7 = r->n[1] *)
    forward. (* _t'8 = a->n[1] *)
    forward. (* r->n[1] = _t'7 + _t'8 *)
    (* limb 2: r->n[2] += a->n[2] *)
    forward. (* _t'5 = r->n[2] *)
    forward. (* _t'6 = a->n[2] *)
    forward. (* r->n[2] = _t'5 + _t'6 *)
    (* limb 3: r->n[3] += a->n[3] *)
    forward. (* _t'3 = r->n[3] *)
    forward. (* _t'4 = a->n[3] *)
    forward. (* r->n[3] = _t'3 + _t'4 *)
    (* limb 4: r->n[4] += a->n[4] *)
    forward. (* _t'1 = r->n[4] *)
    forward. (* _t'2 = a->n[4] *)
    forward. (* r->n[4] = _t'1 + _t'2 *)

    Exists [Z.add (Znth 0 lr) (Znth 0 lr); Z.add (Znth 1 lr) (Znth 1 lr);
            Z.add (Znth 2 lr) (Znth 2 lr); Z.add (Znth 3 lr) (Znth 3 lr);
            Z.add (Znth 4 lr) (Znth 4 lr)].
    entailer!.

    (* ===== Postcondition: fe_repr + magnitude range for r' ===== *)

    split.
    + unfold fe_repr. split; [| split].
      * reflexivity.
      * intros i Hi. pose proof (Hlrb i Hi) as Hb. pose proof (Hbadd mr mr (Z.to_nat i)) as Hba.
        assert (Hc: i = 0 \/ i = 1 \/ i = 2 \/ i = 3 \/ i = 4) by lia.
        destruct Hc as [E|[E|[E|[E|E]]]]; subst i; list_solve.
      * change (Znth 0 [Znth 0 lr + Znth 0 lr; Znth 1 lr + Znth 1 lr; Znth 2 lr + Znth 2 lr; Znth 3 lr + Znth 3 lr; Znth 4 lr + Znth 4 lr]) with (Znth 0 lr + Znth 0 lr);
        change (Znth 1 [Znth 0 lr + Znth 0 lr; Znth 1 lr + Znth 1 lr; Znth 2 lr + Znth 2 lr; Znth 3 lr + Znth 3 lr; Znth 4 lr + Znth 4 lr]) with (Znth 1 lr + Znth 1 lr);
        change (Znth 2 [Znth 0 lr + Znth 0 lr; Znth 1 lr + Znth 1 lr; Znth 2 lr + Znth 2 lr; Znth 3 lr + Znth 3 lr; Znth 4 lr + Znth 4 lr]) with (Znth 2 lr + Znth 2 lr);
        change (Znth 3 [Znth 0 lr + Znth 0 lr; Znth 1 lr + Znth 1 lr; Znth 2 lr + Znth 2 lr; Znth 3 lr + Znth 3 lr; Znth 4 lr + Znth 4 lr]) with (Znth 3 lr + Znth 3 lr);
        change (Znth 4 [Znth 0 lr + Znth 0 lr; Znth 1 lr + Znth 1 lr; Znth 2 lr + Znth 2 lr; Znth 3 lr + Znth 3 lr; Znth 4 lr + Znth 4 lr]) with (Znth 4 lr + Znth 4 lr);
        rewrite eval5_add; apply Zplus_mod.
    + intros i Hi. assert (Hc: i = 0 \/ i = 1 \/ i = 2 \/ i = 3 \/ i = 4) by lia.
      destruct Hc as [E|[E|[E|[E|E]]]]; subst i; list_solve.
  - (* alias = false: disjoint r and a. *)
    specialize (H5 eq_refl).
    rewrite (HE lr Hlrlen), (HE la Hlalen). Intros.

    (* limb 0: r->n[0] += a->n[0] *)
    forward. (* _t'9 = r->n[0] *)
    forward. (* _t'10 = a->n[0] *)
    forward. (* r->n[0] = _t'9 + _t'10 *)
    (* limb 1: r->n[1] += a->n[1] *)
    forward. (* _t'7 = r->n[1] *)
    forward. (* _t'8 = a->n[1] *)
    forward. (* r->n[1] = _t'7 + _t'8 *)
    (* limb 2: r->n[2] += a->n[2] *)
    forward. (* _t'5 = r->n[2] *)
    forward. (* _t'6 = a->n[2] *)
    forward. (* r->n[2] = _t'5 + _t'6 *)
    (* limb 3: r->n[3] += a->n[3] *)
    forward. (* _t'3 = r->n[3] *)
    forward. (* _t'4 = a->n[3] *)
    forward. (* r->n[3] = _t'3 + _t'4 *)
    (* limb 4: r->n[4] += a->n[4] *)
    forward. (* _t'1 = r->n[4] *)
    forward. (* _t'2 = a->n[4] *)
    forward. (* r->n[4] = _t'1 + _t'2 *)

    Exists [Z.add (Znth 0 lr) (Znth 0 la); Z.add (Znth 1 lr) (Znth 1 la);
            Z.add (Znth 2 lr) (Znth 2 la); Z.add (Znth 3 lr) (Znth 3 la);
            Z.add (Znth 4 lr) (Znth 4 la)].
    entailer!.

    (* ===== Postcondition: fe_repr + magnitude range for r' ===== *)

    split.
    { unfold fe_repr. split; [| split].
      { reflexivity. }
      { intros i Hi. pose proof (Hlrb i Hi). pose proof (Hlab i Hi).
        pose proof (Hbadd mr ma (Z.to_nat i)).
        assert (Hc: i = 0 \/ i = 1 \/ i = 2 \/ i = 3 \/ i = 4) by lia.
        destruct Hc as [E|[E|[E|[E|E]]]]; subst i; list_solve. }
      { change (Znth 0 [Znth 0 lr + Znth 0 la; Znth 1 lr + Znth 1 la; Znth 2 lr + Znth 2 la; Znth 3 lr + Znth 3 la; Znth 4 lr + Znth 4 la]) with (Znth 0 lr + Znth 0 la);
        change (Znth 1 [Znth 0 lr + Znth 0 la; Znth 1 lr + Znth 1 la; Znth 2 lr + Znth 2 la; Znth 3 lr + Znth 3 la; Znth 4 lr + Znth 4 la]) with (Znth 1 lr + Znth 1 la);
        change (Znth 2 [Znth 0 lr + Znth 0 la; Znth 1 lr + Znth 1 la; Znth 2 lr + Znth 2 la; Znth 3 lr + Znth 3 la; Znth 4 lr + Znth 4 la]) with (Znth 2 lr + Znth 2 la);
        change (Znth 3 [Znth 0 lr + Znth 0 la; Znth 1 lr + Znth 1 la; Znth 2 lr + Znth 2 la; Znth 3 lr + Znth 3 la; Znth 4 lr + Znth 4 la]) with (Znth 3 lr + Znth 3 la);
        change (Znth 4 [Znth 0 lr + Znth 0 la; Znth 1 lr + Znth 1 la; Znth 2 lr + Znth 2 la; Znth 3 lr + Znth 3 la; Znth 4 lr + Znth 4 la]) with (Znth 4 lr + Znth 4 la);
        rewrite eval5_add; apply Zplus_mod. } }
    { intros i Hi. assert (Hc: i = 0 \/ i = 1 \/ i = 2 \/ i = 3 \/ i = 4) by lia.
      destruct Hc as [E|[E|[E|[E|E]]]]; subst i; list_solve. }

    rewrite (HE la Hlalen). cancel.
Qed.
