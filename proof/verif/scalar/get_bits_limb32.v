(** * verif.scalar.get_bits_limb32: body proof for secp256k1_scalar_get_bits_limb32. *)
(** Copyright (C) 2026 remix7531
    SPDX-License-Identifier: MIT *)

Require Import secp256k1.vst.base.
Require Import secp256k1.theory.limb_window.
Require Import secp256k1.contract.helper.notations.
Require Import secp256k1.contract.gprog.scalar.
Require Import secp256k1.tactics.core.
Require Import secp256k1.tactics.int128.
Require Import secp256k1.tactics.scalar.
Require Import secp256k1.tactics.hygiene.
(* Standing simpl/opacity discipline (Int64.Z_mod_modulus / Z.shiftr / Z.shiftl /
   Z.pow); without it the store/return value-eval simpl-unfolds into a blow-up and
   [forward] on the shift+mask return diverges. *)

(* ================================================================= *)
(** ** secp256k1_scalar_get_bits_limb32 -- single-limb bit-slice extraction. *)

(** Returns [(a >> offset) mod 2^count] when the window lies within one limb.

    The C reads limb [k = offset >> 6] of [a] (a runtime array subscript),
    shifts it right by [s = offset & 0x3F], and masks with
    [0xFFFFFFFF >> (32 - count) = 2^count - 1].  Since the preconds force
    [k in {0,1,2,3}] and [s + count <= 64], the [count]-bit window lies wholly
    in limb [k], so [(d[k] >> s) mod 2^count = (a / 2^offset) mod 2^count].

    The symbolic subscript [offset >> 6] is handled by rewriting
    [Int.shru (Int.repr offset) (Int.repr 6)] to [offset / 64] ([Hshru]) and
    case-splitting [offset / 64 in {0,1,2,3}] so the load and the final [Znth]
    reduce to a concrete limb.  The window arithmetic is the shared
    [limb_window] (theory/limb_window.v); the full C-value -> Z reduction is the
    file-local [INTRED]. *)
Lemma body_secp256k1_scalar_get_bits_limb32:
  semax_body Vprog Gprog
    f_secp256k1_scalar_get_bits_limb32 spec_secp256k1_scalar_get_bits_limb32.
Proof.
  start_function.

  (* ===== Setup: name hyps, limb index [k = offset/64], subscript [Hshru] ===== *)
  rename H into Hcount.
  rename H0 into Hoff0.
  rename H1 into Hwin.
  rename H2 into Hsum.

  assert_PROP (Zlength (scalar_to_val a) = 4) as Hlen by entailer!.

  (* limb index [k = offset / 64] is in [[0, 4)] (since [offset <= 255]) *)
  assert (Hk : 0 <= offset / 64 < 4).
  {
    split.
    - apply Z.div_pos; lia.
    - apply Z.div_lt_upper_bound; lia.
  }

  (* the runtime subscript [offset >> 6] is the limb index [offset / 64] *)
  assert (Hshru : Int.unsigned (Int.shru (Int.repr offset) (Int.repr 6)) = offset / 64).
  {
    rewrite Int.shru_div_two_p.
    rewrite (Int.unsigned_repr offset) by rep_lia.
    rewrite (Int.unsigned_repr 6) by rep_lia.
    rewrite two_p_correct.
    apply Int.unsigned_repr.
    change (two_power_pos _) with 64 in *.
    rep_lia.
  }

  (* ===== The mask [0xFFFFFFFF >> (32 - count)] is [2^count - 1] ===== *)
  (* shared [vst.integers.Int_shru_neg1_mask] *)
  assert (Hmask : Int.shru (Int.repr (-1)) (Int.repr (32 - count)) = Int.repr (2^count - 1))
    by (apply Int_shru_neg1_mask; lia).

  (* ===== Full C-value -> Z reduction of [(d[k] >> s) & mask] (any limb [k]) ===== *)
  (* [dk] is the loaded limb (passed in its concrete per-case form to dodge the
     [2^(64*0)] vs [a mod 2^64] conversion mismatch on a bare [apply]). *)
  assert (INTRED : forall (dk k : Z),
    0 <= k ->
    offset / 64 = k ->
    dk = (a / 2^(64*k)) mod 2^64 ->
    Int.repr
      (Int64.Z_mod_modulus
         (Z.land
            (Int64.Z_mod_modulus
               (Z.shiftr (Int64.unsigned (Int64.repr dk))
                  (Int64.Z_mod_modulus (Int.unsigned (Int.repr (Z.land offset 63))))))
            (Int64.Z_mod_modulus
               (Int.unsigned (Int.shru (Int.repr (-1)) (Int.repr (32 - count)))))))
    = Int.repr ((a / 2^offset) mod 2^count)).
  {
    intros dk0 k Hkpos Hkeq Hdkeq.
    subst dk0.
    (* [offset & 0x3F] is [offset mod 64] *)
    assert (Hland : Z.land offset 63 = offset mod 64).
    {
      change 63 with (Z.ones 6).
      rewrite Z.land_ones by lia.
      change (2^6) with 64.
      reflexivity.
    }
    rewrite Hland.
    assert (Hmod : 0 <= offset mod 64 < 64) by (apply Z.mod_pos_bound; lia).
    rewrite (Int.unsigned_repr (offset mod 64)) by rep_lia.
    rewrite Hmask.
    set (dk := (a / 2^(64*k)) mod 2^64).
    assert (Hdk : 0 <= dk < 2^64) by (subst dk; apply Z.mod_pos_bound; lia).
    (* peel [Int64.unsigned] / [Int64.Z_mod_modulus] off the in-range shift amount *)
    rewrite (Int64.unsigned_repr dk) by rep_lia.
    rewrite (Int64.Z_mod_modulus_eq (offset mod 64)).
    change Int64.modulus with (2^64).
    rewrite (Zmod_small (offset mod 64) (2^64)) by lia.
    rewrite Z.shiftr_div_pow2 by lia.
    assert (Hps : 0 < 2^(offset mod 64)) by (apply Z.pow_pos_nonneg; lia).
    (* the shifted limb is still in range, so its [Z_mod_modulus] is the identity *)
    assert (Hshft : 0 <= dk / 2^(offset mod 64) < 2^64).
    {
      split.
      - apply Z.div_pos; lia.
      - apply Z.div_lt_upper_bound; [lia |].
        apply Z.lt_le_trans with (2^64); [lia |].
        nia.
    }
    rewrite (Int64.Z_mod_modulus_eq (dk / 2^(offset mod 64))).
    change Int64.modulus with (2^64).
    rewrite (Zmod_small (dk / 2^(offset mod 64)) (2^64)) by lia.
    (* and likewise for the [2^count - 1] mask *)
    assert (Hmaskb : 0 <= 2^count - 1 < 2^32).
    {
      assert (2^0 <= 2^count) by (apply Z.pow_le_mono_r; lia).
      assert (2^count <= 2^32) by (apply Z.pow_le_mono_r; lia).
      change (2^0) with 1 in *.
      lia.
    }
    rewrite (Int.unsigned_repr (2^count - 1)) by rep_lia.
    rewrite (Int64.Z_mod_modulus_eq (2^count - 1)).
    change Int64.modulus with (2^64).
    rewrite (Zmod_small (2^count - 1) (2^64))
      by (assert (2^32 < 2^64) by (apply Z.pow_lt_mono_r; lia); lia).
    (* [_ & (2^count - 1)] is [_ mod 2^count] *)
    replace (2^count - 1) with (Z.ones count) by (rewrite Z.ones_equiv; lia).
    rewrite Z.land_ones by lia.
    assert (Hmodc : 0 <= (dk / 2^(offset mod 64)) mod 2^count < 2^count)
      by (apply Z.mod_pos_bound; apply Z.pow_pos_nonneg; lia).
    assert (Hc64 : 2^count < 2^64) by (apply Z.pow_lt_mono_r; lia).
    rewrite (Int64.Z_mod_modulus_eq ((dk / 2^(offset mod 64)) mod 2^count)).
    change Int64.modulus with (2^64).
    rewrite (Zmod_small _ (2^64)) by lia.
    f_equal.
    (* close via the window lemma: [offset = 64*k + offset mod 64] *)
    assert (Hoff_eq : 64*k + offset mod 64 = offset).
    {
      rewrite <- Hkeq.
      pose proof (Z.div_mod offset 64 ltac:(lia)) as Hdm.
      lia.
    }
    subst dk.
    pose proof (limb_window a (offset mod 64) count k (proj1 (scalar_range a)) Hkpos
                  ltac:(lia) ltac:(lia) ltac:(lia)) as Hwin0.
    rewrite Hwin0.
    rewrite Hoff_eq.
    reflexivity.
  }

  (* ===== Load limb [offset >> 6] of [a] ===== *)
  (* _t'1 = a->d[offset >> 6] *)
  forward.
  {
    (* tc_val of the loaded limb: reduce the symbolic [Znth] to a concrete [Vlong] *)
    rewrite Hshru.
    entailer!.
    replace (let (q, _) := Z.div_eucl offset 64 in q) with (offset / 64) by reflexivity.
    assert (Hc : offset/64=0 \/ offset/64=1 \/ offset/64=2 \/ offset/64=3) by lia.
    destruct Hc as [E|[E|[E|E]]]; rewrite E; simpl Znth; exact I.
  }

  (* ===== Case-split the limb index for the return-value reduction ===== *)
  assert (Hidx : offset/64=0 \/ offset/64=1 \/ offset/64=2 \/ offset/64=3) by lia.
  rewrite Hshru in *.
  destruct Hidx as [E|[E|[E|E]]]; rewrite E in *.

  - (* limb 0 *)
    unfold scalar_to_val.
    repeat (rewrite Znth_pos_cons by lia).
    rewrite Znth_0_cons.
    change (Z.pow_pos 2 64) with (2^64).
    (* return (t'1 >> (offset & 0x3F)) & (0xFFFFFFFF >> (32 - count)) *)
    forward.
    {
      entailer!.
      assert (Hland : Z.land offset 63 = offset mod 64).
      {
        change 63 with (Z.ones 6).
        rewrite Z.land_ones by lia.
        change (2^6) with 64.
        reflexivity.
      }
      rewrite Hland.
      assert (Hmod : 0 <= offset mod 64 < 64) by (apply Z.mod_pos_bound; lia).
      rewrite Int.unsigned_repr by rep_lia.
      change (Int.unsigned Int64.iwordsize') with 64.
      change (Int.unsigned Int.iwordsize) with 32.
      lia.
    }
    entailer!.
    f_equal.
    apply (INTRED _ 0 ltac:(lia) eq_refl).
    change (64 * 0) with 0.
    rewrite Z.pow_0_r, Z.div_1_r.
    reflexivity.

  - (* limb 1 *)
    unfold scalar_to_val.
    repeat (rewrite Znth_pos_cons by lia).
    rewrite Znth_0_cons.
    change (Z.pow_pos 2 64) with (2^64).
    (* return (t'1 >> (offset & 0x3F)) & (0xFFFFFFFF >> (32 - count)) *)
    forward.
    {
      entailer!.
      assert (Hland : Z.land offset 63 = offset mod 64).
      {
        change 63 with (Z.ones 6).
        rewrite Z.land_ones by lia.
        change (2^6) with 64.
        reflexivity.
      }
      rewrite Hland.
      assert (Hmod : 0 <= offset mod 64 < 64) by (apply Z.mod_pos_bound; lia).
      rewrite Int.unsigned_repr by rep_lia.
      change (Int.unsigned Int64.iwordsize') with 64.
      change (Int.unsigned Int.iwordsize) with 32.
      lia.
    }
    entailer!.
    f_equal.
    apply (INTRED _ 1 ltac:(lia) eq_refl).
    change (64 * 1) with 64.
    reflexivity.

  - (* limb 2 *)
    unfold scalar_to_val.
    repeat (rewrite Znth_pos_cons by lia).
    rewrite Znth_0_cons.
    change (Z.pow_pos 2 128) with (2^128).
    (* return (t'1 >> (offset & 0x3F)) & (0xFFFFFFFF >> (32 - count)) *)
    forward.
    {
      entailer!.
      assert (Hland : Z.land offset 63 = offset mod 64).
      {
        change 63 with (Z.ones 6).
        rewrite Z.land_ones by lia.
        change (2^6) with 64.
        reflexivity.
      }
      rewrite Hland.
      assert (Hmod : 0 <= offset mod 64 < 64) by (apply Z.mod_pos_bound; lia).
      rewrite Int.unsigned_repr by rep_lia.
      change (Int.unsigned Int64.iwordsize') with 64.
      change (Int.unsigned Int.iwordsize) with 32.
      lia.
    }
    entailer!.
    f_equal.
    apply (INTRED _ 2 ltac:(lia) eq_refl).
    change (64 * 2) with 128.
    reflexivity.

  - (* limb 3 *)
    unfold scalar_to_val.
    repeat (rewrite Znth_pos_cons by lia).
    rewrite Znth_0_cons.
    change (Z.pow_pos 2 192) with (2^192).
    (* return (t'1 >> (offset & 0x3F)) & (0xFFFFFFFF >> (32 - count)) *)
    forward.
    {
      entailer!.
      assert (Hland : Z.land offset 63 = offset mod 64).
      {
        change 63 with (Z.ones 6).
        rewrite Z.land_ones by lia.
        change (2^6) with 64.
        reflexivity.
      }
      rewrite Hland.
      assert (Hmod : 0 <= offset mod 64 < 64) by (apply Z.mod_pos_bound; lia).
      rewrite Int.unsigned_repr by rep_lia.
      change (Int.unsigned Int64.iwordsize') with 64.
      change (Int.unsigned Int.iwordsize) with 32.
      lia.
    }
    entailer!.
    f_equal.
    apply (INTRED _ 3 ltac:(lia) eq_refl).
    change (64 * 3) with 192.
    reflexivity.
Qed.
