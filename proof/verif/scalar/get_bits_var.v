(** * verif.scalar.get_bits_var: body proof for secp256k1_scalar_get_bits_var. *)
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
(** ** File-local Int64 C-value reduction (pure Z). *)

(** Full C-value -> Z reduction of the straddle return
    [((d[k] >> s) | (d[k+1] << (64 - s))) & (0xFFFFFFFF >> (32 - count))]
    (limbs passed in their per-case concrete form via defining equations to
    dodge the [2^(64*0)] vs [a mod 2^64] mismatch on a bare [apply]).  All the
    [Int64.Z_mod_modulus] / [Int64.unsigned] wrappers are in range and peel off;
    the OR is the disjoint two-limb combine, and the [2^count - 1] mask is
    [mod 2^count]. *)
Lemma get_bits_var_comb : forall (a offset count dlo dhi k : Z),
  0 <= a ->
  0 <= k ->
  offset / 64 = k ->
  dlo = (a / 2 ^ (64 * k)) mod 2 ^ 64 ->
  dhi = (a / 2 ^ (64 * (k + 1))) mod 2 ^ 64 ->
  0 < count <= 32 ->
  offset mod 64 + count > 64 ->
  offset + count <= 256 ->
  Int.repr
    (Int64.Z_mod_modulus
       (Z.land
          (Int64.Z_mod_modulus
             (Z.lor
                (Int64.Z_mod_modulus
                   (Z.shiftr (Int64.unsigned (Int64.repr dlo))
                      (Int64.Z_mod_modulus
                         (Int.unsigned (Int.repr (Z.land offset 63))))))
                (Int64.Z_mod_modulus
                   (Z.shiftl (Int64.unsigned (Int64.repr dhi))
                      (Int64.Z_mod_modulus
                         (Int.unsigned (Int.repr (64 - Z.land offset 63))))))))
          (Int64.Z_mod_modulus
             (Int.unsigned (Int.shru (Int.repr (-1)) (Int.repr (32 - count)))))))
  = Int.repr ((a / 2 ^ offset) mod 2 ^ count).
Proof.
  intros a offset count dlo dhi k Ha Hk Hkeq Hdlo Hdhi Hcount Hstraddle Hsum.

  (* ===== Setup: reduce the shift amount [s], peel the C-value wrappers ===== *)
  assert (Hoff0 : 0 <= offset).
  {
    pose proof (Z.div_mod offset 64 ltac:(lia)) as Hdm.
    pose proof (Z.mod_pos_bound offset 64 ltac:(lia)) as Hmb.
    rewrite Hkeq in Hdm.
    lia.
  }

  (* [offset & 0x3F = offset mod 64], abbreviated [s], with [0 < s < 64] *)
  assert (Hland : Z.land offset 63 = offset mod 64).
  { change 63 with (Z.ones 6).
    rewrite Z.land_ones by lia.
    change (2 ^ 6) with 64.
    reflexivity. }
  rewrite Hland.
  assert (Hmod : 0 <= offset mod 64 < 64) by (apply Z.mod_pos_bound; lia).
  rewrite (Int.unsigned_repr (offset mod 64)) by rep_lia.
  rewrite (Int.unsigned_repr (64 - offset mod 64)) by rep_lia.

  (* the mask [0xFFFFFFFF >> (32 - count) = 2^count - 1] (shared
     [vst.integers.Int_shru_neg1_mask]) *)
  assert (Hmask : Int.shru (Int.repr (-1)) (Int.repr (32 - count)) = Int.repr (2 ^ count - 1))
    by (apply Int_shru_neg1_mask; lia).
  rewrite Hmask.
  set (s := offset mod 64) in *.
  assert (Hsd : 0 < s < 64) by (subst s; lia).
  assert (Hdlo_b : 0 <= dlo < 2 ^ 64) by (subst dlo; apply Z.mod_pos_bound; lia).
  assert (Hdhi_b : 0 <= dhi < 2 ^ 64) by (subst dhi; apply Z.mod_pos_bound; lia).

  (* peel the [Int64.unsigned] / [Int64.Z_mod_modulus] wrappers (all in range) *)
  rewrite (Int64.unsigned_repr dlo) by rep_lia.
  rewrite (Int64.unsigned_repr dhi) by rep_lia.
  rewrite (Int64.Z_mod_modulus_eq s).
  rewrite (Int64.Z_mod_modulus_eq (64 - s)).
  change Int64.modulus with (2 ^ 64).
  rewrite (Zmod_small s (2 ^ 64)) by lia.
  rewrite (Zmod_small (64 - s) (2 ^ 64)) by lia.
  rewrite Z.shiftr_div_pow2 by lia.
  rewrite Z.shiftl_mul_pow2 by lia.

  (* ===== Combine: the disjoint OR of the two limb pieces is addition ===== *)
  (* the OR of the two pieces is the disjoint combine -> [dlo/2^s + (dhi mod 2^s)*2^(64-s)] *)
  assert (Hps : 0 < 2 ^ s) by (apply Z.pow_pos_nonneg; lia).
  assert (Hlodiv : 0 <= dlo / 2 ^ s < 2 ^ 64).
  { split; [apply Z.div_pos; lia |].
    apply Z.le_lt_trans with dlo; [| lia].
    apply Z.div_le_upper_bound; [lia |].
    rewrite <- (Z.mul_1_l dlo) at 1.
    apply Z.mul_le_mono_nonneg_r; lia. }
  rewrite (Int64.Z_mod_modulus_eq (dlo / 2 ^ s)).
  change Int64.modulus with (2 ^ 64).
  rewrite (Zmod_small (dlo / 2 ^ s) (2 ^ 64)) by lia.
  rewrite (Int64.Z_mod_modulus_eq (dhi * 2 ^ (64 - s))).
  change Int64.modulus with (2 ^ 64).

  (* the high piece truncated to 64 bits keeps only [dhi]'s low [s] bits *)
  assert (Hhi_red : (dhi * 2 ^ (64 - s)) mod 2 ^ 64 = (dhi mod 2 ^ s) * 2 ^ (64 - s)).
  { rewrite (Z_div_mod_eq_full dhi (2 ^ s)) at 1.
    replace (2 ^ 64) with (2 ^ s * 2 ^ (64 - s))
      by (rewrite <- Z.pow_add_r by lia; f_equal; lia).
    rewrite Z.mul_add_distr_r.
    rewrite <- Z.mul_assoc.
    rewrite Z.add_comm.
    replace (2 ^ s * (dhi / 2 ^ s * 2 ^ (64 - s)))
      with ((dhi / 2 ^ s) * (2 ^ s * 2 ^ (64 - s))) by ring.
    rewrite Z.mod_add
      by (apply Z.neq_sym; apply Z.lt_neq; apply Z.mul_pos_pos; apply Z.pow_pos_nonneg; lia).
    rewrite Z.mod_small; [reflexivity |].
    assert (Hm : 0 <= dhi mod 2 ^ s < 2 ^ s)
      by (apply Z.mod_pos_bound; apply Z.pow_pos_nonneg; lia).
    split.
    - apply Z.mul_nonneg_nonneg; [lia | apply Z.pow_nonneg; lia].
    - apply Zmult_lt_compat_r; [apply Z.pow_pos_nonneg; lia | lia]. }
  rewrite Hhi_red.

  (* the OR of two disjoint pieces is addition ([lor_disjoint_is_add]); the
     low piece is [< 2^(64-s)] and the high piece is [2^(64-s)]-aligned *)
  assert (Hlodiv2 : 0 <= dlo / 2 ^ s < 2 ^ (64 - s)).
  { split; [apply Z.div_pos; lia |].
    apply Z.div_lt_upper_bound; [lia |].
    rewrite <- Z.pow_add_r by lia.
    replace (s + (64 - s)) with 64 by lia.
    lia. }
  assert (Hhimod : 0 <= dhi mod 2 ^ s) by (apply Z.mod_pos_bound; lia).
  rewrite (lor_disjoint_is_add (dlo / 2 ^ s) (dhi mod 2 ^ s) (64 - s)
             ltac:(lia) Hlodiv2 Hhimod).

  (* and that sum is the 64-bit window of the two adjacent limbs *)
  rewrite (shifted_pair_window dlo dhi s 64 Hdlo_b Hdhi_b ltac:(lia)).

  (* the 64-bit window is in range; [Z_mod_modulus] off it is identity *)
  assert (Hw64 : 0 <= ((dlo + dhi * 2 ^ 64) / 2 ^ s) mod 2 ^ 64 < 2 ^ 64)
    by (apply Z.mod_pos_bound; lia).
  rewrite (Int64.Z_mod_modulus_eq (((dlo + dhi * 2 ^ 64) / 2 ^ s) mod 2 ^ 64)).
  change Int64.modulus with (2 ^ 64).
  rewrite (Zmod_small _ (2 ^ 64)) by lia.

  (* mask: [_ & (2^count - 1)] = [_ mod 2^count] *)
  assert (Hmaskb : 0 <= 2 ^ count - 1 < 2 ^ 32).
  { assert (2 ^ 0 <= 2 ^ count) by (apply Z.pow_le_mono_r; lia).
    assert (2 ^ count <= 2 ^ 32) by (apply Z.pow_le_mono_r; lia).
    change (2 ^ 0) with 1 in *.
    lia. }
  rewrite (Int.unsigned_repr (2 ^ count - 1)) by rep_lia.
  rewrite (Int64.Z_mod_modulus_eq (2 ^ count - 1)).
  change Int64.modulus with (2 ^ 64).
  rewrite (Zmod_small (2 ^ count - 1) (2 ^ 64))
    by (assert (2 ^ 32 < 2 ^ 64) by (apply Z.pow_lt_mono_r; lia); lia).
  replace (2 ^ count - 1) with (Z.ones count) by (rewrite Z.ones_equiv; lia).
  rewrite Z.land_ones by lia.
  assert (Hc64 : 2 ^ count < 2 ^ 64) by (apply Z.pow_lt_mono_r; lia).
  assert (Hmodc : 0 <= (((dlo + dhi * 2 ^ 64) / 2 ^ s) mod 2 ^ 64) mod 2 ^ count < 2 ^ count)
    by (apply Z.mod_pos_bound; apply Z.pow_pos_nonneg; lia).
  rewrite (Int64.Z_mod_modulus_eq
             ((((dlo + dhi * 2 ^ 64) / 2 ^ s) mod 2 ^ 64) mod 2 ^ count)).
  change Int64.modulus with (2 ^ 64).
  rewrite (Zmod_small _ (2 ^ 64)) by lia.
  f_equal.

  (* ===== Closeout: fold the limbs into the window and relate to the slice ===== *)
  (* drop the inner [mod 2^64]: [count <= 32 <= 64], so it is absorbed *)
  assert (Hdvd : (2 ^ count | 2 ^ 64))
    by (exists (2 ^ (64 - count)); rewrite <- Z.pow_add_r by lia; f_equal; lia).
  rewrite (Z.mod_mod_divide _ (2 ^ 64) (2 ^ count)) by exact Hdvd.

  (* fold the two adjacent limbs into [(a/2^(64k)) mod 2^128], shift by [s] *)
  subst dlo dhi.
  rewrite (adjacent_limbs_fold a 64 k Ha ltac:(lia) Hk).
  change (2 ^ (2 * 64)) with (2 ^ 128).

  (* and finally relate the [128]-bit window to [(a/2^offset) mod 2^count] *)
  assert (Hoff_eq : 64 * k + s = offset).
  { subst s. rewrite <- Hkeq.
    pose proof (Z.div_mod offset 64 ltac:(lia)) as Hdm.
    lia. }
  rewrite <- Hoff_eq.
  rewrite Z.pow_add_r by lia.
  rewrite <- Z.div_div by (try apply Z.pow_nonzero; try apply Z.pow_pos_nonneg; lia).

  (* the [count]-bit window [[s, s+count)] of the 128-bit slice survives [mod 2^128] *)
  replace (2 ^ 128) with (2 ^ s * 2 ^ (128 - s))
    by (rewrite <- Z.pow_add_r by lia; f_equal; lia).
  rewrite Zaux.Zdiv_mod_mult by (apply Z.pow_nonneg; lia).
  assert (Hdvd3 : (2 ^ count | 2 ^ (128 - s)))
    by (exists (2 ^ (128 - s - count)); rewrite <- Z.pow_add_r by lia; f_equal; lia).
  rewrite (Z.mod_mod_divide _ (2 ^ (128 - s)) (2 ^ count)) by exact Hdvd3.
  reflexivity.
Qed.

(* ================================================================= *)
(** ** secp256k1_scalar_get_bits_var -- two-limb-aware bit-slice extraction. *)

(** Returns [(a >> offset) mod 2^count], handling a window straddling two
    limbs.  The single-limb branch (the window lies in one limb, i.e.
    [offset mod 64 + count <= 64], equivalently the C test
    [(offset+count-1) >> 6 == offset >> 6]) forwards to [get_bits_limb32].
    The straddle branch loads limbs [k = offset/64] and [k+1] and combines
    [(d[k] >> s | d[k+1] << (64 - s)) & (2^count - 1)] with [s = offset mod
    64]: the two limbs form bits [[64k, 64k+128)] of [a], shifting the pair
    down by [s] selects bits [[offset, offset+64)], and the mask keeps the low
    [count] of them. *)
Lemma body_secp256k1_scalar_get_bits_var:
  semax_body Vprog Gprog
    f_secp256k1_scalar_get_bits_var spec_secp256k1_scalar_get_bits_var.
Proof.
  start_function.

  (* ===== Setup: name hyps, scalar length, subscript [Hshru] ===== *)
  rename H into Hcount.
  rename H0 into Hoff0.
  rename H1 into Hsum.

  assert_PROP (Zlength (scalar_to_val a) = 4) as Hlen by entailer!.

  (* [offset >> 6] (as a [Z]) is the limb index [offset / 64]. *)
  assert (Hshru : forall x, 0 <= x < 2 ^ 32 ->
    Int.shru (Int.repr x) (Int.repr 6) = Int.repr (x / 64)).
  {
    intros x Hx.
    rewrite Int.shru_div_two_p.
    rewrite (Int.unsigned_repr x) by rep_lia.
    rewrite (Int.unsigned_repr 6) by rep_lia.
    rewrite two_p_correct.
    change (two_power_pos 6) with 64.
    reflexivity.
  }

  (* branch on the single-limb test [(offset+count-1) >> 6 == offset >> 6] *)
  forward_if.

  - (* ===== Single-limb branch: inline load + shift + mask ===== *)
    (* the C test rewrites to a pure-Z equation of limb indices *)
    assert (Hadd : Int.sub (Int.add (Int.repr offset) (Int.repr count)) (Int.repr 1)
                   = Int.repr (offset + count - 1))
      by (rewrite add_repr, sub_repr; reflexivity).
    rewrite Hadd in H.
    rewrite (Hshru (offset + count - 1)) in H by rep_lia.
    rewrite (Hshru offset) in H by rep_lia.

    assert (Hdiveq : (offset + count - 1) / 64 = offset / 64).
    {
      assert (Hb1 : 0 <= (offset + count - 1) / 64 < 2 ^ 32)
        by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
      assert (Hb2 : 0 <= offset / 64 < 2 ^ 32)
        by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
      apply repr_inj_unsigned in H; [exact H | rep_lia | rep_lia].
    }

    (* index equality is exactly the [get_bits_limb32] single-limb precond *)
    assert (Hwin : offset mod 64 + count <= 64).
    {
      pose proof (Z.div_mod offset 64 ltac:(lia)) as Hdm.
      pose proof (Z.div_mod (offset + count - 1) 64 ltac:(lia)) as Hdm2.
      pose proof (Z.mod_pos_bound offset 64 ltac:(lia)) as Hmb.
      pose proof (Z.mod_pos_bound (offset + count - 1) 64 ltac:(lia)) as Hmb2.
      rewrite Hdiveq in Hdm2.
      lia.
    }

    (* Master inlined [get_bits_limb32]'s body here (same returned value), so the
       branch is [(a->d[offset >> 6] >> (offset & 0x3F)) & (0xFFFFFFFF >> (32 -
       count))]: a single-limb load + shift + mask, mirroring [get_bits_limb32]. *)

    (* limb index [k = offset / 64] is in [[0, 4)] (since [offset <= 255]) *)
    assert (Hk : 0 <= offset / 64 < 4).
    {
      split.
      - apply Z.div_pos; lia.
      - apply Z.div_lt_upper_bound; lia.
    }

    (* the runtime subscript [offset >> 6] is the limb index [offset / 64] *)
    assert (Hshru_u : Int.unsigned (Int.shru (Int.repr offset) (Int.repr 6)) = offset / 64).
    {
      rewrite Int.shru_div_two_p.
      rewrite (Int.unsigned_repr offset) by rep_lia.
      rewrite (Int.unsigned_repr 6) by rep_lia.
      rewrite two_p_correct.
      apply Int.unsigned_repr.
      change (two_power_pos _) with 64 in *.
      rep_lia.
    }

    (* the mask [0xFFFFFFFF >> (32 - count)] is [2^count - 1] (shared
       [vst.integers.Int_shru_neg1_mask]) *)
    assert (Hmask : Int.shru (Int.repr (-1)) (Int.repr (32 - count)) = Int.repr (2 ^ count - 1))
      by (apply Int_shru_neg1_mask; lia).

    (* full C-value -> Z reduction of [(d[k] >> s) & mask] (any limb [k]); [dk] is
       the loaded limb, passed in its concrete per-case form to dodge the
       [2^(64*0)] vs [a mod 2^64] conversion mismatch on a bare [apply]. *)
    assert (INTRED : forall (dk k : Z),
      0 <= k ->
      offset / 64 = k ->
      dk = (a / 2 ^ (64 * k)) mod 2 ^ 64 ->
      Int.repr
        (Int64.Z_mod_modulus
           (Z.land
              (Int64.Z_mod_modulus
                 (Z.shiftr (Int64.unsigned (Int64.repr dk))
                    (Int64.Z_mod_modulus (Int.unsigned (Int.repr (Z.land offset 63))))))
              (Int64.Z_mod_modulus
                 (Int.unsigned (Int.shru (Int.repr (-1)) (Int.repr (32 - count)))))))
      = Int.repr ((a / 2 ^ offset) mod 2 ^ count)).
    {
      intros dk0 k Hkpos Hkeq Hdkeq.
      subst dk0.
      (* [offset & 0x3F] is [offset mod 64] *)
      assert (Hland : Z.land offset 63 = offset mod 64).
      {
        change 63 with (Z.ones 6).
        rewrite Z.land_ones by lia.
        change (2 ^ 6) with 64.
        reflexivity.
      }
      rewrite Hland.
      assert (Hmod : 0 <= offset mod 64 < 64) by (apply Z.mod_pos_bound; lia).
      rewrite (Int.unsigned_repr (offset mod 64)) by rep_lia.
      rewrite Hmask.
      set (dk := (a / 2 ^ (64 * k)) mod 2 ^ 64).
      assert (Hdk : 0 <= dk < 2 ^ 64) by (subst dk; apply Z.mod_pos_bound; lia).

      (* peel [Int64.unsigned] / [Int64.Z_mod_modulus] off the in-range shift amount *)
      rewrite (Int64.unsigned_repr dk) by rep_lia.
      rewrite (Int64.Z_mod_modulus_eq (offset mod 64)).
      change Int64.modulus with (2 ^ 64).
      rewrite (Zmod_small (offset mod 64) (2 ^ 64)) by lia.
      rewrite Z.shiftr_div_pow2 by lia.

      assert (Hps : 0 < 2 ^ (offset mod 64)) by (apply Z.pow_pos_nonneg; lia).
      (* the shifted limb is still in range, so its [Z_mod_modulus] is the identity *)
      assert (Hshft : 0 <= dk / 2 ^ (offset mod 64) < 2 ^ 64).
      {
        split.
        - apply Z.div_pos; lia.
        - apply Z.div_lt_upper_bound; [lia |].
          apply Z.lt_le_trans with (2 ^ 64); [lia |].
          nia.
      }
      rewrite (Int64.Z_mod_modulus_eq (dk / 2 ^ (offset mod 64))).
      change Int64.modulus with (2 ^ 64).
      rewrite (Zmod_small (dk / 2 ^ (offset mod 64)) (2 ^ 64)) by lia.

      (* and likewise for the [2^count - 1] mask *)
      assert (Hmaskb : 0 <= 2 ^ count - 1 < 2 ^ 32).
      {
        assert (2 ^ 0 <= 2 ^ count) by (apply Z.pow_le_mono_r; lia).
        assert (2 ^ count <= 2 ^ 32) by (apply Z.pow_le_mono_r; lia).
        change (2 ^ 0) with 1 in *.
        lia.
      }
      rewrite (Int.unsigned_repr (2 ^ count - 1)) by rep_lia.
      rewrite (Int64.Z_mod_modulus_eq (2 ^ count - 1)).
      change Int64.modulus with (2 ^ 64).
      rewrite (Zmod_small (2 ^ count - 1) (2 ^ 64))
        by (assert (2 ^ 32 < 2 ^ 64) by (apply Z.pow_lt_mono_r; lia); lia).

      (* [_ & (2^count - 1)] is [_ mod 2^count] *)
      replace (2 ^ count - 1) with (Z.ones count) by (rewrite Z.ones_equiv; lia).
      rewrite Z.land_ones by lia.
      assert (Hmodc : 0 <= (dk / 2 ^ (offset mod 64)) mod 2 ^ count < 2 ^ count)
        by (apply Z.mod_pos_bound; apply Z.pow_pos_nonneg; lia).
      assert (Hc64 : 2 ^ count < 2 ^ 64) by (apply Z.pow_lt_mono_r; lia).
      rewrite (Int64.Z_mod_modulus_eq ((dk / 2 ^ (offset mod 64)) mod 2 ^ count)).
      change Int64.modulus with (2 ^ 64).
      rewrite (Zmod_small _ (2 ^ 64)) by lia.
      f_equal.

      (* close via the window lemma: [offset = 64*k + offset mod 64] *)
      assert (Hoff_eq : 64 * k + offset mod 64 = offset).
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

    (* _t'3 = a->d[offset >> 6] *)
    forward.
    {
      (* tc_val of the loaded limb: reduce the symbolic [Znth] to a concrete [Vlong] *)
      rewrite Hshru_u.
      entailer!.
      replace (let (q, _) := Z.div_eucl offset 64 in q) with (offset / 64) by reflexivity.
      assert (Hc : offset / 64 = 0 \/ offset / 64 = 1 \/ offset / 64 = 2 \/ offset / 64 = 3) by lia.
      destruct Hc as [E | [E | [E | E]]]; rewrite E; simpl Znth; exact I.
    }

    (* case-split the limb index for the return-value reduction *)
    assert (Hidx : offset / 64 = 0 \/ offset / 64 = 1 \/ offset / 64 = 2 \/ offset / 64 = 3) by lia.
    rewrite Hshru_u in *.
    destruct Hidx as [E | [E | [E | E]]]; rewrite E in *.

    + (* limb 0 *)
      unfold scalar_to_val.
      repeat (rewrite Znth_pos_cons by lia).
      rewrite Znth_0_cons.
      change (Z.pow_pos 2 64) with (2 ^ 64).
      (* return (t'3 >> (offset & 0x3F)) & (0xFFFFFFFF >> (32 - count)) *)
      forward.
      {
        entailer!.
        assert (Hland : Z.land offset 63 = offset mod 64).
        {
          change 63 with (Z.ones 6).
          rewrite Z.land_ones by lia.
          change (2 ^ 6) with 64.
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

    + (* limb 1 *)
      unfold scalar_to_val.
      repeat (rewrite Znth_pos_cons by lia).
      rewrite Znth_0_cons.
      change (Z.pow_pos 2 64) with (2 ^ 64).
      (* return (t'3 >> (offset & 0x3F)) & (0xFFFFFFFF >> (32 - count)) *)
      forward.
      {
        entailer!.
        assert (Hland : Z.land offset 63 = offset mod 64).
        {
          change 63 with (Z.ones 6).
          rewrite Z.land_ones by lia.
          change (2 ^ 6) with 64.
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

    + (* limb 2 *)
      unfold scalar_to_val.
      repeat (rewrite Znth_pos_cons by lia).
      rewrite Znth_0_cons.
      change (Z.pow_pos 2 128) with (2 ^ 128).
      (* return (t'3 >> (offset & 0x3F)) & (0xFFFFFFFF >> (32 - count)) *)
      forward.
      {
        entailer!.
        assert (Hland : Z.land offset 63 = offset mod 64).
        {
          change 63 with (Z.ones 6).
          rewrite Z.land_ones by lia.
          change (2 ^ 6) with 64.
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

    + (* limb 3 *)
      unfold scalar_to_val.
      repeat (rewrite Znth_pos_cons by lia).
      rewrite Znth_0_cons.
      change (Z.pow_pos 2 192) with (2 ^ 192).
      (* return (t'3 >> (offset & 0x3F)) & (0xFFFFFFFF >> (32 - count)) *)
      forward.
      {
        entailer!.
        assert (Hland : Z.land offset 63 = offset mod 64).
        {
          change 63 with (Z.ones 6).
          rewrite Z.land_ones by lia.
          change (2 ^ 6) with 64.
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

  - (* ===== Straddle branch: combine two adjacent limbs ===== *)
    (* the C test rewrites to a pure-Z disequation of limb indices *)
    assert (Hadd : Int.sub (Int.add (Int.repr offset) (Int.repr count)) (Int.repr 1)
                   = Int.repr (offset + count - 1))
      by (rewrite add_repr, sub_repr; reflexivity).
    rewrite Hadd in H.
    rewrite (Hshru (offset + count - 1)) in H by rep_lia.
    rewrite (Hshru offset) in H by rep_lia.

    assert (Hdivne : (offset + count - 1) / 64 <> offset / 64).
    { intro Hc. apply H. rewrite Hc. reflexivity. }

    (* the window straddles a limb boundary: [offset mod 64 + count > 64] *)
    assert (Hstraddle : offset mod 64 + count > 64).
    {
      pose proof (Z.div_mod offset 64 ltac:(lia)) as Hdm.
      pose proof (Z.div_mod (offset + count - 1) 64 ltac:(lia)) as Hdm2.
      pose proof (Z.mod_pos_bound offset 64 ltac:(lia)) as Hmb.
      pose proof (Z.mod_pos_bound (offset + count - 1) 64 ltac:(lia)) as Hmb2.
      pose proof (Z.div_le_mono offset (offset + count - 1) 64 ltac:(lia) ltac:(lia)) as Hle.
      nia.
    }

    (* so [offset < 192], giving [k = offset/64 <= 2] and [k+1 < 4] in bounds *)
    assert (Hk0 : 0 <= offset / 64) by (apply Z.div_pos; lia).
    assert (Hk2 : offset / 64 <= 2).
    {
      pose proof (Z.div_mod offset 64 ltac:(lia)) as Hdm.
      pose proof (Z.mod_pos_bound offset 64 ltac:(lia)) as Hmb.
      nia.
    }

    assert (Hshru_u : Int.unsigned (Int.shru (Int.repr offset) (Int.repr 6)) = offset / 64).
    {
      rewrite Int.shru_div_two_p.
      rewrite (Int.unsigned_repr offset) by rep_lia.
      rewrite (Int.unsigned_repr 6) by rep_lia.
      rewrite two_p_correct.
      change (two_power_pos 6) with 64.
      apply Int.unsigned_repr.
      rep_lia.
    }
    assert (Hshru_u1 : Int.unsigned
              (Int.add (Int.shru (Int.repr offset) (Int.repr 6)) (Int.repr 1))
            = offset / 64 + 1).
    {
      unfold Int.add.
      rewrite Hshru_u.
      rewrite (Int.unsigned_repr 1) by rep_lia.
      apply Int.unsigned_repr.
      rep_lia.
    }

    (* _t'2 = a->d[offset >> 6] *)
    forward.
    {
      rewrite Hshru_u.
      entailer!.
      replace (let (q, _) := Z.div_eucl offset 64 in q) with (offset / 64) by reflexivity.
      assert (Hc : offset / 64 = 0 \/ offset / 64 = 1 \/ offset / 64 = 2) by lia.
      destruct Hc as [E | [E | E]]; rewrite E; simpl Znth; exact I.
    }
    (* _t'3 = a->d[(offset >> 6) + 1] (the [k+1 < 4] in-bounds side is
       auto-discharged from [Hk2]; only the [tc_val] obligation remains) *)
    forward.
    {
      rewrite Hshru_u1.
      entailer!.
      replace (let (q, _) := Z.div_eucl offset 64 in q) with (offset / 64) by reflexivity.
      assert (Hc : offset / 64 = 0 \/ offset / 64 = 1 \/ offset / 64 = 2) by lia.
      destruct Hc as [E | [E | E]]; rewrite E; simpl Znth; exact I.
    }

    rewrite Hshru_u.
    rewrite Hshru_u1.

    (* the loaded limbs are [d[k] = (a/2^(64k)) mod 2^64] and
       [d[k+1] = (a/2^(64(k+1))) mod 2^64]; reduce the symbolic subscript to a
       literal so each [Znth] becomes a concrete [Vlong]. *)
    assert (Hidx : offset / 64 = 0 \/ offset / 64 = 1 \/ offset / 64 = 2) by lia.
    destruct Hidx as [E | [E | E]]; rewrite E in *.

    + (* limb 0 / limb 1 *)
      unfold scalar_to_val.
      change (0 + 1) with 1.
      rewrite Znth_0_cons.
      rewrite (Znth_pos_cons 1) by lia.
      change (1 - 1) with 0.
      rewrite Znth_0_cons.
      (* return ((t'2 >> s) | (t'3 << (64 - s))) & (0xFFFFFFFF >> (32 - count)) *)
      forward.
      {
        entailer!.
        assert (Hland : Z.land offset 63 = offset mod 64).
        { change 63 with (Z.ones 6).
          rewrite Z.land_ones by lia.
          change (2 ^ 6) with 64.
          reflexivity. }
        rewrite Hland.
        assert (Hmod : 0 <= offset mod 64 < 64) by (apply Z.mod_pos_bound; lia).
        rewrite !Int.unsigned_repr by rep_lia.
        change (Int.unsigned Int64.iwordsize') with 64.
        change (Int.unsigned Int.iwordsize) with 32.
        lia.
      }
      entailer!.
      f_equal.
      eapply (get_bits_var_comb a offset count _ _ 0); try lia.
      { (* side goal: 0 <= a *)
        exact (proj1 (scalar_range a)). }
      { (* side goal: dlo = (a / 2 ^ (64 * 0)) mod 2 ^ 64 *)
        change (64 * 0) with 0.
        rewrite Z.pow_0_r, Z.div_1_r.
        reflexivity. }
      { (* side goal: dhi = (a / 2 ^ (64 * (0 + 1))) mod 2 ^ 64 *)
        change (64 * (0 + 1)) with 64.
        reflexivity. }

    + (* limb 1 / limb 2 *)
      unfold scalar_to_val.
      change (1 + 1) with 2.
      rewrite (Znth_pos_cons 1) by lia.
      change (1 - 1) with 0.
      rewrite Znth_0_cons.
      rewrite (Znth_pos_cons 2) by lia.
      change (2 - 1) with 1.
      rewrite (Znth_pos_cons 1) by lia.
      change (1 - 1) with 0.
      rewrite Znth_0_cons.
      (* return ((t'2 >> s) | (t'3 << (64 - s))) & (0xFFFFFFFF >> (32 - count)) *)
      forward.
      {
        entailer!.
        assert (Hland : Z.land offset 63 = offset mod 64).
        { change 63 with (Z.ones 6).
          rewrite Z.land_ones by lia.
          change (2 ^ 6) with 64.
          reflexivity. }
        rewrite Hland.
        assert (Hmod : 0 <= offset mod 64 < 64) by (apply Z.mod_pos_bound; lia).
        rewrite !Int.unsigned_repr by rep_lia.
        change (Int.unsigned Int64.iwordsize') with 64.
        change (Int.unsigned Int.iwordsize) with 32.
        lia.
      }
      entailer!.
      f_equal.
      eapply (get_bits_var_comb a offset count _ _ 1); try lia.
      { (* side goal: 0 <= a *)
        exact (proj1 (scalar_range a)). }
      { (* side goal: dlo = (a / 2 ^ (64 * 1)) mod 2 ^ 64 *)
        change (64 * 1) with 64.
        reflexivity. }
      { (* side goal: dhi = (a / 2 ^ (64 * (1 + 1))) mod 2 ^ 64 *)
        change (64 * (1 + 1)) with 128.
        reflexivity. }

    + (* limb 2 / limb 3 *)
      unfold scalar_to_val.
      change (2 + 1) with 3.
      rewrite (Znth_pos_cons 2) by lia.
      change (2 - 1) with 1.
      rewrite (Znth_pos_cons 1) by lia.
      change (1 - 1) with 0.
      rewrite Znth_0_cons.
      rewrite (Znth_pos_cons 3) by lia.
      change (3 - 1) with 2.
      rewrite (Znth_pos_cons 2) by lia.
      change (2 - 1) with 1.
      rewrite (Znth_pos_cons 1) by lia.
      change (1 - 1) with 0.
      rewrite Znth_0_cons.
      (* return ((t'2 >> s) | (t'3 << (64 - s))) & (0xFFFFFFFF >> (32 - count)) *)
      forward.
      {
        entailer!.
        assert (Hland : Z.land offset 63 = offset mod 64).
        { change 63 with (Z.ones 6).
          rewrite Z.land_ones by lia.
          change (2 ^ 6) with 64.
          reflexivity. }
        rewrite Hland.
        assert (Hmod : 0 <= offset mod 64 < 64) by (apply Z.mod_pos_bound; lia).
        rewrite !Int.unsigned_repr by rep_lia.
        change (Int.unsigned Int64.iwordsize') with 64.
        change (Int.unsigned Int.iwordsize) with 32.
        lia.
      }
      entailer!.
      f_equal.
      eapply (get_bits_var_comb a offset count _ _ 2); try lia.
      { (* side goal: 0 <= a *)
        exact (proj1 (scalar_range a)). }
      { (* side goal: dlo = (a / 2 ^ (64 * 2)) mod 2 ^ 64 *)
        change (64 * 2) with 128.
        reflexivity. }
      { (* side goal: dhi = (a / 2 ^ (64 * (2 + 1))) mod 2 ^ 64 *)
        change (64 * (2 + 1)) with 192.
        reflexivity. }
Qed.
