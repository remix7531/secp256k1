(** * vst.helper.signed62: the [Signed62] little-endian limb representation +
    [make_modinfo] -- modinv-owned (kept under helper/ because it also bridges
    the scalar <-> signed62 converters) C-representation glue for the safegcd modular
    inverse. *)
(** Copyright (C) 2026 remix7531
    Ported from BlockstreamResearch/simplicity Coq/C/secp256k1/spec_modinv64.v
    (commit c1dddedd), Copyright (c) 2018 Blockstream, originally MIT.
    Upstream notice reproduced in proof/README.md.
    SPDX-License-Identifier: MIT *)

(** Hoisted out of [vst/modinv/contract.v] so the scalar <-> signed62 bridge specs
    and the public inverse funspecs can live in the scalar layer (which sits
    below [vst/modinv/contract.v]) without depending on the modinv contract.  This
    file carries NO funspecs; it depends only on the vst/theory layers plus the
    [structs_modinv] aliases (for the spatial notations at the bottom), so it is
    layering-sound below [vst/scalar/contract.v].

    Adapted for Rocq 9.0 / VST 2.16 against this repo's single extraction AST. *)

Require Import secp256k1.vst.base.
Require Import secp256k1.theory.integers.extra_math.
Require Import secp256k1.theory.modinv.construction.inverse.
Require Import secp256k1.vst.helper.structs_modinv.

(* The 62-bit limb algebra below is all [Z.shiftr] / [Z.pow] rewriting, and an
   unfolded [2 ^ 62] blows up [simpl] and the [lia] side goals.  STYLE bans an
   inline [Opaque] in verif/ only; this is a contract-layer file, and a bare
   (non-[#[global]]) [Opaque] does not survive a [Require] in Rocq 9, so this
   one stays local to this file and never reaches a body proof. *)
Opaque Z.shiftr Z.pow.

(* ================================================================= *)
(** ** Signed62 model -- [secp256k1_modinv64_signed62] little-endian limbs. *)

(** The functional model of the C [secp256k1_modinv64_signed62] number: a
    list of signed 62-bit limbs (stored as [int64]), little-endian, denoting
    [sum_i signed(l_i) * 2^(62*i)]. [signed]/[reprn] are the value<->limbs
    pair; [pad] bridges a limb list to the C array's [list val] (Vundef-padded
    to length 5). The helper lemmas establish the round-trip and the bit-level
    facts the body proofs lean on. *)
Module Signed62.

(** Limb-count bounds: a [n]-limb signed62 value lies in
    [[min_signed n, max_signed n]]. *)
Definition max_signed n : Z := 2^(n*62)-1.
Definition min_signed n : Z := -2^(n*62).

(** Denotation: fold a limb list into the integer it represents, each limb
    weighted by [2^62] (limbs are [Int64.signed], so the value is signed). *)
Fixpoint signed (l : list int64) : Z :=
match l with
| [] => 0
| (a :: l') => Int64.signed a + 2^62 * signed l'
end.

(** Limb decomposition: split [a] into [n] little-endian 62-bit limbs. The
    final ([1%nat]) limb keeps the full (signed) remainder; lower limbs carry
    [a mod 2^62] and recurse on [a >> 62]. Inverse of [signed] under bounds. *)
Fixpoint reprn (n : nat) (a : Z) : list int64 :=
match n with
| 0%nat => []
| 1%nat => [Int64.repr a]
| (S n0) => Int64.repr (a mod (2 ^ 62)) :: (reprn n0 (Z.shiftr a 62))
end.

(** [reprn n a] always has exactly [n] limbs. *)
Lemma reprn_length n : forall a, length (reprn n a) = n.
Proof.
  induction n.
  { (* base: reprn 0 a = [] *)
    reflexivity. }

  destruct n.
  { (* base: reprn 1 a = [Int64.repr a] *)
    reflexivity. }

  (* step: one limb peeled off the front, the rest by the IH *)
  intro a.
  simpl in *.
  rewrite IHn.
  reflexivity.
Qed.

(** The [Zlength] form of [reprn_length]. *)
Lemma reprn_Zlength n : forall a, Zlength (reprn n a) = Z.of_nat n.
Proof.
  intros a.
  rewrite Zlength_correct, Signed62.reprn_length.
  reflexivity.
Qed.

(** Top-limb peel: an [(S n)]-limb decomposition is the [n]-limb decomposition
    of the low [62*n] bits, with the high part appended as the last limb. *)
Lemma reprn_succ n a : reprn (S n) a =
  reprn n (a mod 2 ^ (62 * Z.of_nat n)) ++ [Int64.repr (Z.shiftr a (62 * Z.of_nat n))].
Proof.
  revert a.
  induction n.
  { (* base: reprn 1 a = [] ++ [Int64.repr a] *)
    intros a.
    reflexivity. }

  (* Setup: expose the head limb so the IH applies to the tail. *)
  intros a.
  pattern (S n).
  simpl (reprn (S _) a).
  cbn beta.

  (* Main: rewrite the tail with the IH and merge the two shifts. *)
  rewrite IHn, Z.shiftr_shiftr, Nat2Z.inj_succ, Z.mul_succ_r, Z.add_comm by lia.
  simpl.
  destruct n.
  { (* branch: n = 0 -- the tail is the single top limb *)
    reflexivity. }

  (* Closeout: [(a mod 2^(62*(n+1)+62)) >> 62 = (a >> 62) mod 2^(62*(n+1))]. *)
  rewrite Z.pow_add_r by lia.
  rewrite !(Z.shiftr_div_pow2 _ 62) by lia.
  rewrite <- Zmod_div_mod.
  { rewrite (Z.mul_comm _ (2^62)), Zaux.Zdiv_mod_mult by lia.
    reflexivity. }

  (* The three side conditions of [Zmod_div_mod]. *)
  { (* side: 0 < 2^62 *)
    lia. }
  { (* side: 0 < 2^(62*(n+1)) * 2^62 *)
    lia. }
  { (* side: 2^62 divides 2^(62*(n+1)) * 2^62 *)
    apply Z.divide_factor_r. }
Qed.

(** The last limb of a [reprn] is the high part [a >> 62*(n-1)]. *)
Lemma reprn_last : forall a n d, (1 <= n)%nat ->
  last (reprn n a) d = Int64.repr (Z.shiftr a (62 * (Z.of_nat n - 1))).
Proof.
  intros a n.
  revert a.
  induction n.
  { (* base: 1 <= 0 is absurd *)
    lia. }

  (* Setup: normalise the shift count [62 * (n+1 - 1)] to [62 * n]. *)
  intros a d Hn.
  rewrite Nat2Z.inj_succ.
  unfold Z.succ.
  replace (Z.of_nat n + 1 - 1) with (Z.of_nat n) by ring.

  (* Closeout: the peel puts the high part last, and [last_last] reads it. *)
  rewrite reprn_succ.
  apply last_last.
Qed.

(** Any non-top limb [i] is the normalized 62-bit slice [(a >> 62*i) mod 2^62]. *)
Lemma reprn_nth : forall a n i d, (0 <= i < n - 1)%nat ->
  nth i (reprn n a) d = Int64.repr ((Z.shiftr a (62 * (Z.of_nat i))) mod (2^62)).
Proof.
  intros a n.
  revert a.
  induction n.
  { (* base: 0 <= i < 0 - 1 is absurd *)
    intros.
    lia. }

  (* Setup: peel the top limb off; index [i] stays in the [n]-limb prefix. *)
  intros a i d Hi.
  rewrite reprn_succ.
  rewrite app_nth1 by (rewrite reprn_length; lia).
  destruct (Nat.lt_ge_cases i (n - 1)).

  - (* branch: i < n-1 -- a non-top limb of the prefix, handled by the IH *)
    rewrite IHn, !Z.shiftr_div_pow2, <- (Nat.sub_add i n), Nat2Z.inj_add,
            Z.mul_add_distr_l, Z.pow_add_r, Z.mul_comm, Zaux.Zdiv_mod_mult by lia.

    (* Closeout: peel the outer [mod 2^62] off the inner truncation. *)
    rewrite !Z.pow_mul_r by lia.
    rewrite <- Zmod_div_mod.
    { reflexivity. }

    (* The three side conditions of [Zmod_div_mod]. *)
    { (* side: 0 < 2^62 *)
      lia. }
    { (* side: 0 < (2^62)^(n-i) *)
      lia. }
    { (* side: 2^62 divides (2^62)^(n-i) *)
      apply Zpow_facts.Zpower_divide.
      lia. }

  - (* branch: n-1 <= i -- the slice is the last limb of the prefix *)
    set (l := (reprn n _)).
    replace i with (n - 1)%nat by lia.
    replace n with (length l) at 1 by apply reprn_length.
    unfold l.
    rewrite nth_last, reprn_last by lia.

    (* Closeout: the top limb of the prefix is the [62*(n-1)] slice of [a]. *)
    replace (62 * Z.of_nat n) with (62 * (Z.of_nat n - 1) + 62) by ring.
    rewrite Z.pow_add_r, !Z.shiftr_div_pow2, Zaux.Zdiv_mod_mult by lia.
    repeat f_equal.
    lia.
Qed.

(** The [Znth] form of [reprn_nth] for non-top limbs. *)
Lemma reprn_Znth : forall a n i, 0 <= i < Z.of_nat n - 1 ->
  Znth i (reprn n a) = Int64.repr ((Z.shiftr a (62 * i)) mod (2^62)).
Proof.
  intros a n i Hi.
  rewrite <- nth_Znth by (rewrite reprn_Zlength; lia).
  rewrite reprn_nth, Z2Nat.id by lia.
  reflexivity.
Qed.

(** Round-trip: [signed (reprn n a) = a] when [a] fits in [62*n + 1] signed
    bits. This is the key faithfulness lemma for the limb representation. *)
Lemma signed_reprn a n : (1 <= n)%nat -> -2 ^ (62 * Z.of_nat n + 1) <= a <= 2 ^ (62 * Z.of_nat n + 1) - 1 ->
 signed (reprn n a) = a.
Proof.
  revert a.
  induction n.
  { (* base: 1 <= 0 is absurd *)
    lia. }

  intros a _.
  rewrite Nat2Z.inj_succ, Z.mul_succ_r.
  destruct n.

  - (* branch: n+1 = 1 -- the single limb is [Int64.signed (Int64.repr a)] *)
    simpl.
    intros Ha.
    rewrite Int64.signed_repr.
    { lia. }
    { (* side: [a] is already in [Int64]'s signed range *)
      assumption. }

  - (* branch: n+1 >= 2 -- peel the low limb and recurse on [a >> 62] *)
    change (reprn _ a) with (Int64.repr (a mod (2 ^ 62)) :: (reprn (S n) (Z.shiftr a 62))).
    cbn [signed].
    rewrite !Z.pow_add_r in * by lia.
    intros Ha.

    (* The shifted tail still fits the IH's bound. *)
    assert (Hshr : - (2 ^ (62 * Z.of_nat (S n)) * 2 ^ 1) <= Z.shiftr a 62 <
                   2 ^ (62 * Z.of_nat (S n)) * 2 ^ 1)
      by (apply shiftr_bounds; lia).

    rewrite IHn by lia.
    rewrite Int64.signed_repr
      by (pose proof (Z.mod_pos_bound a (2 ^ 62) ltac:(lia)); rep_lia).

    (* Closeout: [a mod 2^62 + 2^62 * (a / 2^62) = a]. *)
    rewrite Z.shiftr_div_pow2, Z.add_comm by lia.
    symmetry.
    apply Z_div_mod_eq_full.
Qed.

(** Length reduction: when [a] fits in [n1] limbs, the C "shrink" step --
    sign-extend limb [n1-1] of the [n2]-limb representation by OR-ing in the
    sign bit, then truncate to [n1] limbs -- recovers exactly [reprn n1 a].
    This models the [f.v[len-2] |= (uint64_t)fn << 62; --len] step in the
    variable-length driver. *)
Lemma reprn_shrink a n1 n2 : (min_signed (Z.of_nat n1) <= a <= max_signed (Z.of_nat n1)) -> (1 <= n1 < n2)%nat ->
     (firstn n1
        (upd_Znth (Z.of_nat n1 - 1) (reprn n2 a)
           (Int64.or (Znth (Z.of_nat n1 - 1) (reprn n2 a))
              (Int64.repr (Z.shiftl (if 0 <=? a then 0 else -1) 62))))) =
     (reprn n1 a).
Proof.
  intros Ha Hn.

  (* Setup: extensionality -- the lengths agree, then compare limb by limb. *)
  apply (nth_eq_ext _ default).
  { rewrite length_firstn, <-ZtoNat_Zlength, Zlength_upd_Znth, ZtoNat_Zlength, !reprn_length.
    lia. }

  rewrite length_firstn, <-ZtoNat_Zlength, Zlength_upd_Znth, ZtoNat_Zlength, !reprn_length.
  replace (Init.Nat.min n1 n2) with n1 by lia.
  intros i Hi.
  rewrite nth_firstn by lia.
  destruct (Nat.eq_dec i (n1 - 1)) as [->|Hneq].

  - (* branch: i = n1-1 -- the sign-extended top limb *)
    rewrite nth_Znth'.
    replace (Z.of_nat (n1 - 1)) with (Z.of_nat n1 - 1) by lia.
    rewrite upd_Znth_same by (rewrite reprn_Zlength; lia).
    rewrite reprn_Znth by lia.
    symmetry.
    replace n1 with (length (reprn n1 a)) at 1 by (rewrite reprn_length; reflexivity).
    rewrite nth_last.
    rewrite reprn_last by lia.
    unfold min_signed, max_signed in Ha.

    (* Case split on the sign of [a], which picks the OR mask. *)
    elim Z.leb_spec.

    + (* branch: 0 <= a -- the OR is with 0, and the slice is already the value *)
      intros Ha0.
      rewrite Int64.or_zero.
      symmetry.
      f_equal.
      apply Z.mod_small.

      (* the high part of a nonnegative [n1]-limb value fits in 62 bits *)
      apply shiftr_bounds.
      rewrite <-Z.pow_add_r by lia.
      replace (62 * (Z.of_nat n1 - 1) + 62) with (Z.of_nat n1 * 62) by lia.
      lia.

    + (* branch: a < 0 -- OR-ing the sign bits in is an add of -2^62 *)
      intros Ha0.
      rewrite <- Int64.add_is_or.

      * (* main: the added -2^62 cancels against the [mod 2^62] *)
        rewrite add64_repr.
        f_equal.
        change (Z.shiftl (-1) 62) with (-2^62).
        rewrite <- (Z_mod_plus_full _ 1), Z.mod_small.
        { ring. }

        (* the [mod] is small because the high part sits in [-2^62, 0) *)
        cut (- (2 ^ 62) <= Z.shiftr a (62 * (Z.of_nat n1 - 1)) < 0).
        { lia. }

        apply shiftr_bounds.
        rewrite Z.mul_0_r.
        cut (-(2^62 * 2 ^ (62 * (Z.of_nat n1 - 1))) <= a < 0).
        { lia. }

        rewrite <-Z.pow_add_r by lia.
        replace (62 + 62 * (Z.of_nat n1 - 1)) with (Z.of_nat n1 * 62); lia.

      * (* side: the two operands share no set bit, so OR = ADD *)
        apply Int64.same_bits_eq.
        intros j Hj.
        rewrite Int64.bits_zero, and64_repr, Int64.testbit_repr by assumption.
        rewrite <- Z.land_ones, !Z.land_spec, Z.testbit_ones_nonneg, Z.shiftl_spec by lia.

        (* Case split on the bit position [j] against the 62-bit boundary. *)
        elim Z.ltb_spec.
        { (* branch: j < 62 -- the shifted sign bits are all clear *)
          intro.
          rewrite (Z.testbit_neg_r _ (j - 62)), !andb_false_r by lia.
          reflexivity. }
        { (* branch: 62 <= j -- the 62-bit mask is clear *)
          rewrite andb_false_r.
          reflexivity. }

  - (* branch: i < n1-1 -- a lower limb, untouched by the [upd_Znth] *)
    rewrite nth_Znth'.
    rewrite reprn_nth, Znth_upd_Znth_diff, reprn_Znth by lia.
    reflexivity.
Qed.

(* ----------------------------------------------------------------- *)
(** *** pad -- limb list to the C array's [list val]. *)

(** Bridge a limb list to the [list val] stored in the 5-element C [v[]]
    array: map [Vlong] over the limbs, then pad with [Vundef] up to length 5.
    Used in the [_var] specs where only the active prefix carries data. *)
Definition pad (l : list int64) : list val := map Vlong l ++ repeat Vundef (5 - length l).

(** In-range index: [pad] reflects the underlying limb as [Vlong]. *)
Lemma pad_nth i (l : list int64) : 0 <= i < Zlength l -> Znth i (pad l) = Vlong (Znth i l).
Proof.
  intros Hi.
  rewrite <- !nth_Znth.

  - (* main: the index lands inside the [map Vlong] prefix *)
    assert (Hin : (Z.to_nat i < length l)%nat)
      by (rewrite <- ZtoNat_Zlength, <- Z2Nat.inj_lt; lia).

    unfold pad.
    rewrite app_nth1 by (rewrite length_map; assumption).
    erewrite nth_indep by (rewrite length_map; assumption).
    apply map_nth.

  - (* side: [i] is in range for [l] *)
    assumption.

  - (* side: [i] is in range for [pad l], which is at least as long *)
    unfold pad.
    rewrite Zlength_app, Zlength_map.
    assert (Hlen := Zlength_nonneg (repeat Vundef (5 - Datatypes.length l))).
    lia.
Qed.

(** Past-the-data index: [pad] yields [Vundef] beyond the limb list. *)
Lemma pad_nth_undef i (l : list int64) : Zlength l <= i -> Znth i (pad l) = Vundef.
Proof.
  (* Setup: move the index to [nat] so [app_nth2] applies. *)
  intros Hi.
  pose (Hl := Zlength_nonneg l).
  rewrite <- (Z2Nat.id i), <- nth_Znth' by lia.
  rewrite Z2Nat.inj_le, ZtoNat_Zlength in Hi by lia.

  (* Closeout: the index falls in the [repeat Vundef] tail. *)
  unfold pad.
  rewrite app_nth2 by (rewrite length_map; lia).
  apply nth_repeat.
Qed.

(** [pad] always produces a length-5 [list val] (the C array size). *)
Lemma pad_length l : (length l <= 5)%nat -> length (pad l) = 5%nat.
Proof.
  intros Hl.
  unfold pad.
  rewrite length_app, length_map, repeat_length.
  lia.
Qed.

(** The [Zlength] form of [pad_length]. *)
Lemma pad_Zlength l : Zlength l <= 5 -> Zlength (pad l) = 5.
Proof.
  intros Hl.
  rewrite Zlength_correct in Hl.
  rewrite Zlength_correct.
  rewrite pad_length by lia.
  reflexivity.
Qed.

(** A full (length-5) limb list needs no padding: [pad l = map Vlong l]. *)
Lemma pad5 l : length l = 5%nat -> pad l = map Vlong l.
Proof.
  unfold pad.
  intros ->.
  cbn.
  rewrite <- app_nil_r.
  reflexivity.
Qed.

(** Updating an in-range slot commutes with [pad]: storing [Vlong a] at [i]
    into the padded array equals padding the limb list updated at [i]. *)
Lemma pad_upd_Znth a i l : 0 <= i < Zlength l -> upd_Znth i (pad l) (Vlong a) = pad (upd_Znth i l a).
Proof.
  intros Hi.
  unfold pad.
  rewrite upd_Znth_app1 by (rewrite Zlength_map; assumption).
  f_equal.

  - (* the mapped prefix: [upd_Znth] commutes with [map Vlong] *)
    apply upd_Znth_map.

  - (* the [Vundef] tail: [upd_Znth] preserves the length, so the padding matches *)
    rewrite <- (ZtoNat_Zlength (upd_Znth _ _ _)), Zlength_upd_Znth, ZtoNat_Zlength.
    reflexivity.
Qed.

(* ----------------------------------------------------------------- *)
(** *** pack_two -- the C [v[0] | ((uint64_t)v[1] << 62)] bottom word. *)

(** The bottom 64 bits of a signed62 number, packed the way
    [secp256k1_jacobi64_maybe_var] builds the two arguments it hands to
    [secp256k1_modinv64_posdivsteps_62_var]:
    [f.v[0] | ((uint64_t)f.v[1] << 62)].  Limb 1 is read with a ZERO default
    ([Znth]'s [Inhabitant int64] is [Int64.zero]), so a one-limb list packs to
    its only limb -- which is exactly what the C sees once [len] has dropped to
    1: the length reduction is gated on limb [len-1] being zero, and
    [update_fg_62_var len] never writes above limb [len-1], so [v[1]]
    physically holds 0 from then on. *)
Definition pack_two (l : list int64) : int64 :=
  Int64.or (Znth 0 l) (Int64.shl (Znth 1 l) (Int64.repr 62)).

(** [pack_two] reads limbs 0 and 1 only, so lists agreeing there pack alike. *)
Lemma pack_two_ext l1 l2 :
  Znth 0 l1 = Znth 0 l2 -> Znth 1 l1 = Znth 1 l2 -> pack_two l1 = pack_two l2.
Proof.
  unfold pack_two.
  intros -> ->.
  reflexivity.
Qed.

(** The [(uint64_t)0 << 62] the [len = 1] packing shifts in is [0]. *)
Lemma shl_zero_62 : Int64.shl Int64.zero (Int64.repr 62) = Int64.zero.
Proof.
  unfold Int64.shl.
  rewrite Int64.unsigned_zero, Z.shiftl_0_l.
  reflexivity.
Qed.

(** Bit-level shape of [lo | (hi << 62)]: bits [0..61] come from [lo] (which
    must carry nothing above bit 61) and bits [62..63] from [hi]. *)
Lemma or_shl_62_bits (lo hi : int64) (a : Z) :
  (forall j, 0 <= j < 62 -> Int64.testbit lo j = Z.testbit a j) ->
  (forall j, 62 <= j < 64 -> Int64.testbit lo j = false) ->
  (forall j, 0 <= j < 2 -> Int64.testbit hi j = Z.testbit a (j + 62)) ->
  Int64.or lo (Int64.shl hi (Int64.repr 62)) = Int64.repr a.
Proof.
  (* Setup: compare the two words bit by bit, with the shift count reduced. *)
  intros Hlow Hclear Htop.
  apply Int64.same_bits_eq.
  intros j Hj.
  rewrite Int64.bits_or, Int64.bits_shl, Int64.testbit_repr by assumption.
  change (Int64.unsigned (Int64.repr 62)) with 62.
  change Int64.zwordsize with 64 in Hj.
  destruct (zlt j 62) as [Hlt | Hge].
  { (* branch: j < 62 -- the shifted limb contributes nothing there *)
    rewrite orb_false_r.
    apply Hlow.
    lia. }

  (* branch: 62 <= j < 64 -- [lo] is clear there, so [hi] supplies the bit *)
  rewrite Hclear by lia.
  rewrite orb_false_l.
  rewrite (Htop (j - 62)) by lia.
  f_equal.
  lia.
Qed.

(** Limb 0 of a [reprn] carries bits [0..61] of the value, whichever branch
    [reprn] took: the [1]-limb branch stores the whole value, every longer one
    stores [a mod 2^62]. *)
Lemma reprn_head_bits n a j : (1 <= n)%nat -> 0 <= j < 62 ->
  Int64.testbit (Znth 0 (reprn n a)) j = Z.testbit a j.
Proof.
  intros Hn Hj.
  destruct n as [|[|m]].
  { (* base: 1 <= 0 is absurd *)
    lia. }
  { (* branch: n = 1 -- the single limb is the whole value *)
    change (reprn 1 a) with [Int64.repr a].
    rewrite Znth_0_cons.
    apply Int64.testbit_repr.
    change Int64.zwordsize with 64.
    lia. }

  (* branch: n >= 2 -- limb 0 is the low 62-bit slice, which keeps bits 0..61 *)
  change (reprn _ a) with (Int64.repr (a mod (2 ^ 62)) :: (reprn (S m) (Z.shiftr a 62))).
  rewrite Znth_0_cons.
  rewrite Int64.testbit_repr by (change Int64.zwordsize with 64; lia).
  apply Z.mod_pow2_bits_low.
  lia.
Qed.

(** Value law for [f.v[0] | ((uint64_t)f.v[1] << 62)]: the packed word is the
    bottom 64 bits of the value, at every limb count.  At [n = 1] limb 1 is out
    of range and reads as [Int64.zero], so the packing is limb 0 itself -- the
    [len = 1] case of the C, where [v[1]] holds a zero. *)
Lemma pack_two_reprn n a : (1 <= n)%nat -> pack_two (reprn n a) = Int64.repr a.
Proof.
  intros Hn.
  unfold pack_two.
  destruct n as [|[|m]].
  { (* base: 1 <= 0 is absurd *)
    lia. }
  { (* branch: n = 1 -- limb 1 reads as zero, so nothing is shifted in *)
    change (reprn 1 a) with [Int64.repr a].
    change (Znth 0 [Int64.repr a]) with (Int64.repr a).
    change (Znth 1 [Int64.repr a]) with Int64.zero.
    rewrite shl_zero_62.
    apply Int64.or_zero. }

  (* Setup: peel the head limb, so the C's two loads are limbs 0 and 1. *)
  change (reprn _ a) with (Int64.repr (a mod (2 ^ 62)) :: (reprn (S m) (Z.shiftr a 62))).
  rewrite Znth_0_cons, Znth_pos_cons by lia.
  replace (1 - 1) with 0 by lia.

  (* Main: bits 0..61 come from limb 0, bits 62..63 from limb 1. *)
  apply or_shl_62_bits.
  { (* limb 0 keeps bits 0..61 of the value *)
    intros j Hj.
    rewrite Int64.testbit_repr by (change Int64.zwordsize with 64; lia).
    apply Z.mod_pow2_bits_low.
    lia. }
  { (* limb 0 carries nothing above bit 61 *)
    intros j Hj.
    rewrite Int64.testbit_repr by (change Int64.zwordsize with 64; lia).
    apply Z.mod_pow2_bits_high.
    lia. }

  (* Closeout: bits 0..1 of limb 1 are bits 62..63 of the value. *)
  intros j Hj.
  rewrite reprn_head_bits by lia.
  apply Z.shiftr_spec.
  lia.
Qed.

(** Limbs stored above the [n] active ones do not change the packing, as long
    as the first of them holds the zero the C buffer physically has there (only
    the [n = 1] case reads it). *)
Lemma pack_two_app n a l : (1 <= n)%nat -> Znth 0 l = Int64.zero ->
  pack_two (reprn n a ++ l) = Int64.repr a.
Proof.
  intros Hn Hl.
  destruct n as [|[|m]].
  { (* base: 1 <= 0 is absurd *)
    lia. }
  { (* branch: n = 1 -- limb 1 is the first padding slot, which holds zero *)
    change (reprn 1 a ++ l) with (Int64.repr a :: l).
    unfold pack_two.
    rewrite Znth_0_cons, Znth_pos_cons by lia.
    replace (1 - 1) with 0 by lia.
    rewrite Hl, shl_zero_62.
    apply Int64.or_zero. }

  (* branch: n >= 2 -- both read limbs come from [reprn], the padding is above *)
  rewrite (pack_two_ext _ (reprn (S (S m)) a)).
  { apply pack_two_reprn.
    lia. }
  { apply Znth_app1.
    rewrite reprn_Zlength.
    lia. }
  { apply Znth_app1.
    rewrite reprn_Zlength.
    lia. }
Qed.

(** The zero-padded form -- the shape the driver's [f] / [g] buffers hold once
    [len] has shrunk: [n] active limbs followed by zeros (incl. the [n = 1]
    padded case, where the packed word is limb 0 alone). *)
Lemma pack_two_reprn_zeros n k a : (1 <= n)%nat ->
  pack_two (reprn n a ++ repeat Int64.zero k) = Int64.repr a.
Proof.
  intros Hn.
  apply pack_two_app.
  { (* side: the active limb count *)
    assumption. }

  (* side: slot 0 of the padding is zero, whether or not the padding is empty *)
  destruct k.
  { apply Znth_nil. }
  { apply Znth_0_cons. }
Qed.

(** The [Int64.unsigned] form of [pack_two_reprn]: the packed word denotes the
    bottom 64 bits of the value. *)
Lemma pack_two_reprn_unsigned n a : (1 <= n)%nat ->
  Int64.unsigned (pack_two (reprn n a)) = a mod 2 ^ 64.
Proof.
  intros Hn.
  rewrite pack_two_reprn by assumption.
  rewrite Int64.unsigned_repr_eq.
  reflexivity.
Qed.

(** When the value fits in a word -- in particular at [n = 1], where
    [0 <= a < 2^62] -- the packed word IS the value, leaving no range side
    condition at the call site. *)
Lemma pack_two_reprn_small n a : (1 <= n)%nat -> 0 <= a < 2 ^ 64 ->
  Int64.unsigned (pack_two (reprn n a)) = a.
Proof.
  intros Hn Ha.
  rewrite pack_two_reprn_unsigned by assumption.
  apply Z.mod_small.
  assumption.
Qed.

(** The [pad] form: the two [val]s the C loads out of a [signed62_at] /
    [signed62_var_at] buffer for [v[0]] / [v[1]], plus the word they pack to --
    so a caller never unfolds [pad].  [2 <= n] is required because [pad] stores
    [Vundef] in slot 1 of a one-limb list, whereas the C buffer holds a zero
    there; [pack_two_reprn_zeros] is the law for that [len = 1] case. *)
Lemma pack_two_pad n a : (2 <= n <= 5)%nat ->
  Znth 0 (pad (reprn n a)) = Vlong (Znth 0 (reprn n a)) /\
  Znth 1 (pad (reprn n a)) = Vlong (Znth 1 (reprn n a)) /\
  Int64.or (Znth 0 (reprn n a)) (Int64.shl (Znth 1 (reprn n a)) (Int64.repr 62))
    = Int64.repr a.
Proof.
  intros Hn.
  split; [| split].
  { (* conjunct 0: the [v[0]] load *)
    apply pad_nth.
    rewrite reprn_Zlength.
    lia. }
  { (* conjunct 1: the [v[1]] load *)
    apply pad_nth.
    rewrite reprn_Zlength.
    lia. }

  (* conjunct 2: the two loads pack to the bottom 64 bits of the value *)
  apply (pack_two_reprn n a).
  lia.
Qed.

End Signed62.

(* ================================================================= *)
(** ** C-representation glue -- [make_modinfo]. *)

(** The [secp256k1_modinv64_modinfo] struct value for modulus [m]: its
    [.modulus] field is the 5-limb signed62 form of [m], and [.modulus_inv62]
    is [m^{-1} mod 2^62] (here as [mod_inv m (2^62)]). *)
Definition make_modinfo (m : Z) : (list val * val)%type :=
  (map Vlong (Signed62.reprn 5 m), Vlong (Int64.repr (mod_inv m (2^62)))).

(* ================================================================= *)
(** ** Spatial-predicate notations -- [signed62_at] / [modinfo_at]. *)

(** Shorthand for the modinv [data_at] resources, mirroring [vst/helper/
    notations].  Plain [Notation] -- definitionally equal to the underlying
    [data_at], so [forward_call], [cancel], and [entailer!] see straight through
    them and the driver bodies' explicit [field_at] handling is unaffected. Kept
    here beside [Signed62] / [make_modinfo] (the bridges they expand to), which
    live above the [vst/helper/notations] layer. *)

(** A [secp256k1_modinv64_signed62] buffer holding the 5-limb form of [x]. *)
Notation "'signed62_at' sh p x" :=
  (data_at sh t_secp256k1_modinv64_signed62 (map Vlong (Signed62.reprn 5 x)) p)
  (at level 20, sh at level 0, p at level 0, x at level 0).

(** A [secp256k1_modinv64_modinfo] buffer for modulus [m]. *)
Notation "'modinfo_at' sh p m" :=
  (data_at sh t_secp256k1_modinv64_modinfo (make_modinfo m) p)
  (at level 20, sh at level 0, p at level 0, m at level 0).
