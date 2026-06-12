(** * Verif_scalar_set_b32: Proof of body_secp256k1_scalar_set_b32 *)
(** Copyright (C) 2026 remix7531
    SPDX-License-Identifier: MIT *)

Require Import secp256k1.vst.base.
Require Import secp256k1.contract.helper.structs_scalar.
Require Import secp256k1.contract.helper.notations.
Require Import secp256k1.contract.gprog.scalar.
Require Import secp256k1.theory.bytes.
Require Import secp256k1.contract.util.
Require Import secp256k1.tactics.core.
Require Import secp256k1.tactics.int128.
Require Import secp256k1.tactics.scalar.

(* ================================================================= *)
(** ** Hoisted pure cores -- [theory.bytes]. *)

(** The big-endian recombination lemmas ([be_fold_left_acc],
    [Z_of_be_bytes_app], [Z_of_be_bytes_bound]) live in [theory.bytes],
    next to the [Z_of_be_bytes] definition they describe. *)

(* ================================================================= *)
(** ** secp256k1_scalar_set_b32 -- [r = bytes mod N], overflow flag set. *)

(** [secp256k1_scalar_set_b32] parses a 32-byte big-endian array into the
    four 64-bit limbs of [r] (via four [read_be64] reads of disjoint
    8-byte windows), then reduces the 256-bit value mod [N] and stores the
    overflow flag.  The proof splits the [bytes32_at] buffer into four
    8-byte [data_at]s at byte offsets 0/8/16/24, feeds each to the matching
    [read_be64] call, recombines [Z_of_be_bytes] over the chunks
    ([Z_of_be_bytes_app]), repackages the four stored limbs as a [UInt256]
    [r_u] whose value is [Z_of_be_bytes bs], and finishes with the
    [check_overflow]/[reduce] tail (cf. [scalar_add]). *)
Lemma body_secp256k1_scalar_set_b32:
  semax_body Vprog Gprog
    f_secp256k1_scalar_set_b32 spec_secp256k1_scalar_set_b32.
Proof.
  start_function.
  rename H into Hlen.
  rename H0 into Hrange.

  (* ===== Stage 1: split the 32-byte buffer into four 8-byte chunks ===== *)
  assert_PROP (field_compatible (tarray tuchar 32) [] b32_ptr) as Hfc by entailer!.
  set (c0 := sublist 0 8 bs).
  set (c1 := sublist 8 16 bs).
  set (c2 := sublist 16 24 bs).
  set (c3 := sublist 24 32 bs).
  assert (Hsplit : bs = c0 ++ c1 ++ c2 ++ c3).
  { subst c0 c1 c2 c3.
    rewrite <- (sublist_same 0 32 bs) at 1 by lia.
    rewrite (sublist_split 0 8 32 bs) by lia.
    rewrite (sublist_split 8 16 32 bs) by lia.
    rewrite (sublist_split 16 24 32 bs) by lia.
    reflexivity. }
  assert (Hl0 : Zlength c0 = 8) by (subst c0; rewrite Zlength_sublist; lia).
  assert (Hl1 : Zlength c1 = 8) by (subst c1; rewrite Zlength_sublist; lia).
  assert (Hl2 : Zlength c2 = 8) by (subst c2; rewrite Zlength_sublist; lia).
  assert (Hl3 : Zlength c3 = 8) by (subst c3; rewrite Zlength_sublist; lia).
  assert (Hr0 : Forall (fun b => 0 <= b < 256) c0) by (subst c0; apply Forall_sublist; auto).
  assert (Hr1 : Forall (fun b => 0 <= b < 256) c1) by (subst c1; apply Forall_sublist; auto).
  assert (Hr2 : Forall (fun b => 0 <= b < 256) c2) by (subst c2; apply Forall_sublist; auto).
  assert (Hr3 : Forall (fun b => 0 <= b < 256) c3) by (subst c3; apply Forall_sublist; auto).

  (* Rewrite [bytes32_at] as the four-chunk append, then peel each 8-byte
     chunk off the front, normalizing each chunk pointer to [offset_val]. *)
  rewrite Hsplit.
  unfold bytes_to_val.
  rewrite !map_app.
  rewrite (split2_data_at_Tarray_app 8 32 sh_b tuchar
    (map (fun b : Z => Vint (Int.repr b)) c0)
    (map (fun b : Z => Vint (Int.repr b)) c1 ++
     map (fun b : Z => Vint (Int.repr b)) c2 ++
     map (fun b : Z => Vint (Int.repr b)) c3) b32_ptr)
    by (rewrite ?Zlength_app, ?Zlength_map; lia).
  assert_PROP (field_address0 (tarray tuchar 32) (SUB 8) b32_ptr = offset_val 8 b32_ptr) as Hp1.
  { entailer!.
    rewrite arr_field_address0 by (auto; lia).
    reflexivity. }
  rewrite Hp1.
  assert_PROP (field_compatible (tarray tuchar (32 - 8)) [] (offset_val 8 b32_ptr)) as Hfc2 by entailer!.
  rewrite (split2_data_at_Tarray_app 8 (32 - 8) sh_b tuchar
    (map (fun b : Z => Vint (Int.repr b)) c1)
    (map (fun b : Z => Vint (Int.repr b)) c2 ++
     map (fun b : Z => Vint (Int.repr b)) c3) (offset_val 8 b32_ptr))
    by (rewrite ?Zlength_app, ?Zlength_map; lia).
  assert (Hp2 : field_address0 (tarray tuchar (32 - 8)) (SUB 8) (offset_val 8 b32_ptr) = offset_val 16 b32_ptr).
  { rewrite arr_field_address0 by (auto; lia).
    rewrite offset_offset_val.
    reflexivity. }
  rewrite Hp2.
  assert_PROP (field_compatible (tarray tuchar (32 - 8 - 8)) [] (offset_val 16 b32_ptr)) as Hfc3 by entailer!.
  rewrite (split2_data_at_Tarray_app 8 (32 - 8 - 8) sh_b tuchar
    (map (fun b : Z => Vint (Int.repr b)) c2)
    (map (fun b : Z => Vint (Int.repr b)) c3) (offset_val 16 b32_ptr))
    by (rewrite ?Zlength_app, ?Zlength_map; lia).
  assert (Hp3 : field_address0 (tarray tuchar (32 - 8 - 8)) (SUB 8) (offset_val 16 b32_ptr) = offset_val 24 b32_ptr).
  { rewrite arr_field_address0 by (auto; lia).
    rewrite offset_offset_val.
    reflexivity. }
  rewrite Hp3.
  change (32 - 8 - 8 - 8) with 8.

  (* ===== Stage 2: the four big-endian reads (most-significant chunk last) ===== *)

  (* r->d[0] = read_be64(&b32[24]): low limb = last 8 bytes *)
  forward_call (offset_val 24 b32_ptr, c3, sh_b).
  (* match the callee precondition's [bytes_to_val c3] against the c3 chunk
     [data_at] just peeled off; the later three reads reuse this SEP layout *)
  cancel.
  forward.

  (* r->d[1] = read_be64(&b32[16]) *)
  forward_call (offset_val 16 b32_ptr, c2, sh_b).
  forward.

  (* r->d[2] = read_be64(&b32[8]) *)
  forward_call (offset_val 8 b32_ptr, c1, sh_b).
  forward.

  (* r->d[3] = read_be64(&b32[0]): high limb = first 8 bytes *)
  forward_call (b32_ptr, c0, sh_b).
  forward.

  (* ===== Stage 3: the stored limbs form the 256-bit value [Z_of_be_bytes bs] ===== *)

  (* Per-chunk bounds: each 8-byte window decodes into [[0, 2^64)]. *)
  assert (Hn0 : length c0 = 8%nat) by (apply Nat2Z.inj; rewrite <- Zlength_correct; lia).
  assert (Hn1 : length c1 = 8%nat) by (apply Nat2Z.inj; rewrite <- Zlength_correct; lia).
  assert (Hn2 : length c2 = 8%nat) by (apply Nat2Z.inj; rewrite <- Zlength_correct; lia).
  assert (Hn3 : length c3 = 8%nat) by (apply Nat2Z.inj; rewrite <- Zlength_correct; lia).
  assert (Hd0b : 0 <= Z_of_be_bytes c3 < 2^64).
  { pose proof (Z_of_be_bytes_bound c3 Hr3) as Hb.
    rewrite Hn3 in Hb.
    simpl Z.of_nat in Hb.
    change (256^8) with (2^64) in Hb.
    lia. }
  assert (Hd1b : 0 <= Z_of_be_bytes c2 < 2^64).
  { pose proof (Z_of_be_bytes_bound c2 Hr2) as Hb.
    rewrite Hn2 in Hb.
    simpl Z.of_nat in Hb.
    change (256^8) with (2^64) in Hb.
    lia. }
  assert (Hd2b : 0 <= Z_of_be_bytes c1 < 2^64).
  { pose proof (Z_of_be_bytes_bound c1 Hr1) as Hb.
    rewrite Hn1 in Hb.
    simpl Z.of_nat in Hb.
    change (256^8) with (2^64) in Hb.
    lia. }
  assert (Hd3b : 0 <= Z_of_be_bytes c0 < 2^64).
  { pose proof (Z_of_be_bytes_bound c0 Hr0) as Hb.
    rewrite Hn0 in Hb.
    simpl Z.of_nat in Hb.
    change (256^8) with (2^64) in Hb.
    lia. }

  (* The 32-byte value recombines from the four big-endian chunks. *)
  assert (Hv_eq : Z_of_be_bytes bs =
    Z_of_be_bytes c3 + Z_of_be_bytes c2 * 2^64
    + Z_of_be_bytes c1 * 2^128 + Z_of_be_bytes c0 * 2^192).
  { rewrite Hsplit.
    rewrite !Z_of_be_bytes_app.
    rewrite !length_app.
    rewrite Hn1, Hn2, Hn3.
    simpl Z.of_nat.
    change (256 ^ 8) with (2^64).
    change (256 ^ (8 + (8 + 8))) with (2^192).
    change (256 ^ (8 + 8)) with (2^128).
    ring. }
  assert (Hvrange : 0 <= Z_of_be_bytes bs < 2^256).
  { rewrite Hv_eq.
    change (2^256) with (2^64 * 2^64 * 2^64 * 2^64).
    nia. }

  (* Package the 256-bit value as a [UInt256] [r_u]. *)
  pose (r_u := mkUInt256 (Z_of_be_bytes bs) Hvrange).
  assert (Hru_val : u256_val r_u = Z_of_be_bytes bs) by reflexivity.

  (* Each stored limb is the corresponding limb of [r_u]. *)
  assert (Heval : Z_of_be_bytes bs =
    eval4 (2^64) (Z_of_be_bytes c3) (Z_of_be_bytes c2) (Z_of_be_bytes c1) (Z_of_be_bytes c0)).
  { unfold eval4.
    rewrite Hv_eq.
    change ((2^64)^2) with (2^128).
    change ((2^64)^3) with (2^192).
    ring. }
  pose proof (limbs_eval4 (2^64) (Z_of_be_bytes c3) (Z_of_be_bytes c2) (Z_of_be_bytes c1) (Z_of_be_bytes c0)
    ltac:(lia) Hd0b Hd1b Hd2b Hd3b) as [Hm0 [Hm1 [Hm2 Hm3]]].
  unfold limb in Hm0, Hm1, Hm2, Hm3.
  simpl Z.of_nat in Hm0, Hm1, Hm2, Hm3.
  rewrite Z.pow_0_r, Z.div_1_r, Z.pow_1_r in *.
  rewrite <- Heval in Hm0, Hm1, Hm2, Hm3.

  (* The four stored limbs are exactly [uint256_to_val r_u]; this lets
     [forward_call] read the scalar struct as [u256_at r_ptr r_u]. *)
  assert (Hbridge :
    (upd_Znth 3
      (upd_Znth 2
        (upd_Znth 1
          (upd_Znth 0 (default_val t_secp256k1_scalar)
            (Vlong (Int64.repr (Z_of_be_bytes c3))))
          (Vlong (Int64.repr (Z_of_be_bytes c2))))
        (Vlong (Int64.repr (Z_of_be_bytes c1))))
      (Vlong (Int64.repr (Z_of_be_bytes c0))))
    = uint256_to_val r_u).
  { unfold uint256_to_val.
    simpl u256_val.
    rewrite Hm0, Hm1.
    change (2^128) with ((2^64)^2).
    change (2^192) with ((2^64)^3).
    rewrite Hm2, Hm3.
    unfold default_val.
    simpl.
    reflexivity. }

  (* ===== Stage 4: check_overflow + reduce ===== *)

  (* _t'5 = check_overflow(r): 1 iff the value is >= N *)
  forward_call (r_ptr, r_u, sh_r).

  (* _t'6 = reduce(r, _t'5): conditionally subtract N *)
  forward_call (r_ptr, r_u, (if Z_lt_dec (u256_val r_u) secp256k1_N then 0 else 1), sh_r).
  { destruct (Z_lt_dec (u256_val r_u) secp256k1_N); lia. }
  Intros vret.
  rename H into Hvret.

  (* over = _t'6 *)
  forward.

  (* ===== Stage 5: the overflow store (overflow != NULL by spec) ===== *)
  assert_PROP (ovf_ptr <> nullval) as Hovf_nn by entailer!.
  forward_if.

  (* then-branch: *overflow = over *)
  - forward.

    (* The reduced value is the scalar [Z_of_be_bytes bs mod N]. *)
    assert (HNbnd : 0 < secp256k1_N < 2^256) by (unfold secp256k1_N; lia).
    assert (Hvret_modN : u256_val vret = Z_of_be_bytes bs mod secp256k1_N).
    { rewrite Hvret, Hru_val.
      destruct (Z_lt_dec (Z_of_be_bytes bs) secp256k1_N) as [Hlt|Hge].
      - (* no overflow: value already < N *)
        rewrite Z.mul_0_l, Z.add_0_r.
        rewrite (Z.mod_small (Z_of_be_bytes bs) (2^256)) by lia.
        rewrite (Z.mod_small (Z_of_be_bytes bs) secp256k1_N) by lia.
        reflexivity.
      - (* overflow: subtract N once (value in [N, 2^256) subset [N, 2N)) *)
        rewrite Z.mul_1_l.
        replace (Z_of_be_bytes bs + (2^256 - secp256k1_N))
          with ((Z_of_be_bytes bs - secp256k1_N) + 1 * 2^256) by ring.
        rewrite Z_mod_plus_full.
        rewrite (Z.mod_small (Z_of_be_bytes bs - secp256k1_N) (2^256)) by lia.
        symmetry.
        rewrite (Z.mod_eq (Z_of_be_bytes bs) secp256k1_N) by lia.
        assert (Z_of_be_bytes bs / secp256k1_N = 1)
          by (symmetry; apply Z.div_unique_pos with (r := Z_of_be_bytes bs - secp256k1_N);
              unfold secp256k1_N in *; lia).
        lia. }

    (* postcondition: r = reduce_256 r_u; rejoin the byte chunks *)
    Exists (reduce_256 r_u).
    entailer!.

    (* The stored overflow flag matches the spec's [if N <= v then 1 else 0]. *)
    replace (if Z_le_dec secp256k1_N (Z_of_be_bytes bs) then 1 else 0)
      with (if Z_lt_dec (Z_of_be_bytes bs) secp256k1_N then 0 else 1)
      by (destruct (Z_lt_dec (Z_of_be_bytes bs) secp256k1_N),
            (Z_le_dec secp256k1_N (Z_of_be_bytes bs)); lia).

    (* The reduced scalar in the struct is exactly [vret]. *)
    assert (Hscal : scalar_at sh_r r_ptr (reduce_256 r_u) = u256_at sh_r r_ptr vret).
    { f_equal.
      unfold scalar_to_val, uint256_to_val.
      simpl scalar_val.
      rewrite Hvret_modN.
      reflexivity. }
    rewrite Hscal.
    cancel.

    (* Recombine the four 8-byte chunks back into [bytes32_at]. *)
    rewrite Hsplit.
    unfold bytes_to_val.
    rewrite !map_app.
    rewrite (split2_data_at_Tarray_app 8 32 sh_b tuchar
      (map (fun b : Z => Vint (Int.repr b)) c0)
      (map (fun b : Z => Vint (Int.repr b)) c1 ++
       map (fun b : Z => Vint (Int.repr b)) c2 ++
       map (fun b : Z => Vint (Int.repr b)) c3) b32_ptr)
      by (rewrite ?Zlength_app, ?Zlength_map; lia).
    rewrite Hp1.
    rewrite (split2_data_at_Tarray_app 8 (32 - 8) sh_b tuchar
      (map (fun b : Z => Vint (Int.repr b)) c1)
      (map (fun b : Z => Vint (Int.repr b)) c2 ++
       map (fun b : Z => Vint (Int.repr b)) c3) (offset_val 8 b32_ptr))
      by (rewrite ?Zlength_app, ?Zlength_map; lia).
    rewrite Hp2.
    rewrite (split2_data_at_Tarray_app 8 (32 - 8 - 8) sh_b tuchar
      (map (fun b : Z => Vint (Int.repr b)) c2)
      (map (fun b : Z => Vint (Int.repr b)) c3) (offset_val 16 b32_ptr))
      by (rewrite ?Zlength_app, ?Zlength_map; lia).
    rewrite Hp3.
    change (32 - 8 - 8 - 8) with 8.
    cancel.

  (* else-branch: overflow == NULL contradicts the non-NULL spec. *)
  - contradiction.
Qed.
