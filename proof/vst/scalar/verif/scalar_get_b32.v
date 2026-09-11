(** * Verif_scalar_get_b32: Proof of body_secp256k1_scalar_get_b32 *)
(** Copyright (C) 2026 remix7531
    SPDX-License-Identifier: MIT *)

Require Import secp256k1.vst.base.
Require Import secp256k1.vst.helper.notations.
Require Import secp256k1.vst.gprog.
Require secp256k1.specification.
Import specification.Math.
Import specification.Math.integer_bytes.
Require Import secp256k1.vst.util.contract.
Require Import secp256k1.vst.tactics.core.
Require Import secp256k1.vst.tactics.int128.
Require Import secp256k1.vst.tactics.scalar.

(* ================================================================= *)
(** ** Byte-encoding split lemmas -- [be_bytes_of_Z] over a 32-byte limb split. *)

(** The big-endian encoding of [v] in [m + n] bytes splits into the high
    [m] bytes (of [v / 2^(8n)]) followed by the low [n] bytes (of
    [v mod 2^(8n)]).  [be_bytes_of_Z] peels the low byte at the tail each
    step, so the proof inducts on [n]. *)
Lemma be_bytes_of_Z_split : forall (m n : nat) (v : Z),
  be_bytes_of_Z v (m + n) =
  be_bytes_of_Z (v / 2 ^ (8 * Z.of_nat n)) m ++
  be_bytes_of_Z (v mod 2 ^ (8 * Z.of_nat n)) n.
Proof.
  induction n as [| n IHn]; intros v.
  - (* n = 0: the low part is empty, [v / 1 = v]. *)
    rewrite Nat.add_0_r.
    simpl (8 * Z.of_nat 0)%Z.
    rewrite Z.pow_0_r.
    rewrite Z.div_1_r.
    simpl (be_bytes_of_Z _ 0).
    rewrite app_nil_r.
    reflexivity.
  - (* n -> S n: peel one low byte and align the divisor/modulus. *)
    replace (m + S n)%nat with (S (m + n)) by lia.
    remember (2 ^ (8 * Z.of_nat n))%Z as P eqn:HP.
    assert (HPpos : 0 < P).
    { rewrite HP. apply Z.pow_pos_nonneg; lia. }
    assert (Hpow : (2 ^ (8 * Z.of_nat (S n)))%Z = 256 * P).
    {
      rewrite HP.
      rewrite Nat2Z.inj_succ.
      replace (8 * Z.succ (Z.of_nat n))%Z with (8 * Z.of_nat n + 8)%Z by lia.
      rewrite Z.pow_add_r by lia.
      change (2 ^ 8)%Z with 256%Z.
      lia.
    }
    rewrite Hpow.
    cbn [be_bytes_of_Z].
    rewrite IHn.
    rewrite (Z.div_div v 256 P) by lia.
    rewrite (Zaux.Zdiv_mod_mult v 256 P) by lia.
    rewrite (Z.mul_comm 256 P).
    rewrite (Zaux.Zmod_mod_mult v P 256) by lia.
    rewrite app_assoc.
    reflexivity.
Qed.

(** A 256-bit value's 32-byte big-endian encoding is the concatenation of
    its four 64-bit limbs' 8-byte encodings, most-significant limb first. *)
Lemma be_bytes_of_Z_32_limbs : forall v : Z,
  0 <= v < 2 ^ 256 ->
  be_bytes_of_Z v 32 =
  be_bytes_of_Z ((v / 2 ^ 192) mod 2 ^ 64) 8 ++
  be_bytes_of_Z ((v / 2 ^ 128) mod 2 ^ 64) 8 ++
  be_bytes_of_Z ((v / 2 ^ 64) mod 2 ^ 64) 8 ++
  be_bytes_of_Z (v mod 2 ^ 64) 8.
Proof.
  intros v Hv.
  (* Peel the most-significant 8-byte limb. *)
  change 32%nat with (8 + 24)%nat.
  rewrite (be_bytes_of_Z_split 8 24 v).
  change (2 ^ (8 * Z.of_nat 24))%Z with (2 ^ 192)%Z.
  assert (Hhi : (v / 2 ^ 192) mod 2 ^ 64 = v / 2 ^ 192).
  {
    apply Z.mod_small.
    split.
    - apply Z.div_pos; lia.
    - apply Z.div_lt_upper_bound; [lia |].
      change (2 ^ 64 * 2 ^ 192)%Z with (2 ^ 256)%Z.
      lia.
  }
  rewrite Hhi.
  f_equal.
  (* Peel the next limb out of the low 24 bytes. *)
  change 24%nat with (8 + 16)%nat.
  rewrite (be_bytes_of_Z_split 8 16 (v mod 2 ^ 192)).
  change (2 ^ (8 * Z.of_nat 16))%Z with (2 ^ 128)%Z.
  assert (Hp192 : (2 ^ 192 = 2 ^ 128 * 2 ^ 64)%Z) by reflexivity.
  rewrite Hp192.
  rewrite (Zaux.Zdiv_mod_mult v (2 ^ 128) (2 ^ 64)) by lia.
  rewrite (Z.mul_comm (2 ^ 128) (2 ^ 64)).
  rewrite (Zaux.Zmod_mod_mult v (2 ^ 64) (2 ^ 128)) by lia.
  f_equal.
  (* Peel the last two limbs out of the low 16 bytes. *)
  change 16%nat with (8 + 8)%nat.
  rewrite (be_bytes_of_Z_split 8 8 (v mod 2 ^ 128)).
  change (2 ^ (8 * Z.of_nat 8))%Z with (2 ^ 64)%Z.
  assert (Hp128 : (2 ^ 128 = 2 ^ 64 * 2 ^ 64)%Z) by reflexivity.
  rewrite Hp128.
  rewrite (Zaux.Zdiv_mod_mult v (2 ^ 64) (2 ^ 64)) by lia.
  rewrite (Zaux.Zmod_mod_mult v (2 ^ 64) (2 ^ 64)) by lia.
  reflexivity.
Qed.

(* ================================================================= *)
(** ** 32-byte buffer split/join -- [bytes32_split8] / [bytes32_join8]. *)

(** Split an uninitialized 32-byte [tuchar] buffer into four 8-byte
    chunks at offsets 0, 8, 16, 24. *)
Lemma bytes32_split8 : forall (sh : share) (p : val),
  field_compatible (tarray tuchar 32) [] p ->
  data_at_ sh (tarray tuchar 32) p =
  (data_at_ sh (tarray tuchar 8) p *
   data_at_ sh (tarray tuchar 8) (offset_val 8 p) *
   data_at_ sh (tarray tuchar 8) (offset_val 16 p) *
   data_at_ sh (tarray tuchar 8) (offset_val 24 p))%logic.
Proof.
  intros sh p Hfc.
  rewrite (split2_data_at__Tarray_tuchar sh 32 8 p) by (try lia; auto).
  rewrite (arr_field_address0 tuchar 32 p 8) by (auto; lia).
  simpl (sizeof tuchar * 8).
  assert (Hfc8tail : field_compatible (tarray tuchar (32 - 8)) [] (offset_val 8 p)).
  {
    pose proof (proj1 (field_compatible_Tarray_split tuchar 8 32 p ltac:(lia)) Hfc)
      as [_ Ht].
    rewrite (arr_field_address0 tuchar 32 p 8) in Ht by (auto; lia).
    simpl (sizeof tuchar * 8) in Ht.
    exact Ht.
  }
  rewrite (split2_data_at__Tarray_tuchar sh (32 - 8) 8 (offset_val 8 p))
    by (try lia; auto).
  rewrite (arr_field_address0 tuchar (32 - 8) (offset_val 8 p) 8) by (auto; lia).
  simpl (sizeof tuchar * 8).
  rewrite offset_offset_val.
  change (8 + 8)%Z with 16%Z.
  change (32 - 8 - 8)%Z with 16%Z.
  change (32 - 8)%Z with 24%Z in *.
  assert (Hfc16 : field_compatible (tarray tuchar 16) [] (offset_val 16 p)).
  {
    pose proof (proj1 (field_compatible_Tarray_split tuchar 8 24 (offset_val 8 p)
                         ltac:(lia)) Hfc8tail) as [_ Ht].
    rewrite (arr_field_address0 tuchar 24 (offset_val 8 p) 8) in Ht by (auto; lia).
    simpl (sizeof tuchar * 8) in Ht.
    rewrite offset_offset_val in Ht.
    change (8 + 8)%Z with 16%Z in Ht.
    exact Ht.
  }
  rewrite (split2_data_at__Tarray_tuchar sh 16 8 (offset_val 16 p))
    by (try lia; auto).
  rewrite (arr_field_address0 tuchar 16 (offset_val 16 p) 8) by (auto; lia).
  simpl (sizeof tuchar * 8).
  rewrite offset_offset_val.
  change (16 + 8)%Z with 24%Z.
  change (16 - 8)%Z with 8%Z.
  rewrite <- !sepcon_assoc.
  reflexivity.
Qed.

(** Join four filled 8-byte chunks (at offsets 0, 8, 16, 24) back into the
    32-byte buffer holding the concatenated bytes. *)
Lemma bytes32_join8 : forall (sh : share) (p : val) (b3 b2 b1 b0 : list Z),
  field_compatible (tarray tuchar 32) [] p ->
  Zlength b3 = 8 -> Zlength b2 = 8 -> Zlength b1 = 8 -> Zlength b0 = 8 ->
  data_at sh (tarray tuchar 8) (bytes_to_val b3) p *
  data_at sh (tarray tuchar 8) (bytes_to_val b2) (offset_val 8 p) *
  data_at sh (tarray tuchar 8) (bytes_to_val b1) (offset_val 16 p) *
  data_at sh (tarray tuchar 8) (bytes_to_val b0) (offset_val 24 p)
  |-- data_at sh (tarray tuchar 32) (bytes_to_val (b3 ++ b2 ++ b1 ++ b0)) p.
Proof.
  intros sh p b3 b2 b1 b0 Hfc H3 H2 H1 H0.
  unfold bytes_to_val.
  rewrite !map_app.
  (* field_compatible facts for the offset sub-arrays. *)
  assert (Hfc24 : field_compatible (tarray tuchar 24) [] (offset_val 8 p)).
  {
    pose proof (proj1 (field_compatible_Tarray_split tuchar 8 32 p ltac:(lia)) Hfc)
      as [_ Ht].
    rewrite (arr_field_address0 tuchar 32 p 8) in Ht by (auto; lia).
    simpl (sizeof tuchar * 8) in Ht.
    change (32 - 8)%Z with 24%Z in Ht.
    exact Ht.
  }
  assert (Hfc16 : field_compatible (tarray tuchar 16) [] (offset_val 16 p)).
  {
    pose proof (proj1 (field_compatible_Tarray_split tuchar 8 24 (offset_val 8 p)
                         ltac:(lia)) Hfc24) as [_ Ht].
    rewrite (arr_field_address0 tuchar 24 (offset_val 8 p) 8) in Ht by (auto; lia).
    simpl (sizeof tuchar * 8) in Ht.
    rewrite offset_offset_val in Ht.
    change (8 + 8)%Z with 16%Z in Ht.
    exact Ht.
  }
  (* Split the destination 32-array into the four 8-byte chunks. *)
  rewrite (split2_data_at_Tarray_app 8 32 sh tuchar
             (map (fun b : Z => Vint (Int.repr b)) b3)
             (map (fun b : Z => Vint (Int.repr b)) b2 ++
              map (fun b : Z => Vint (Int.repr b)) b1 ++
              map (fun b : Z => Vint (Int.repr b)) b0) p).
  2: list_solve.
  2: list_solve.
  rewrite (arr_field_address0 tuchar 32 p 8) by (auto; lia).
  simpl (sizeof tuchar * 8).
  change (32 - 8)%Z with 24%Z.
  rewrite (split2_data_at_Tarray_app 8 24 sh tuchar
             (map (fun b : Z => Vint (Int.repr b)) b2)
             (map (fun b : Z => Vint (Int.repr b)) b1 ++
              map (fun b : Z => Vint (Int.repr b)) b0) (offset_val 8 p)).
  2: list_solve.
  2: list_solve.
  rewrite (arr_field_address0 tuchar 24 (offset_val 8 p) 8) by (auto; lia).
  simpl (sizeof tuchar * 8).
  rewrite offset_offset_val.
  change (8 + 8)%Z with 16%Z.
  change (24 - 8)%Z with 16%Z.
  rewrite (split2_data_at_Tarray_app 8 16 sh tuchar
             (map (fun b : Z => Vint (Int.repr b)) b1)
             (map (fun b : Z => Vint (Int.repr b)) b0) (offset_val 16 p)).
  2: list_solve.
  2: list_solve.
  rewrite (arr_field_address0 tuchar 16 (offset_val 16 p) 8) by (auto; lia).
  simpl (sizeof tuchar * 8).
  rewrite offset_offset_val.
  change (16 + 8)%Z with 24%Z.
  cancel.
Qed.

(* ================================================================= *)
(** ** secp256k1_scalar_get_b32 -- [bin = a as 32 big-endian bytes]. *)

(** The C body loads the four limbs [a->d[3..0]] (most significant first)
    and stores each as 8 big-endian bytes via [write_be64] into [bin[0..24]].
    The proof splits the 32-byte buffer into four 8-byte chunks at offsets
    0/8/16/24 ([bytes32_split8]), feeds each [write_be64] call the chunk it
    fills, then rejoins the four filled chunks ([bytes32_join8]) and matches
    the encoding against [be_bytes_of_Z (scalar_val a) 32] via the limb split
    [be_bytes_of_Z_32_limbs]. *)
Lemma body_secp256k1_scalar_get_b32:
  semax_body Vprog Gprog
    f_secp256k1_scalar_get_b32 spec_secp256k1_scalar_get_b32.
Proof.
  start_function.

  (* The destination buffer is field-compatible; each limb is a 64-bit word. *)
  assert_PROP (field_compatible (tarray tuchar 32) [] bin_ptr) as Hfc by entailer!.
  assert (Hb3 : 0 <= (scalar_val a / 2 ^ 192) mod 2 ^ 64 < 2 ^ 64)
    by (apply Z.mod_pos_bound; lia).
  assert (Hb2 : 0 <= (scalar_val a / 2 ^ 128) mod 2 ^ 64 < 2 ^ 64)
    by (apply Z.mod_pos_bound; lia).
  assert (Hb1 : 0 <= (scalar_val a / 2 ^ 64) mod 2 ^ 64 < 2 ^ 64)
    by (apply Z.mod_pos_bound; lia).
  assert (Hb0 : 0 <= scalar_val a mod 2 ^ 64 < 2 ^ 64)
    by (apply Z.mod_pos_bound; lia).

  (* ===== Stage 1: split the buffer and run the four stores ===== *)

  rewrite (bytes32_split8 sh_bin bin_ptr Hfc).
  Intros.
  forward. (* _t'4 = a->d[3] *)
  (* write_be64(&bin[0], a->d[3]): high limb -> bytes 0..7 *)
  forward_call (bin_ptr,
                val_to_uint64 ((scalar_val a / 2 ^ 192) mod 2 ^ 64) Hb3, sh_bin).
  forward. (* _t'3 = a->d[2] *)
  (* write_be64(&bin[8], a->d[2]): bytes 8..15 *)
  forward_call (offset_val 8 bin_ptr,
                val_to_uint64 ((scalar_val a / 2 ^ 128) mod 2 ^ 64) Hb2, sh_bin).
  forward. (* _t'2 = a->d[1] *)
  (* write_be64(&bin[16], a->d[1]): bytes 16..23 *)
  forward_call (offset_val 16 bin_ptr,
                val_to_uint64 ((scalar_val a / 2 ^ 64) mod 2 ^ 64) Hb1, sh_bin).
  forward. (* _t'1 = a->d[0] *)
  (* write_be64(&bin[24], a->d[0]): low limb -> bytes 24..31 *)
  forward_call (offset_val 24 bin_ptr,
                val_to_uint64 (scalar_val a mod 2 ^ 64) Hb0, sh_bin).

  (* ===== Stage 2: rejoin the chunks into the big-endian encoding ===== *)

  cbn [u64_val val_to_uint64].
  entailer!.
  assert (Ha256 : 0 <= scalar_val a < 2 ^ 256).
  {
    pose proof (scalar_range a) as Hr.
    unfold secp256k1_N in Hr.
    lia.
  }
  rewrite (be_bytes_of_Z_32_limbs (scalar_val a) Ha256).
  sep_apply (bytes32_join8 sh_bin bin_ptr
               (be_bytes_of_Z ((scalar_val a / 2 ^ 192) mod 2 ^ 64) 8)
               (be_bytes_of_Z ((scalar_val a / 2 ^ 128) mod 2 ^ 64) 8)
               (be_bytes_of_Z ((scalar_val a / 2 ^ 64) mod 2 ^ 64) 8)
               (be_bytes_of_Z (scalar_val a mod 2 ^ 64) 8) Hfc);
    try apply be_bytes_of_Z_Zlength.
  cancel.
Qed.
