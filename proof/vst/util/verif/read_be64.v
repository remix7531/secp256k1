(** * Verif_util_read_be64: Proof of body_secp256k1_read_be64 *)
(** Copyright (C) 2026 remix7531
    SPDX-License-Identifier: MIT *)

Require Import secp256k1.vst.base.
Require secp256k1.specification.
Import specification.Math.
Import specification.Math.integer_bytes.
Require Import secp256k1.vst.helper.notations.
Require Import secp256k1.vst.gprog.
Require Import secp256k1.vst.util.contract.
Require Import secp256k1.vst.tactics.core.

(* ================================================================= *)
(** ** secp256k1_read_be64 -- [r = Z_of_be_bytes bs]. *)

(** [secp256k1_read_be64] decodes 8 big-endian bytes at [p] into a
    [uint64_t] by [(p[0] << 56) | ... | p[7]].  The proof loads the 8
    bytes, then matches the [Int64.or]/[Int64.shl] cascade against
    [Int64.repr (Z_of_be_bytes bs)].  The disjoint-or-is-add step uses
    the CompCert lemma [Int64.shifted_or_is_add] peeled bottom-up (the
    [Int64.or] tree is re-associated to the right first), each byte
    occupying a disjoint 8-bit window. *)
Lemma body_secp256k1_read_be64:
  semax_body Vprog Gprog
    f_secp256k1_read_be64 spec_secp256k1_read_be64.
Proof.
  start_function.

  rename H into Hlen.
  rename H0 into Hrange.

  (* ===== Stage 1: split [bs] into its 8 bytes ===== *)

  destruct bs as [|b0 bs]; [now (rewrite Zlength_nil in Hlen; lia)|].
  destruct bs as [|b1 bs]; [list_solve|].
  destruct bs as [|b2 bs]; [list_solve|].
  destruct bs as [|b3 bs]; [list_solve|].
  destruct bs as [|b4 bs]; [list_solve|].
  destruct bs as [|b5 bs]; [list_solve|].
  destruct bs as [|b6 bs]; [list_solve|].
  destruct bs as [|b7 bs]; [list_solve|].
  destruct bs as [|b8 bs]; [|exfalso; list_solve].
  clear Hlen.

  (* extract the per-byte range facts [0 <= bi < 256] *)
  inversion Hrange as [|x l Hb0 Hr0]; subst.
  inversion Hr0 as [|x l Hb1 Hr1]; subst.
  inversion Hr1 as [|x l Hb2 Hr2]; subst.
  inversion Hr2 as [|x l Hb3 Hr3]; subst.
  inversion Hr3 as [|x l Hb4 Hr4]; subst.
  inversion Hr4 as [|x l Hb5 Hr5]; subst.
  inversion Hr5 as [|x l Hb6 Hr6]; subst.
  inversion Hr6 as [|x l Hb7 Hr7]; subst.
  clear Hrange Hr0 Hr1 Hr2 Hr3 Hr4 Hr5 Hr6 Hr7.

  unfold bytes_to_val.
  simpl map.

  (* ===== Stage 2: load the 8 bytes [p[0]..p[7]] ===== *)

  forward; [now (entailer!; rep_lia)|].
  forward; [now (entailer!; rep_lia)|].
  forward; [now (entailer!; rep_lia)|].
  forward; [now (entailer!; rep_lia)|].
  forward; [now (entailer!; rep_lia)|].
  forward; [now (entailer!; rep_lia)|].
  forward; [now (entailer!; rep_lia)|].
  forward; [now (entailer!; rep_lia)|].

  (* ===== Stage 3: return the OR-of-shifts ===== *)

  forward.
  entailer!.
  clear H H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 PNp.

  (* reduce the C [sem_or]/[sem_shl]/[sem_cast] cascade to [Int64] ops *)
  simpl Znth.
  list_simplify.
  unfold Zrepeat.
  simpl app.
  simpl.
  f_equal.
  rewrite !Int.unsigned_repr by rep_lia.

  (* ===== Stage 4: OR-of-disjoint-shifts equals the big-endian sum =====
     Re-associate the [Int64.or] tree to the right, then peel each byte
     bottom-up with [Int64.shifted_or_is_add]; the carried low value is
     always strictly below the next shift window [two_p n]. *)

  rewrite !Int64.or_assoc.
  rewrite (Int64.shifted_or_is_add (Int64.repr b6) (Int64.repr b7) 8)
    by (try (change Int64.zwordsize with 64; lia);
        rewrite Int64.unsigned_repr by rep_lia;
        change (two_p 8) with 256; lia).
  rewrite !Int64.unsigned_repr by rep_lia.
  change (two_p 8) with 256.
  rewrite (Int64.shifted_or_is_add (Int64.repr b5)
             (Int64.repr (b6 * 256 + b7)) 16)
    by (try (change Int64.zwordsize with 64; lia);
        rewrite Int64.unsigned_repr by rep_lia;
        change (two_p 16) with 65536; lia).
  rewrite !Int64.unsigned_repr by rep_lia.
  change (two_p 16) with 65536.
  rewrite (Int64.shifted_or_is_add (Int64.repr b4)
             (Int64.repr (b5 * 65536 + (b6 * 256 + b7))) 24)
    by (try (change Int64.zwordsize with 64; lia);
        rewrite Int64.unsigned_repr by rep_lia;
        change (two_p 24) with 16777216; lia).
  rewrite !Int64.unsigned_repr by rep_lia.
  change (two_p 24) with 16777216.
  rewrite (Int64.shifted_or_is_add (Int64.repr b3)
             (Int64.repr (b4 * 16777216 + (b5 * 65536 + (b6 * 256 + b7)))) 32)
    by (try (change Int64.zwordsize with 64; lia);
        rewrite Int64.unsigned_repr by rep_lia;
        change (two_p 32) with 4294967296; lia).
  rewrite !Int64.unsigned_repr by rep_lia.
  change (two_p 32) with 4294967296.
  rewrite (Int64.shifted_or_is_add (Int64.repr b2)
             (Int64.repr (b3 * 4294967296 +
                          (b4 * 16777216 + (b5 * 65536 + (b6 * 256 + b7))))) 40)
    by (try (change Int64.zwordsize with 64; lia);
        rewrite Int64.unsigned_repr by rep_lia;
        change (two_p 40) with 1099511627776; lia).
  rewrite !Int64.unsigned_repr by rep_lia.
  change (two_p 40) with 1099511627776.
  rewrite (Int64.shifted_or_is_add (Int64.repr b1)
             (Int64.repr (b2 * 1099511627776 +
                          (b3 * 4294967296 +
                           (b4 * 16777216 + (b5 * 65536 + (b6 * 256 + b7)))))) 48)
    by (try (change Int64.zwordsize with 64; lia);
        rewrite Int64.unsigned_repr by rep_lia;
        change (two_p 48) with 281474976710656; lia).
  rewrite !Int64.unsigned_repr by rep_lia.
  change (two_p 48) with 281474976710656.
  rewrite (Int64.shifted_or_is_add (Int64.repr b0)
             (Int64.repr (b1 * 281474976710656 +
                          (b2 * 1099511627776 +
                           (b3 * 4294967296 +
                            (b4 * 16777216 +
                             (b5 * 65536 + (b6 * 256 + b7))))))) 56)
    by (try (change Int64.zwordsize with 64; lia);
        rewrite Int64.unsigned_repr by rep_lia;
        change (two_p 56) with 72057594037927936; lia).
  rewrite !Int64.unsigned_repr by rep_lia.
  change (two_p 56) with 72057594037927936.

  (* ===== Stage 5: the closed sum equals [Z_of_be_bytes] ===== *)

  f_equal.
  unfold integer_bytes.Z_of_be_bytes.
  cbn.
  ring.
Qed.
