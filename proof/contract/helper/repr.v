(** * contract.helper.repr: model-to-C representation predicates (machine
    words + bytes -- FROZEN; each subsystem owns its further bridges, e.g.
    [fe_to_val] in [contract.field]). *)
(** Copyright (C) 2026 remix7531
    SPDX-License-Identifier: MIT *)

Require Import secp256k1.vst.base.
Require Import secp256k1.contract.helper.structs_int128.
Require Import secp256k1.contract.helper.structs_scalar.
Require Import secp256k1.model.int128.
Require Import secp256k1.model.acc.
Require Import secp256k1.model.scalar.
Require Import secp256k1.theory.arithmetic.
Require Import secp256k1.theory.bits.
Require Import secp256k1.vst.array_data_at.

(* ================================================================= *)
(** ** Unsigned model-to-C bridges -- [uint64_to_val] / [uint128_to_val] / [acc_to_val] / [uint256_to_val] / [scalar_to_val] / [uint512_to_val] / [bytes_to_val], plus the [val_to_*] reconstructors. *)

(** Represent a [UInt64] as a C value. *)
Definition uint64_to_val (x : UInt64) : val :=
  Vlong (Int64.repr (u64_val x)).

(** Represent a [UInt128] as a C struct (lo, hi). *)
Definition uint128_to_val (x : UInt128) : reptype t_secp256k1_u128 :=
  let v := u128_val x in
  (Vlong (Int64.repr (v mod 2^64)),
   Vlong (Int64.repr ((v / 2^64) mod 2^64))).

(** Represent an [Acc] as a C struct (c0, c1, c2). *)
Definition acc_to_val (x : Acc) : reptype t_secp256k1_acc :=
  let v := acc_val x in
  (Vlong (Int64.repr (v mod 2^64)),
   (Vlong (Int64.repr ((v / 2^64) mod 2^64)),
    Vlong (Int64.repr ((v / 2^128) mod 2^64)))).

(** Represent a [UInt256] as a 4-limb C scalar struct. *)
Definition uint256_to_val (x : UInt256) : reptype t_secp256k1_uint256 :=
  let v := u256_val x in
  [ Vlong (Int64.repr (v mod 2^64));
    Vlong (Int64.repr ((v / 2^64) mod 2^64));
    Vlong (Int64.repr ((v / 2^128) mod 2^64));
    Vlong (Int64.repr ((v / 2^192) mod 2^64)) ].

(** Represent a [Scalar] as a 4-limb C scalar struct.
    Each limb is [(x / 2^(64*i)) mod 2^64]. *)
Definition scalar_to_val (x : Scalar) : reptype t_secp256k1_scalar :=
  [ Vlong (Int64.repr (x mod 2^64));
    Vlong (Int64.repr ((x / 2^64) mod 2^64));
    Vlong (Int64.repr ((x / 2^128) mod 2^64));
    Vlong (Int64.repr ((x / 2^192) mod 2^64)) ].

(** [scalar_to_val] and [uint256_to_val o scalar_to_u256] agree. *)
Lemma scalar_to_val_eq (s : Scalar) :
  scalar_to_val s = uint256_to_val (scalar_to_u256 s).
Proof. reflexivity. Qed.

(** Represent a [UInt512] as an 8-limb C array. *)
Definition uint512_to_val (x : UInt512) : list val :=
  let v := u512_val x in
  [ Vlong (Int64.repr (v mod 2^64));
    Vlong (Int64.repr ((v / 2^64) mod 2^64));
    Vlong (Int64.repr ((v / 2^128) mod 2^64));
    Vlong (Int64.repr ((v / 2^192) mod 2^64));
    Vlong (Int64.repr ((v / 2^256) mod 2^64));
    Vlong (Int64.repr ((v / 2^320) mod 2^64));
    Vlong (Int64.repr ((v / 2^384) mod 2^64));
    Vlong (Int64.repr ((v / 2^448) mod 2^64)) ].

(** Represent a byte buffer (each byte in [[0, 256)]) as a C [tuchar] array.
    Used by the big-endian scalar (de)serialization specs ([set_b32] /
    [get_b32]) and the [read_be64] / [write_be64] helpers. *)
Definition bytes_to_val (bs : list Z) : list val :=
  map (fun b => Vint (Int.repr b)) bs.

(** Reconstruct a [UInt64] from a raw Z value. *)
Program Definition val_to_uint64 (z : Z)
  (H : 0 <= z < 2^64) : UInt64 :=
  mkUInt64 z _.

(** Reconstruct a [UInt128] from two 64-bit Z limbs (lo, hi). *)
Program Definition val_to_uint128 (lo hi : Z)
  (Hlo : 0 <= lo < 2^64) (Hhi : 0 <= hi < 2^64) : UInt128 :=
  mkUInt128 (lo + hi * 2^64) _.
Next Obligation. nia. Qed.

(** Reconstruct an [Acc] from three 64-bit Z limbs (c0, c1, c2). *)
Program Definition val_to_acc (c0 c1 c2 : Z)
  (H0 : 0 <= c0 < 2^64) (H1 : 0 <= c1 < 2^64) (H2 : 0 <= c2 < 2^64)
  : Acc :=
  mkAcc (c0 + c1 * 2^64 + c2 * 2^128) _.
Next Obligation. nia. Qed.

(* ================================================================= *)
(** ** Per-limb [Znth] bridges -- [uint256_to_val_Znth] / [uint512_to_val_Znth]. *)

(** Each element of [uint256_to_val x] is [uint64_to_val (u256_limb x i)]. *)
Lemma uint256_to_val_Znth : forall (x : UInt256) (i : Z),
  0 <= i < 4 ->
  Znth i (uint256_to_val x) = uint64_to_val (u256_limb x (Z.to_nat i)).
Proof.
  intros x i Hi.
  unfold uint256_to_val, uint64_to_val, u256_limb.
  simpl.
  assert (i = 0 \/ i = 1 \/ i = 2 \/ i = 3) by lia.
  destruct H as [Hi0|[Hi1|[Hi2|Hi3]]];
    subst i; simpl Znth; unfold limb; simpl Z.of_nat;
    rewrite ?Z.mul_0_r, ?Z.pow_0_r, ?Z.div_1_r; reflexivity.
Qed.

(** Each element of [uint512_to_val l] is limb [i] of [u512_val l]. *)
Lemma uint512_to_val_Znth : forall (l : UInt512) i,
  0 <= i < 8 ->
  Znth i (uint512_to_val l) = Vlong (Int64.repr (limb (2^64) (u512_val l) (Z.to_nat i))).
Proof.
  intros l i Hi.
  unfold uint512_to_val, limb.
  assert (i = 0 \/ i = 1 \/ i = 2 \/ i = 3 \/ i = 4 \/ i = 5 \/ i = 6 \/ i = 7) as Hc by lia.
  destruct Hc as [E|[E|[E|[E|[E|[E|[E|E]]]]]]]; subst i;
    cbn [Z.to_nat Z.of_nat Pos.of_succ_nat];
    change ((2^64)^0) with 1;
    change ((2^64)^1) with (2^64);
    change ((2^64)^2) with (2^128);
    change ((2^64)^3) with (2^192);
    change ((2^64)^4) with (2^256);
    change ((2^64)^5) with (2^320);
    change ((2^64)^6) with (2^384);
    change ((2^64)^7) with (2^448);
    rewrite ?Z.div_1_r; reflexivity.
Qed.

(* ================================================================= *)
(** ** Signed model-to-C bridges -- [int64_to_val] / [int128_to_val]. *)

(** Represent an [Int64] as a C [long] value. *)
Definition int64_to_val (x : Int64) : val :=
  Vlong (Int64.repr (i64_val x)).

(** Represent an [Int128] as a C struct (lo, hi).
    lo holds the low 64 bits (unsigned); hi holds the high 64 bits
    (sign-extended, stored as the raw bit pattern via [Int64.repr]). *)
Definition int128_to_val (x : Int128) : reptype t_secp256k1_u128 :=
  let v := i128_val x in
  (Vlong (Int64.repr (v mod 2^64)),
   Vlong (Int64.repr (v / 2^64))).

(** The spatial-predicate notation ([u64_at], [u128_at], [scalar_at], ...)
    that wraps these [*_to_val] bridges lives in [contract.helper.notations]. *)

(* ================================================================= *)
(** ** limb-form bridges -- [*_to_val_limb] (the [to_val_limb] rewrite db).

    Equate the inlined-split form of each C-representation above to its
    [limb (2^64) v i]-based form (moved here from the former tactics/automation.v:
    they are statements ABOUT these representation functions). *)

Lemma uint128_to_val_limb : forall x,
  uint128_to_val x =
  (Vlong (Int64.repr (limb (2^64) (u128_val x) 0)),
   Vlong (Int64.repr (limb (2^64) (u128_val x) 1))).
Proof.
  intros. unfold uint128_to_val.
  rewrite (limb_fold1 (u128_val x)), (limb_fold0 (u128_val x)).
  reflexivity.
Qed.

(** Signed counterpart. The low limb folds to [limb (2^64) v 0] like the
    unsigned case, but the high limb stays [v / 2^64] (NO outer [mod]): the
    stored high word is the sign-extended quotient, not a masked limb. *)
Lemma int128_to_val_limb : forall x,
  int128_to_val x =
  (Vlong (Int64.repr (limb (2^64) (i128_val x) 0)),
   Vlong (Int64.repr (i128_val x / 2^64))).
Proof.
  intros. unfold int128_to_val.
  rewrite (limb_fold0 (i128_val x)).
  reflexivity.
Qed.

Lemma acc_to_val_limb : forall x,
  acc_to_val x =
  (Vlong (Int64.repr (limb (2^64) (acc_val x) 0)),
   (Vlong (Int64.repr (limb (2^64) (acc_val x) 1)),
    Vlong (Int64.repr (limb (2^64) (acc_val x) 2)))).
Proof.
  intros. unfold acc_to_val.
  rewrite (limb_fold2 (acc_val x)), (limb_fold1 (acc_val x)),
          (limb_fold0 (acc_val x)).
  reflexivity.
Qed.

Lemma uint256_to_val_limb : forall x,
  uint256_to_val x =
  [Vlong (Int64.repr (limb (2^64) (u256_val x) 0));
   Vlong (Int64.repr (limb (2^64) (u256_val x) 1));
   Vlong (Int64.repr (limb (2^64) (u256_val x) 2));
   Vlong (Int64.repr (limb (2^64) (u256_val x) 3))].
Proof.
  intros. unfold uint256_to_val.
  rewrite (limb_fold3 (u256_val x)), (limb_fold2 (u256_val x)),
          (limb_fold1 (u256_val x)), (limb_fold0 (u256_val x)).
  reflexivity.
Qed.

Lemma uint512_to_val_limb : forall x,
  uint512_to_val x =
  [Vlong (Int64.repr (limb (2^64) (u512_val x) 0));
   Vlong (Int64.repr (limb (2^64) (u512_val x) 1));
   Vlong (Int64.repr (limb (2^64) (u512_val x) 2));
   Vlong (Int64.repr (limb (2^64) (u512_val x) 3));
   Vlong (Int64.repr (limb (2^64) (u512_val x) 4));
   Vlong (Int64.repr (limb (2^64) (u512_val x) 5));
   Vlong (Int64.repr (limb (2^64) (u512_val x) 6));
   Vlong (Int64.repr (limb (2^64) (u512_val x) 7))].
Proof.
  intros. unfold uint512_to_val.
  rewrite (limb_fold7 (u512_val x)), (limb_fold6 (u512_val x)),
          (limb_fold5 (u512_val x)), (limb_fold4 (u512_val x)),
          (limb_fold3 (u512_val x)), (limb_fold2 (u512_val x)),
          (limb_fold1 (u512_val x)), (limb_fold0 (u512_val x)).
  reflexivity.
Qed.

#[export] Hint Rewrite uint128_to_val_limb int128_to_val_limb acc_to_val_limb
  uint256_to_val_limb uint512_to_val_limb : to_val_limb.
