(** * Verif_i128_accum_mul: Proof of body_secp256k1_i128_accum_mul *)
(** Copyright (C) 2026 remix7531
    SPDX-License-Identifier: MIT *)

Require Import secp256k1.vst.base.
Require Import secp256k1.contract.helper.notations.
Require Import secp256k1.contract.gprog.int128.
Require Import secp256k1.tactics.core.
Require Import secp256k1.tactics.int128.

(* ================================================================= *)
(** ** secp256k1_i128_accum_mul -- [r += a*b]. *)

(** The C body computes [lo = mul128(a,b)] (low 64 bits) and writes the
    signed high 64 bits to a stack-local [hi].  It then adds [lo] into
    [r->lo], folds the unsigned carry-out into [hi], and adds [hi] into
    [r->hi].  Reconstructing the result needs three local facts: the
    signed-limb recombination identity, the carry-detect bridge, and a
    bound on the product's high word.  All three are pure (no [data_at]),
    so they live here as file-local helpers. *)

(** The carry-recombination identity [arith_div_add_carry] (the high word of a
    sum is the sum of the high words plus the low-word carry-out) is the
    pure-Z [theory/arithmetic.v] lemma, used here at [M = 2^64]; its
    subtractive sibling [arith_div_sub_borrow] serves [i128_dissip_mul]. *)

(** Carry-detect bridge: the C idiom [(r->lo) < lo] (an unsigned [<])
    after [r->lo += lo] equals the arithmetic carry out of the low-word
    addition.  Here [R mod 2^64] is the old [r->lo] and [P] is the (raw,
    possibly negative) product, whose unsigned low limb is [P mod 2^64].
    Routes through [ltu_carry_b2z] after normalising both operands to
    their residues. *)
Lemma i128_accum_carry_ltu : forall R P : Z,
  Z.b2z (Int64.ltu (Int64.repr (R mod 2^64 + P)) (Int64.repr P)) =
  (if R mod 2^64 + P mod 2^64 <? 2^64 then 0 else 1).
Proof.
  intros R P.
  assert (HrP : Int64.repr P = Int64.repr (P mod 2^64)).
  { apply Int64.eqm_samerepr.
    change Int64.modulus with (2^64).
    apply eqmod_mod.
    lia. }
  assert (HrRP :
    Int64.repr (R mod 2^64 + P) = Int64.repr (R mod 2^64 + P mod 2^64)).
  { apply Int64.eqm_samerepr.
    change Int64.modulus with (2^64).
    apply eqmod_add.
    - apply eqmod_refl.
    - apply eqmod_mod.
      lia. }
  rewrite HrP, HrRP.
  rewrite (ltu_carry_b2z (R mod 2^64) (P mod 2^64)).
  - change Int64.modulus with (2^64).
    reflexivity.
  - pose proof (Z.mod_pos_bound R (2^64) ltac:(lia)).
    rep_lia.
  - pose proof (Z.mod_pos_bound P (2^64) ltac:(lia)).
    rep_lia.
Qed.

(** The high word of a 64x64 signed product is bounded by [2^62]:
    [|a*b| <= 2^126], so [(a*b)/2^64] lands in [[-2^62, 2^62]].  This
    keeps [hi += carry] inside [Int64] range (the store typecheck). *)
Lemma mul_i64_hi_bound : forall a b : Int64,
  -2^62 <= i64_val a * i64_val b / 2^64 <= 2^62.
Proof.
  intros a b.
  pose proof (i64_range a).
  pose proof (i64_range b).
  split.
  - apply Z.le_trans with (-(2^126) / 2^64).
    + reflexivity.
    + apply Z.div_le_mono; [lia | nia].
  - apply Z.le_trans with (2^126 / 2^64).
    + apply Z.div_le_mono; [lia | nia].
    + reflexivity.
Qed.

Lemma body_secp256k1_i128_accum_mul :
  semax_body Vprog Gprog
    f_secp256k1_i128_accum_mul spec_secp256k1_i128_accum_mul.
Proof.
  start_function.
  (* The two PROP bounds are the only facts the closing arithmetic needs:
     they witness that the result [i128_val r + a*b] fits in [Int128].
     Name them now so the [mkInt128] witness below reads clearly. *)
  rename H into Hres_lo.   (* -2^127 <= i128_val r + a*b *)
  rename H0 into Hres_hi.  (* i128_val r + a*b < 2^127 *)

  (* ===== Phase 1: lo = (uint64_t)secp256k1_mul128(a, b, &hi) ===== *)
  (* The helper returns the product's low 64 bits in [lo] and writes its
     signed high 64 bits to the stack-local [hi]. *)
  forward_call (a, b, v_hi, Tsh).

  (* ===== Phase 2: r->lo += lo, then fold the carry into hi ===== *)
  (* r->lo += lo *)
  forward. (* _t'6 = r->lo *)
  forward. (* r->lo = _t'6 + lo *)

  (* hi += (r->lo < lo): the unsigned comparison after the wrapping add is
     the carry-out of the low limb; add it into the high word. *)
  forward. (* _t'4 = hi *)
  forward. (* _t'5 = r->lo *)
  forward. (* hi = _t'4 + (_t'5 < lo) *)
  (* Store typecheck for [hi]: [hi + carry] stays in signed [Int64] range.
     The product's high word is bounded by [2^62] ([mul_i64_hi_bound]), so
     adding the 0/1 carry cannot overflow. *)
  { entailer!.
    pose proof (mul_i64_hi_bound a b) as Hhi.
    change (Z.pow_pos 2 64) with (2^64).
    change (let (q, _) := Z.div_eucl (i64_val a * i64_val b) (2^64) in q)
      with (i64_val a * i64_val b / 2^64).
    rewrite Int64.signed_repr by rep_lia.
    destruct (Int64.ltu _ _).
    - (* branch: carry = 1 *)
      simpl Z.b2z.
      rewrite Int.signed_repr by rep_lia.
      rep_lia.
    - (* branch: carry = 0 *)
      simpl Z.b2z.
      rewrite Int.signed_repr by rep_lia.
      rep_lia. }

  (* ===== Phase 3: r->hi += hi ===== *)
  forward. (* _t'2 = r->hi *)
  forward. (* _t'3 = hi *)
  forward. (* r->hi = _t'2 + _t'3 *)

  (* ===== Phase 4: postcondition ===== *)
  (* The two limb updates must reconstruct [i128_val r + a*b]. Supply that
     value (with its in-range proof) as the result [Int128]. *)
  Exists (mkInt128 (i128_val r + i64_val a * i64_val b) (conj Hres_lo Hres_hi)).
  entailer!.
  (* Drop the VST side facts [entailer!] introduced (field_compatible,
     tc_val', value_fits, pointer facts); the remaining goal is a pure
     limb-equality, so keep only the two result bounds. *)
  clear -Hres_lo Hres_hi.
  apply derives_refl'.
  unfold int128_to_val.
  simpl (i128_val {| i128_val := i128_val r + i64_val a * i64_val b;
                     i128_range := conj Hres_lo Hres_hi |}).
  f_equal.
  (* Normalise the C-representation's [Z.div_eucl] quotients to [_ / 2^64]
     so each limb goal becomes plain [Z] arithmetic. *)
  change (Z.pow_pos 2 64) with (2^64).
  change (let (q, _) := Z.div_eucl (i128_val r) (2^64) in q)
    with (i128_val r / 2^64).
  change (let (q, _) := Z.div_eucl (i64_val a * i64_val b) (2^64) in q)
    with (i64_val a * i64_val b / 2^64).
  f_equal.
  - (* low word: [(r mod 2^64 + a*b)] and [(r + a*b) mod 2^64] are equal mod 2^64 *)
    f_equal.
    apply Int64.eqm_samerepr.
    change Int64.modulus with (2^64).
    apply eqmod_trans with (i128_val r + i64_val a * i64_val b).
    + apply eqmod_add; [apply eqmod_sym; apply eqmod_mod; lia | apply eqmod_refl].
    + apply eqmod_mod.
      lia.
  - (* high word: [r/2^64 + (a*b/2^64 + carry) = (r + a*b) / 2^64] *)
    f_equal.
    (* the carry sits in [Int.repr] / [Int.signed]; drop that wrapper first *)
    rewrite Int.signed_repr
      by (destruct (Int64.ltu _ _); simpl Z.b2z; rep_lia).
    (* identify the C [<] idiom with the arithmetic low-limb carry-out *)
    rewrite i128_accum_carry_ltu.
    f_equal.
    (* the high word of a sum is [hi(r) + hi(a*b) + carry] ([arith_div_add_carry]) *)
    rewrite (arith_div_add_carry _ _ (2^64)) by lia.
    ring.
Qed.
