(** * vst.integers: CompCert [Int] / [Int64] <-> [Z] bridges and mask identities. *)
(** Copyright (C) 2026 remix7531
    [of_bool_if], [Int_signed_b2z], [zlt_ltb], [Zleb_bool], [Int_shr_shiftr],
    [Int64_shru_shiftr], [Int64_shr_shiftr], [xor64_repr] and
    [Int_repr_Int64_Z_mod_modulus] are ported from
    BlockstreamResearch/simplicity Coq/C/progressC.v
    (commit c1dddedd), Copyright (c) 2018 Blockstream, originally MIT.
    Upstream notice reproduced in proof/README.md.
    SPDX-License-Identifier: MIT *)

(** Word-level glue between CompCert's machine integers and plain [Z]: the
    boolean / comparison bridges, the shift bridges, and the branchless mask
    identities that realize the constant-time C masking idioms, plus the
    signed-range shapes [forward]'s type-checker asks for.  Subsystem-free
    (it imports nothing above [vst.base]), so every layer of the proof can use
    it; [tactics.core] re-exports it.  The [int_to_z] rewrite database at the
    bottom bundles the unconditional equalities for [autorewrite]. *)

Require Import secp256k1.vst.base.

(* ================================================================= *)
(** ** Boolean / comparison bridges -- [of_bool_if] / [Int_signed_b2z] / [zlt_ltb] / [Zleb_bool]. *)

(** [Val.of_bool] is the [Vint] of the boolean's [0]/[1] value. *)
Lemma of_bool_if b : Val.of_bool b = Vint (Int.repr (Z.b2z b)).
Proof.
destruct b; reflexivity.
Qed.

(** [Int.signed] is a no-op on a [b2z]-valued [Int.repr]. *)
Lemma Int_signed_b2z b : Int.signed (Int.repr (Z.b2z b)) = Z.b2z b.
Proof.
destruct b; reflexivity.
Qed.

(** Reflect the [zlt] decision into the boolean [<?]. *)
Lemma zlt_ltb a b : (if zlt a b then true else false) = (a <? b).
Proof.
destruct (zlt a b); destruct (Z.ltb_spec a b); try reflexivity; lia.
Qed.

(** The C [<=] on boolean operands as [orb (negb a) b] (i.e. [a -> b]). *)
Lemma Zleb_bool a b : negb (Z.b2z b <? Z.b2z a) = orb (negb a) b.
Proof.
destruct a; destruct b; reflexivity.
Qed.

(* ================================================================= *)
(** ** Shift bridges -- [Int_shr_shiftr] / [Int64_shru_shiftr] / [Int64_shr_shiftr]. *)

(** Rewrite the [Int.shr] (arithmetic) shift as [Z.shiftr] on the signed value. *)
Lemma Int_shr_shiftr x y : Int.shr x y = Int.repr (Z.shiftr (Int.signed x) (Int.unsigned y)).
Proof.
rewrite Int.shr_div_two_p.
rewrite Zbits.Zshiftr_div_two_p by rep_lia.
reflexivity.
Qed.

(** Rewrite the [Int64.shru] (logical) shift as [Z.shiftr] on the unsigned value. *)
Lemma Int64_shru_shiftr x y : Int64.shru x y = Int64.repr (Z.shiftr (Int64.unsigned x) (Int64.unsigned y)).
Proof.
rewrite Int64.shru_div_two_p.
rewrite Zbits.Zshiftr_div_two_p by rep_lia.
reflexivity.
Qed.

(** Rewrite the [Int64.shr] (arithmetic) shift as [Z.shiftr] on the signed value. *)
Lemma Int64_shr_shiftr x y : Int64.shr x y = Int64.repr (Z.shiftr (Int64.signed x) (Int64.unsigned y)).
Proof.
rewrite Int64.shr_div_two_p.
rewrite Zbits.Zshiftr_div_two_p by rep_lia.
reflexivity.
Qed.

(* ================================================================= *)
(** ** Branchless mask / shift identities -- [Int64_shr_sign_mask] and friends. *)

(** [Int64] realizations of the constant-time C masking code (shared by the
    divstep / get_bits proofs).  Stated wrapper-free (shift amounts are plain
    [Int64.repr c] / [Int.repr c]); callers [change] the C-specific
    [Int.unsigned (Int.repr ..)] wrappers. *)

(** [z >> 63] over a signed [tlong] in [[min_signed, max_signed]] is the sign
    mask: [-1] when [z < 0], else [0]. *)
Lemma Int64_shr_sign_mask (z : Z) :
  Int64.min_signed <= z <= Int64.max_signed ->
  Int64.shr (Int64.repr z) (Int64.repr 63) = Int64.repr (if z <? 0 then -1 else 0).
Proof.
intro Hz.
rewrite Int64.shr_div_two_p.
change (two_p (Int64.unsigned (Int64.repr 63))) with (2 ^ 63).
rewrite Int64.signed_repr by rep_lia.
f_equal.
destruct (z <? 0) eqn:Hlt.
- (* z < 0: floor division by 2^63 is -1 *)
  apply Z.ltb_lt in Hlt.
  symmetry.
  apply Zdiv.Zdiv_unique with (z + 2 ^ 63); rep_lia.
- (* z >= 0: small dividend, quotient 0 *)
  apply Z.ltb_ge in Hlt.
  apply Z.div_small; rep_lia.
Qed.

(** [g & 1] is the parity [g mod 2]. *)
Lemma Int64_and_low1 (g : Z) :
  Int64.and (Int64.repr g) (Int64.repr 1) = Int64.repr (g mod 2).
Proof.
rewrite Int64.and_commut.
rewrite and64_repr.
f_equal.
rewrite Z.land_comm.
change 1 with (Z.ones 1).
rewrite Z.land_ones by lia.
reflexivity.
Qed.

(** [(a ^ mask) - mask] selects [-a] when [mask = -1], else [a]. *)
Lemma Int64_xor_sub_mask (a : Z) (b : bool) :
  Int64.sub (Int64.xor (Int64.repr a) (Int64.repr (if b then -1 else 0)))
            (Int64.repr (if b then -1 else 0)) =
  Int64.repr (if b then -a else a).
Proof.
destruct b.
- (* mask = -1: xor is bitwise-not, [(not a) - (-1) = -a] *)
  change (Int64.repr (-1)) with Int64.mone.
  fold (Int64.not (Int64.repr a)).
  rewrite Int64.not_neg, Int64.neg_repr.
  change Int64.mone with (Int64.repr (-1)).
  rewrite add64_repr, sub64_repr.
  f_equal.
  ring.
- (* mask = 0: identity *)
  change (Int64.repr 0) with Int64.zero.
  rewrite Int64.xor_zero, Int64.sub_zero_l.
  reflexivity.
Qed.

(** [a & mask] selects [a] when [mask = -1], else [0]. *)
Lemma Int64_and_mask (a : Z) (b : bool) :
  Int64.and (Int64.repr a) (Int64.repr (if b then -1 else 0)) =
  Int64.repr (if b then a else 0).
Proof.
destruct b.
- change (Int64.repr (-1)) with Int64.mone.
  apply Int64.and_mone.
- change (Int64.repr 0) with Int64.zero.
  apply Int64.and_zero.
Qed.

(** Logical [<< 1] on the [Int64.repr] of [e] (sign-agnostic, doubles mod [2^64]). *)
Lemma Int64_shl1 (e : Z) :
  Int64.shl (Int64.repr e) (Int64.repr 1) = Int64.repr (2 * e).
Proof.
rewrite Int64.shl_mul_two_p.
change (Int64.unsigned (Int64.repr 1)) with 1.
change (two_p 1) with 2.
rewrite mul64_repr.
f_equal.
ring.
Qed.

(** Logical [>> 1] on the [Int64.repr] of [w]: the word [w mod 2^64] halved. *)
Lemma Int64_shru1 (w : Z) :
  Int64.shru (Int64.repr w) (Int64.repr 1) = Int64.repr (Z.shiftr (w mod Int64.modulus) 1).
Proof.
rewrite Int64.shru_div_two_p.
change (Int64.unsigned (Int64.repr 1)) with 1.
change (two_p 1) with 2.
rewrite Int64.unsigned_repr_eq.
rewrite Z.shiftr_div_pow2 by lia.
reflexivity.
Qed.

(** The C mask [0xFFFFFFFF >> (32 - c)] is [2^c - 1] (a [c]-bit low mask). *)
Lemma Int_shru_neg1_mask (c : Z) :
  0 < c <= 32 ->
  Int.shru (Int.repr (-1)) (Int.repr (32 - c)) = Int.repr (2 ^ c - 1).
Proof.
intro Hc.
rewrite Int.shru_div_two_p.
rewrite (Int.unsigned_repr (32 - c)) by rep_lia.
change (Int.unsigned (Int.repr (-1))) with (2 ^ 32 - 1).
rewrite two_p_correct.
f_equal.
assert (Hpc0 : 0 < 2 ^ c) by (apply Z.pow_pos_nonneg; lia).
assert (Hpd0 : 0 < 2 ^ (32 - c)) by (apply Z.pow_pos_nonneg; lia).
assert (Hsplit : 2 ^ 32 = 2 ^ c * 2 ^ (32 - c))
  by (rewrite <- Z.pow_add_r by lia; f_equal; lia).
symmetry.
apply Z.div_unique_pos with (r := 2 ^ (32 - c) - 1); lia.
Qed.

(** [~x] on a [uint64] is [2^64 - 1 - x]: bitwise-not as arithmetic.  An [Int64]
    fact (not pure [Z]), shared by the scalar negate / cond_negate proofs. *)
Lemma Int64_not_repr_complement (x : Z) :
  0 <= x < 2^64 ->
  Int64.not (Int64.repr x) = Int64.repr (2^64 - 1 - x).
Proof.
intros Hx.
rewrite Int64.not_neg.
rewrite Int64.neg_repr.
change Int64.mone with (Int64.repr (-1)).
rewrite add64_repr.
apply Int64.eqm_samerepr.
exists (-1).
change Int64.modulus with (2^64).
lia.
Qed.

(** The [nonzero] mask value [secp256k1_scalar_negate] computes from a
    decided zero test: [(uint64_t)(-1) * (secp256k1_scalar_is_zero(a) == 0)]
    compiles to exactly this nested [Int64]/[Int] expression.  Generalised
    over an arbitrary decided proposition [P] -- the call site instantiates
    [d] with the zero-test decision [Z.eq_dec av 0], so [d]'s type pins down
    [P] by unification and a bare [apply] closes the goal. *)
Lemma Int64_neg1_mul_b2z_eq (P : Prop) (d : {P} + {~ P}) :
  Int64.mul (Int64.repr (-1))
    (Int64.repr
       (Int.signed
          (Int.repr
             (Z.b2z
                (Int.eq (Int.repr (if d then 1 else 0))
                   (Int.repr 0))))))
  = if d then Int64.zero else Int64.mone.
Proof.
destruct d; apply Int64.same_if_eq; vm_compute; reflexivity.
Qed.

(* ================================================================= *)
(** ** Ported word identities -- [xor64_repr] / [Int_repr_Int64_Z_mod_modulus]. *)

(** Bitwise [xor] of two [Int64.repr]s is the [repr] of the [Z] xor. *)
Lemma xor64_repr i j : Int64.xor (Int64.repr i) (Int64.repr j) = Int64.repr (Z.lxor i j).
Proof.
apply Int64.same_bits_eq.
intros k Hk.
rewrite Int64.bits_xor, !Int64.testbit_repr, Z.lxor_spec; auto.
Qed.

(** Reducing a [Z] modulo [2^64] before truncating it to an [Int] is a no-op. *)
Lemma Int_repr_Int64_Z_mod_modulus x : Int.repr (Int64.Z_mod_modulus x) = Int.repr x.
Proof.
apply modulo_samerepr.
rewrite Int64.Z_mod_modulus_eq, <- Zmod_div_mod; try rep_lia.
exists Int.modulus; reflexivity.
Qed.

(* ================================================================= *)
(** ** int64 type-check ranges -- [Int64_add_mask_range] and friends. *)

(** The signed-range shapes [forward] asks for when it type-checks the masked
    limb arithmetic of the safegcd C bodies.  A body poses them (with
    [pose proof]) up front, in exactly this shape, so the per-limb [tc_expr]
    obligations are discharged from the context without an explicit side-goal
    block.  Stated on the [Z] operands, with the sign mask as [if b then -1
    else 0]; [theory.bits] states the same sign-mask vocabulary on plain [Z]
    ([land_sign_mask_eq] and friends). *)

(** [r_i + (m_i & mask)]: a limb in [(-2^62, 2^62)] plus a masked modulus limb
    stays in [int64] range. *)
Lemma Int64_add_mask_range : forall (b : bool) (x y : Z), - (2 ^ 62) < x < 2 ^ 62 -> 0 <= y < 2 ^ 62 ->
  Int64.min_signed <= Int64.signed (Int64.repr x) +
    Int64.signed (Int64.repr (Z.land y (if b then -1 else 0))) <= Int64.max_signed.
Proof.
intros b x y Hx Hy.
rewrite (Int64.signed_repr x) by rep_lia.
destruct b.
- (* mask = -1: the masked limb passes through *)
  rewrite Z.land_m1_r.
  rewrite Int64.signed_repr by rep_lia.
  rep_lia.
- (* mask = 0: the masked limb vanishes *)
  rewrite Z.land_0_r.
  rewrite Int64.signed_repr by rep_lia.
  rep_lia.
Qed.

(** [(r_i ^ mask) - mask]: complementing and re-adding the sign mask keeps a
    limb in [(-2^62, 2^63)] in [int64] range. *)
Lemma Int64_xor_sub_mask_range : forall (b : bool) (x : Z), - (2 ^ 62) < x < 2 ^ 63 ->
  Int64.min_signed <=
    Int64.signed (Int64.xor (Int64.repr x) (Int64.repr (if b then -1 else 0))) -
    Int64.signed (Int64.repr (if b then -1 else 0)) <= Int64.max_signed.
Proof.
intros b x Hx.
rewrite xor64_repr.
destruct b.
- (* mask = -1: the xor is the complement [-x-1] *)
  rewrite Z.lxor_m1_r.
  replace (Z.lnot x) with (- x - 1) by (unfold Z.lnot; lia).
  rewrite Int64.signed_repr by rep_lia.
  rewrite Int64.signed_repr by rep_lia.
  rep_lia.
- (* mask = 0: the xor is the identity *)
  rewrite Z.lxor_0_r.
  rewrite Int64.signed_repr by rep_lia.
  rewrite Int64.signed_repr by rep_lia.
  rep_lia.
Qed.

(** [r_i+1 += r_i >> 62]: the incoming carry lies in [[-2, 2)], so the
    accumulator stays in [int64] range. *)
Lemma Int64_add_shr_range : forall (x y : Z), - 2 ^ 63 + 2 <= x <= 2 ^ 63 - 2 -> - 2 ^ 63 <= y <= 2 ^ 63 - 1 ->
  Int64.min_signed <= x + Int64.signed (Int64.shr (Int64.repr y) (Int64.repr 62)) <= Int64.max_signed.
Proof.
intros x y Hx Hy.
rewrite Int64_shr_shiftr.
rewrite (Int64.signed_repr y) by rep_lia.
rewrite Int64.unsigned_repr by rep_lia.
assert (Hc : -2 <= Z.shiftr y 62 < 2).
{ rewrite Z.shiftr_div_pow2 by lia.
  split.
  - apply Z.div_le_lower_bound; lia.
  - apply Z.div_lt_upper_bound; lia. }
rewrite Int64.signed_repr by rep_lia.
rep_lia.
Qed.

(** The interior-limb specialization of [Int64_add_mask_range]: both operands
    are 62-bit residues, so the range hypotheses are discharged internally. *)
Lemma Int64_add_mask_mod62_range : forall (b : bool) (x y : Z),
  Int64.min_signed <= Int64.signed (Int64.repr (x mod 2 ^ 62)) +
    Int64.signed (Int64.repr (Z.land (y mod 2 ^ 62) (if b then -1 else 0))) <= Int64.max_signed.
Proof.
intros b x y.
assert (Hx := Z.mod_pos_bound x (2 ^ 62) ltac:(lia)).
assert (Hy := Z.mod_pos_bound y (2 ^ 62) ltac:(lia)).
apply Int64_add_mask_range; lia.
Qed.

(** The interior-limb specialization of [Int64_xor_sub_mask_range]: the
    complemented operand is a 62-bit residue plus an optional second one. *)
Lemma Int64_xor_sub_mask_mod62_range : forall (b c : bool) (x y : Z),
  Int64.min_signed <=
    Int64.signed (Int64.xor (Int64.repr (x mod 2 ^ 62 + (if c then y mod 2 ^ 62 else 0)))
                            (Int64.repr (if b then -1 else 0))) -
    Int64.signed (Int64.repr (if b then -1 else 0)) <= Int64.max_signed.
Proof.
intros b c x y.
assert (Hx := Z.mod_pos_bound x (2 ^ 62) ltac:(lia)).
assert (Hy := Z.mod_pos_bound y (2 ^ 62) ltac:(lia)).
apply Int64_xor_sub_mask_range.
destruct c; lia.
Qed.

(* ================================================================= *)
(** ** The [int_to_z] rewrite database -- machine words down to plain [Z]. *)

(** [autorewrite with int_to_z] pushes CompCert word operations down onto a
    single [Int.repr] / [Int64.repr] of a plain [Z] expression: the arithmetic
    and bitwise [*_repr] combinators, the shift bridges, the [zero] projections
    and the boolean reflections above.

    Every rule registered here is an UNCONDITIONAL equality, so [autorewrite]
    can never leave a side goal.  Deliberately excluded, because they carry a
    range hypothesis and must be discharged at the call site: [Int.signed_repr]
    / [Int64.signed_repr], [Int.unsigned_repr] / [Int64.unsigned_repr], the
    [*_unsigned_repr_eq] modulus forms, [Int.signed_one], and
    [Int64.shl_mul_two_p] (whose [two_p] result needs a further [two_p_equiv]
    step). *)
#[export] Hint Rewrite
  of_bool_if Int_signed_b2z zlt_ltb Zleb_bool
  Int_shr_shiftr Int64_shru_shiftr Int64_shr_shiftr
  add64_repr sub64_repr mul64_repr and64_repr or64_repr xor64_repr
  Int64.neg_repr sub_repr
  Int.signed_zero Int64.signed_zero Int64.unsigned_zero
  : int_to_z.
