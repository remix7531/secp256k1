(** * model.tests_slow_ecmult_gen: seconds-scale checks for [model.ecmult_gen]. *)
(** Copyright (C) 2026 remix7531
    SPDX-License-Identifier: MIT *)

(** The [model/tests_ecmult_gen.v] checks that need real point arithmetic
    over the FULL 256-bit field ([fe_inv], about [4]-[15] seconds under
    [vm_compute] on this machine depending on concurrent load -- see that
    file's header for why the toy curves keep the SAME field size).
    Deliberately NOT in [_RocqProject]. VST-free, no axioms.

    [chk_gb_wf_100] lives here rather than in the fast file for the same
    real-field-arithmetic reason ([smul 100 G] is about a dozen [padd] /
    [pdouble] calls, ~50 seconds measured on this machine) -- see that
    check's own comment for a SECOND, sharper reason: naively discharging
    a [<> PInf] goal on a computed [Point] costs far more than the
    arithmetic alone, because [vm_compute] must reify the whole matched-out
    [Fe] pair (data plus its [Program]-generated range proof) back into a
    literal term for [discriminate] to inspect -- measured at over 100
    seconds and 5+ GB before it was rewritten through [point_neq_inf]
    below, against the ~50 seconds a boolean-witness [match] costs for the
    identical fact.

    SCOPE.  [model.ecmult_gen]'s pinned [ecmult_gen_model] cannot be
    exercised directly: it is [ecmult_gen_model_of] applied to the PINNED
    [comb_bits] (264), [secp256k1_N] and [G/2], all far out of [vm_compute]
    reach.  [ecmult_gen_model_of] itself IS instantiable at a toy order, and
    the module's headline check -- the blinded COMPOSITION,
    [chk_ecmult_gen13_blinded] at the end of this file -- is exactly that
    instance.  The exhaustive order-13 sweep the KAT plan asks for (that
    equation for every [n] in [[0, 13)]) is a COST deferral and nothing more:
    the single composition below measured 92.9 s standalone, so all 13
    residues run to about 20 minutes, which would roughly triple this file's
    total.  The other checks here exercise [comb] itself -- the function
    [comb_correct] (Admitted) is a claim about, and the one
    [ecmult_gen_model_of] actually calls -- directly, at the two toy
    geometries, which is exactly what [model/ecmult_gen.v]'s header
    recommends ("a small [nbits] is the way to exercise [comb] by
    computation").

    Even so, EVERY residue is not affordable: a single [comb]/[smul] pair at
    the order-199 geometry ([nbits = 12]) measured at about 280 seconds
    combined ([vm_compute] plus the kernel's [Qed] re-check) on this
    machine, i.e. exhausting all 199 residues would be many hours -- the
    same order-of-magnitude judgement [model/tests_group.v]'s header makes
    for a full-order [smul secp256k1_N G]. So this file checks: BOTH
    generators' stated order directly (the cheapest, most direct evidence
    the transcribed constants are right), and [comb] against the closed
    form at the two EXTREME digit patterns (all bits set / all bits clear)
    for order 13, where the cost is still affordable, and only the top
    pattern for order 199. *)

From Stdlib Require Import ZArith.
From Stdlib Require Import Lia.

Require Import secp256k1.model.constants.
Require Import secp256k1.model.group.
Require Import secp256k1.model.ecmult_gen.

Open Scope Z_scope.

(* ================================================================= *)
(** ** The two toy generators (same transcription as [model/tests_ecmult_gen.v];
    duplicated rather than imported, matching [model/tests_slow_group.v]'s
    independence from [model/tests_group.v]). *)

Definition G13_x_z : Z :=
  0xa2482ff84bf34edfa51262fde57921dbe0dd2cb7a5914790bc71631fc09704fb.
Definition G13_y_z : Z :=
  0x942536cba3e494923a701cc3ee3e443fdf182aa915b8aa6a166d3b19ba84b045.
Definition G199_x_z : Z :=
  0x7fb07b5cd07c3bda553902e27a87ea2c35108a7f051f41e5b76abad51f2703ad.
Definition G199_y_z : Z :=
  0xa2515395b4c4438952a634fac10dd4d6d6f474598990c273a4f3116d32ff969.

Program Definition fe_G13_x : Fe := mkFe G13_x_z _.
Next Obligation. unfold G13_x_z, secp256k1_P. lia. Qed.
Program Definition fe_G13_y : Fe := mkFe G13_y_z _.
Next Obligation. unfold G13_y_z, secp256k1_P. lia. Qed.
Program Definition fe_G199_x : Fe := mkFe G199_x_z _.
Next Obligation. unfold G199_x_z, secp256k1_P. lia. Qed.
Program Definition fe_G199_y : Fe := mkFe G199_y_z _.
Next Obligation. unfold G199_y_z, secp256k1_P. lia. Qed.

Definition G13 : Point := PAff fe_G13_x fe_G13_y.
Definition G199 : Point := PAff fe_G199_x fe_G199_y.

(* ================================================================= *)
(** ** The generators really have the claimed order.

    [src/group_impl.h:43-49]'s own comment states the subgroup size; this is
    that claim, literally, re-derived here by [smul] rather than assumed --
    the single strongest, cheapest-per-bit-of-assurance check this file can
    make about the two transcriptions above. Cross-checked independently in
    Python (a from-scratch affine double-and-add over the same [p]) before
    being written here. *)

(** [13 * G13 = O] -- [G13] generates the order-13 subgroup. *)
Lemma chk_g13_order : smul 13 G13 = PInf.
Proof. vm_compute. reflexivity. Qed.

(** [199 * G199 = O] -- [G199] generates the order-199 subgroup. *)
Lemma chk_g199_order : smul 199 G199 = PInf.
Proof. vm_compute. reflexivity. Qed.

(* ================================================================= *)
(** ** [comb] against its closed form -- [comb_correct]'s content, ground.

    [comb nbits s p = smul (2*(s mod 2^nbits) - (2^nbits - 1)) p]: exactly
    [model.ecmult_gen]'s [comb_correct] statement (Admitted there), checked
    here as a GROUND fact at the two extreme digit patterns of the order-13
    geometry ([nbits = 4]): [s = 0] (every digit clear, the most negative
    multiple [-(2^nbits-1) = -15]) and [s = 2^nbits-1 = 15] (every digit set,
    [+15]). Compared via [point_eqb], not [=] -- see [model/tests_group.v]'s
    [chk_pneg_involution] for why raw point equality does not
    [vm_compute]-convert across two independently-built [Fe] range proofs. *)

(** [comb 4 0 G13 = smul (-15) G13]. *)
Lemma chk_comb13_all_clear :
  point_eqb (comb 4 0 G13) (smul (2 * (0 mod 2^4) - (2^4 - 1)) G13) = true.
Proof. vm_compute. reflexivity. Qed.

(** [comb 4 15 G13 = smul 15 G13]. *)
Lemma chk_comb13_all_set :
  point_eqb (comb 4 15 G13) (smul (2 * (15 mod 2^4) - (2^4 - 1)) G13) = true.
Proof. vm_compute. reflexivity. Qed.

(** [comb 12 4095 G199 = smul 4095 G199], the order-199 geometry's
    ([nbits = 12]) all-digits-set pattern.  The [s = 0] counterpart is NOT
    also checked here: this single case already measured about 280 seconds
    ([vm_compute] plus [Qed]) on this machine, so a second one at this
    geometry would roughly double this file's cost for the same kind of
    evidence [chk_comb13_all_clear] already gives at the cheaper geometry. *)
Lemma chk_comb199_all_set :
  point_eqb (comb 12 4095 G199) (smul (2 * (4095 mod 2^12) - (2^12 - 1)) G199) = true.
Proof. vm_compute. reflexivity. Qed.

(* ================================================================= *)
(** ** The context invariant [gb_wf], instantiated at a concrete blinding
    value.

    [model.ecmult_gen]'s own [gen_blind_wf] already proves this for every
    [b]; this check picks one concrete [b] (not [-1], which
    [gen_blind_default_offsets] already exercises) and re-derives the two
    conjuncts directly rather than by invoking that lemma, so a
    transcription error in [gen_blind] itself would still show up here.  The
    second conjunct ([gb_ge_offset gb = smul b G] and the scalar-offset
    equation) is definitional -- [gen_blind]'s fields ARE [smul b G] and that
    residue by construction, so [reflexivity] closes it without forcing any
    field arithmetic at all. *)

(** [Point] equality against the proof-free [PInf] constructor, reduced to a
    boolean witness before [vm_compute] ever has to reify anything.  Proving
    [p <> PInf] directly (`vm_compute; discriminate` on the raw goal) forces
    [vm_compute] to reify the FULL WHNF of [p] back into a literal term --
    including the [Fe] pair's [Program]-generated range proofs -- so that
    [discriminate] has something to pattern-match; measured on this machine
    at over 100 seconds and past 5 GB (killed under a memory cap) for
    [smul 100 G <> PInf] alone. Routing through this boolean witness instead
    means the goal [vm_compute] actually has to reify is the tiny [true],
    while the expensive part (walking every intermediate [padd] / [pdouble] /
    [fe_inv] to decide the match) stays INSIDE the VM as machine values that
    are never converted back to source terms -- the same reason
    [model.group]'s own [point_eqb] projects out [fe_val] before comparing
    (see [model/tests_group.v]'s [chk_pneg_involution]). Measured at about 50
    seconds this way, the same order as the raw field-arithmetic cost alone. *)
Lemma point_neq_inf : forall p : Point,
  match p with PInf => false | PAff _ _ => true end = true -> p <> PInf.
Proof.
  intros p Hp Heq.
  subst p.
  discriminate Hp.
Qed.

(** [gen_blind 100]'s point offset, [smul 100 G], is not the identity -- the
    side condition [secp256k1_ecmult_gen_blind]'s cmov at
    [src/ecmult_gen_impl.h:334] establishes for every ACTUAL blinding value
    it draws (this concrete [100] stands in for "some nonzero residue mod
    the group order").  About a dozen [padd] / [pdouble] calls, ~50 seconds
    on this machine -- see the file header and [point_neq_inf] above for why
    it is not simply [vm_compute; discriminate]. *)
Lemma chk_gb_wf_100 : gb_wf (gen_blind 100).
Proof.
  split.
  - apply point_neq_inf.
    vm_compute.
    reflexivity.
  - exists 100.
    split; reflexivity.
Qed.

(* ================================================================= *)
(** ** The blinded composition -- [ecmult_gen_model_of] at order 13.

    The module's headline known-answer check: the only one that reaches the
    two steps [comb] alone never does -- the offset reduction
    [(n + off) mod order] and the final [padd] with [ge_offset]
    ([src/ecmult_gen_impl.h:100-103]).  Both [comb_correct] and
    [ecmult_gen_correct] are [Admitted], so a direction or sign slip in
    either step ([n - off] for [n + off], or [diff + b] for [diff - b])
    would otherwise be caught by nothing in this proof at all.

    Measured at 92.9 s wall standalone on this machine (46.7 s [vm_compute]
    plus 45.5 s of kernel [Qed] re-check), which is why it is in this file
    and not in [model/tests_ecmult_gen.v] with its 30 s budget. *)

(** The blinded composition at the order-13 toy geometry.  [G13/2] is
    [smul 7 G13] ([2*7 = 14 = 1] mod 13); the blinding difference at
    [nbits = 4] is [(2^4 - 1) * inv2 = 15 * 7 = 1] mod 13, so a blinding
    value [b = 2] gives [scalar_offset = 1 - 2 = 12] and
    [ge_offset = 2*G13].  Then [d = (5 + 12) mod 13 = 4],
    [comb 4 4 (G13/2) = smul (2*4 - 15) (G13/2) = smul (-7) (G13/2)], which
    is [smul 3 G13] since [-7 * 7 = -49 = 3] mod 13, and [3*G13 + 2*G13] is
    the [smul 5 G13] on the right.  Expected value derived by hand from the
    C's own equations ([src/ecmult_gen_impl.h:100-103]); the right-hand side
    reaches it by double-and-add, a different route through [model.group]
    than the comb takes. *)
Lemma chk_ecmult_gen13_blinded :
  point_eqb (ecmult_gen_model_of 4 13 (smul 7 G13) 12 (smul 2 G13) 5)
            (smul 5 G13) = true.
Proof. vm_compute. reflexivity. Qed.
