(** * Verif_scalar_reduce_512: Proof of body_secp256k1_scalar_reduce_512 *)
(** Copyright (C) 2026 remix7531
    SPDX-License-Identifier: MIT *)

Require Import secp256k1.vst.base.
Require Import secp256k1.vst.helper.structs_scalar.
Require Import secp256k1.vst.helper.notations.
Require Import secp256k1.vst.gprog.
Require Import secp256k1.vst.scalar.impl.
Require Import secp256k1.vst.tactics.core.
Require Import secp256k1.vst.tactics.int128.
Require Import secp256k1.vst.tactics.scalar.

(* ================================================================= *)
(** ** secp256k1_scalar_reduce_512 -- [r = l mod N] (two folds and a branchless tail). *)

(** Two modular folds take 512 bits to 385 and then to 258, all on one
    128-bit stack accumulator.  A branchless tail then adds [(p4 + 1) * N_C],
    reads the carry out of limb 3 as a mask and adds [N] back under that mask,
    which leaves the canonical residue in four limbs. *)

(* ----------------------------------------------------------------- *)
(** *** Helper lemmas *)
(** The lemmas below are file-local because they are tied to the concrete
    VST representation used in this proof ([UInt128] accumulators,
    [Int64.repr] masks, [uint256_to_val]) and do not generalise to an
    abstract base-B statement that would belong in theory/. *)

(** [u128_no_carry] turns the postcondition of a [*_carry] helper into a
    plain sum: when the exact sum [s] is below [2^128], the returned carry
    must be 0, because the stored accumulator [r] is non-negative. *)
Lemma u128_no_carry : forall r c s : Z,
  c = 0 \/ c = 1 ->
  0 <= r < 2^128 ->
  r + c * 2^128 = s ->
  s < 2^128 ->
  r = s.
Proof.
  intros r c s Hc Hr Heq Hs.
  lia.
Qed.

(** [u128_round_identity] is one [extract_fast] round: the low limb read by
    [secp256k1_u128_to_u64] plus the shifted accumulator left by
    [secp256k1_u128_rshift] reconstruct the accumulator. *)
Lemma u128_round_identity : forall (x : UInt128) (lo : UInt64) (carry : UInt128),
  lo = u128_lo x ->
  u128_val carry = u128_val x / 2^64 ->
  u64_val lo + u128_val carry * 2^64 = u128_val x.
Proof.
  intros x lo carry Hlo Hcarry.
  rewrite Hlo, u128_lo_val, Hcarry.
  pose proof (Z_div_mod_eq_full (u128_val x) (2^64)).
  lia.
Qed.

(** [mask_and_eq] is the mask trick of the tail: after [--p4] the mask is
    [c - 1] for a carry [c] in [{0, 1}], i.e. all ones or zero, so
    [p4 & N_i] is [N_i] or [0].  The C spells [N_i] as the signed 64-bit
    literal [z] with [z + 2^64 = N_i]. *)
Lemma mask_and_eq : forall c z n : Z,
  c = 0 \/ c = 1 ->
  z + 2^64 = n ->
  Int64.and (Int64.repr (c - 1)) (Int64.repr z) = Int64.repr ((1 - c) * n).
Proof.
  intros c z n Hc Hzn.
  assert (Hrepr : Int64.repr z = Int64.repr n).
  { apply Int64.eqm_samerepr.
    exists (-1).
    change Int64.modulus with (2^64).
    lia. }
  destruct Hc as [Hc | Hc].
  - (* c = 0: the mask is all ones and keeps N_i. *)
    subst c.
    change (Int64.repr (0 - 1)) with Int64.mone.
    rewrite Int64.and_commut, Int64.and_mone, Hrepr.
    f_equal.
    lia.
  - (* c = 1: the mask is zero. *)
    subst c.
    change (Int64.repr (1 - 1)) with Int64.zero.
    rewrite Int64.and_zero_l.
    reflexivity.
Qed.

(** [uint256_from_limbs] converts a list of four [uint64_to_val]
    projections into the canonical [uint256_to_val (mkUInt256 r_z Hr)]
    form.  It is file-local because it depends on the concrete
    [uint256_to_val] definition (which unfolds to [limb]-based splits)
    and on [limbs_eval4] from the project theory layer.  Placing it
    in tactics/ would expose the representation type to the automation
    layer, which should remain rep-agnostic. *)
Lemma uint256_from_limbs :
  forall (v0 v1 v2 v3 : UInt64),
  let r_z := u64_val v0 + u64_val v1 * 2^64
           + u64_val v2 * 2^128 + u64_val v3 * 2^192 in
  forall (Hr : 0 <= r_z < 2^256),
  [uint64_to_val v0; uint64_to_val v1;
   uint64_to_val v2; uint64_to_val v3]
  = uint256_to_val (mkUInt256 r_z Hr).
Proof.
  intros v0 v1 v2 v3 r_z Hr.
  pose proof (u64_range v0) as Hv0.
  pose proof (u64_range v1) as Hv1.
  pose proof (u64_range v2) as Hv2.
  pose proof (u64_range v3) as Hv3.
  assert (Hr_eval : r_z = eval4 (2^64) (u64_val v0) (u64_val v1) (u64_val v2) (u64_val v3)).
  { unfold eval4, r_z.
    change ((2^64)^2) with (2^128).
    change ((2^64)^3) with (2^192).
    ring. }
  pose proof (limbs_eval4 (2^64) (u64_val v0) (u64_val v1) (u64_val v2) (u64_val v3)
    ltac:(lia) Hv0 Hv1 Hv2 Hv3) as [Hl0 [Hl1 [Hl2 Hl3]]].
  rewrite <- Hr_eval in Hl0, Hl1, Hl2, Hl3.
  unfold uint256_to_val.
  simpl u256_val.
  fold_limb.
  rewrite Hl0, Hl1, Hl2, Hl3.
  unfold uint64_to_val.
  reflexivity.
Qed.

(* ----------------------------------------------------------------- *)
(** *** Stage lemmas *)
(** The lemmas below state, once each, the pure arithmetic of one folding
    stage.  They are file-local because they name this function's stage
    structure (the [N_C] limbs, the 385- and 258-bit intermediate layouts,
    the two passes of the tail) rather than a reusable base-B fact; the
    generic facts they rest on ([fold_sub_mod], [eval8_limbs]) already live
    in [theory/integers] and [theory/scalar]. *)

(** [reduce_512_stage1_mod] is Stage 1 (512 -> 385 bits): the six extract
    rounds telescope to [l_lo + l_hi * N_C], which is congruent mod [N] to
    the 8-limb input [lv] because [N_C = 2^256 - N].  [c_k] is the carry out
    of round [k] and [m_k] the limb it extracts. *)
Lemma reduce_512_stage1_mod :
  forall l0 l1 l2 l3 n0 n1 n2 n3 m0 m1 m2 m3 m4 m5
         c0 c1 c2 c3 c4 c5 lv : Z,
  eval8 (2^64) l0 l1 l2 l3 n0 n1 n2 n3 = lv ->
  m0 + c0 * 2^64 = l0 + n0 * N_C_0 ->
  m1 + c1 * 2^64 = c0 + l1 + n1 * N_C_0 + n0 * N_C_1 ->
  m2 + c2 * 2^64 = c1 + l2 + n2 * N_C_0 + n1 * N_C_1 + n0 ->
  m3 + c3 * 2^64 = c2 + l3 + n3 * N_C_0 + n2 * N_C_1 + n1 ->
  m4 + c4 * 2^64 = c3 + n3 * N_C_1 + n2 ->
  m5 + c5 * 2^64 = c4 + n3 ->
  (m0 + m1 * 2^64 + m2 * 2^128 + m3 * 2^192 + m4 * 2^256
   + m5 * 2^320 + c5 * 2^384) mod secp256k1_N = lv mod secp256k1_N.
Proof.
  intros l0 l1 l2 l3 n0 n1 n2 n3 m0 m1 m2 m3 m4 m5
    c0 c1 c2 c3 c4 c5 lv Heval Hr0 Hr1 Hr2 Hr3 Hr4 Hr5.

  (* Carry chain telescopes to lo + hi * N_C *)
  assert (Htotal : m0 + m1 * 2^64 + m2 * 2^128 + m3 * 2^192 + m4 * 2^256
    + m5 * 2^320 + c5 * 2^384
    = (l0 + l1 * 2^64 + l2 * 2^128 + l3 * 2^192)
      + (n0 + n1 * 2^64 + n2 * 2^128 + n3 * 2^192)
        * (N_C_0 + N_C_1 * 2^64 + N_C_2 * 2^128)).
  { rep_lia. }

  rewrite Htotal.
  rewrite <- secp256k1_N_C_limbs, fold_sub_mod.
  (* Goal: (lo + hi * 2^256) mod N = lv mod N *)
  f_equal.
  unfold eval8 in Heval.
  lia.
Qed.

(** [reduce_512_stage2_mod] is Stage 2 (385 -> 258 bits): the same fold one
    limb narrower, over the seven limbs [m0..m6] Stage 1 produced.  [mc] is
    the Stage 1 top carry, which the C code reads back as the limb [m6], so
    the two are equated by hypothesis; [p4] is the Stage 2 top carry plus
    [m6]. *)
Lemma reduce_512_stage2_mod :
  forall m0 m1 m2 m3 m4 m5 m6 mc p0 p1 p2 p3 p4
         c0 c1 c2 c3 lv : Z,
  p0 + c0 * 2^64 = m0 + m4 * N_C_0 ->
  p1 + c1 * 2^64 = c0 + m1 + m5 * N_C_0 + m4 * N_C_1 ->
  p2 + c2 * 2^64 = c1 + m2 + m6 * N_C_0 + m5 * N_C_1 + m4 ->
  p3 + c3 * 2^64 = c2 + m3 + m6 * N_C_1 + m5 ->
  m6 = mc ->
  p4 = c3 + m6 ->
  (m0 + m1 * 2^64 + m2 * 2^128 + m3 * 2^192 + m4 * 2^256
   + m5 * 2^320 + mc * 2^384) mod secp256k1_N = lv mod secp256k1_N ->
  (p0 + p1 * 2^64 + p2 * 2^128 + p3 * 2^192 + p4 * 2^256)
    mod secp256k1_N = lv mod secp256k1_N.
Proof.
  intros m0 m1 m2 m3 m4 m5 m6 mc p0 p1 p2 p3 p4
    c0 c1 c2 c3 lv Hr0 Hr1 Hr2 Hr3 Hm6 Hp4 Hprev.
  subst m6.
  subst p4.

  (* Carry chain telescopes to m_lo + m_hi * N_C *)
  assert (Htotal : p0 + p1 * 2^64 + p2 * 2^128 + p3 * 2^192 + (c3 + mc) * 2^256
    = (m0 + m1 * 2^64 + m2 * 2^128 + m3 * 2^192)
      + (m4 + m5 * 2^64 + mc * 2^128)
        * (N_C_0 + N_C_1 * 2^64 + N_C_2 * 2^128)).
  { rep_lia. }

  rewrite Htotal.
  rewrite <- secp256k1_N_C_limbs, fold_sub_mod, <- Hprev.
  f_equal.
  ring.
Qed.

(** [reduce_512_tail_carry] is the first pass of the tail: adding
    [(p4 + 1) * N_C] to the 258-bit value [p[0..3] + p4 * 2^256] with
    [p4 <= 3] carries at most once out of limb 3, so the carry [b3] that
    becomes the mask is 0 or 1.  [q_k] is the limb the pass writes back and
    [b_k] the shifted accumulator after it. *)
Lemma reduce_512_tail_carry :
  forall p0 p1 p2 p3 p4 q0 q1 q2 q3 b0 b1 b2 b3 : Z,
  0 <= p0 < 2^64 ->
  0 <= p1 < 2^64 ->
  0 <= p2 < 2^64 ->
  0 <= p3 < 2^64 ->
  0 <= p4 <= 3 ->
  0 <= q0 < 2^64 ->
  0 <= q1 < 2^64 ->
  0 <= q2 < 2^64 ->
  0 <= q3 < 2^64 ->
  0 <= b3 ->
  q0 + b0 * 2^64 = p0 + (p4 + 1) * N_C_0 ->
  q1 + b1 * 2^64 = b0 + p1 + (p4 + 1) * N_C_1 ->
  q2 + b2 * 2^64 = b1 + p2 + (p4 + 1) ->
  q3 + b3 * 2^64 = b2 + p3 ->
  b3 = 0 \/ b3 = 1.
Proof.
  intros p0 p1 p2 p3 p4 q0 q1 q2 q3 b0 b1 b2 b3
    Hp0 Hp1 Hp2 Hp3 Hp4 Hq0 Hq1 Hq2 Hq3 Hb3 Hr0 Hr1 Hr2 Hr3.

  (* Setup: telescope the pass; b3 * 2^256 < 2^256 + 4 * N_C < 2^257 *)
  assert (Htotal : q0 + q1 * 2^64 + q2 * 2^128 + q3 * 2^192 + b3 * 2^256
    = p0 + p1 * 2^64 + p2 * 2^128 + p3 * 2^192
      + (p4 + 1) * (N_C_0 + N_C_1 * 2^64 + 2^128)) by lia.
  clear Hr0 Hr1 Hr2 Hr3.
  unfold N_C_0, N_C_1 in Htotal.
  lia.
Qed.

(** [reduce_512_tail_core] is the arithmetic of the tail on whole numbers.
    With [R = P + p4 * N_C] (congruent to [P + p4 * 2^256], and [R < 2N]),
    the first pass leaves [Q = R + N_C] modulo [2^256] with carry [b3], and
    the second adds [N] back when [b3 = 0].  Since [N + N_C = 2^256], the
    carry is 1 exactly when [R >= N]: then [Q = R - N]; otherwise [Q + N]
    wraps to [R].  Either way the result [Rr] is [R mod N]. *)
Lemma reduce_512_tail_core : forall P p4 Q b3 Rr d3 : Z,
  0 <= P < 2^256 ->
  0 <= p4 <= 3 ->
  0 <= Q < 2^256 ->
  0 <= Rr < 2^256 ->
  b3 = 0 \/ b3 = 1 ->
  Q + b3 * 2^256 = P + (p4 + 1) * (2^256 - secp256k1_N) ->
  Rr + d3 * 2^256 = Q + (1 - b3) * secp256k1_N ->
  Rr = (P + p4 * 2^256) mod secp256k1_N.
Proof.
  intros P p4 Q b3 Rr d3 HP Hp4 HQ HRr Hb3 Hfirst Hsecond.
  rewrite secp256k1_N_unfold in *.
  destruct Hb3 as [Hb3 | Hb3].
  - (* b3 = 0: R < N, adding N wraps once and leaves Rr = R. *)
    subst b3.
    assert (Hd3 : d3 = 1) by lia.
    subst d3.
    apply (Z.mod_unique_pos _ _ p4).
    + lia.
    + lia.
  - (* b3 = 1: N <= R < 2N, the first pass already left Rr = R - N. *)
    subst b3.
    assert (Hd3 : d3 = 0) by lia.
    subst d3.
    apply (Z.mod_unique_pos _ _ (p4 + 1)).
    + lia.
    + lia.
Qed.

(** [reduce_512_tail_mod] is the tail on limbs: the first pass ([q_k],
    [b_k]) and the masked second pass ([r_k], [d_k], with the mask already
    resolved to [(1 - b3) * N_i] by [mask_and_eq]) telescope to the two
    identities of [reduce_512_tail_core]. *)
Lemma reduce_512_tail_mod :
  forall p0 p1 p2 p3 p4 q0 q1 q2 q3 b0 b1 b2 b3
         r0 r1 r2 r3 d0 d1 d2 d3 : Z,
  0 <= p0 < 2^64 ->
  0 <= p1 < 2^64 ->
  0 <= p2 < 2^64 ->
  0 <= p3 < 2^64 ->
  0 <= p4 <= 3 ->
  0 <= q0 < 2^64 ->
  0 <= q1 < 2^64 ->
  0 <= q2 < 2^64 ->
  0 <= q3 < 2^64 ->
  0 <= r0 < 2^64 ->
  0 <= r1 < 2^64 ->
  0 <= r2 < 2^64 ->
  0 <= r3 < 2^64 ->
  b3 = 0 \/ b3 = 1 ->
  q0 + b0 * 2^64 = p0 + (p4 + 1) * N_C_0 ->
  q1 + b1 * 2^64 = b0 + p1 + (p4 + 1) * N_C_1 ->
  q2 + b2 * 2^64 = b1 + p2 + (p4 + 1) ->
  q3 + b3 * 2^64 = b2 + p3 ->
  r0 + d0 * 2^64 = q0 + (1 - b3) * N_0 ->
  r1 + d1 * 2^64 = d0 + q1 + (1 - b3) * N_1 ->
  r2 + d2 * 2^64 = d1 + q2 + (1 - b3) * N_2 ->
  r3 + d3 * 2^64 = d2 + q3 + (1 - b3) * N_3 ->
  r0 + r1 * 2^64 + r2 * 2^128 + r3 * 2^192
  = (p0 + p1 * 2^64 + p2 * 2^128 + p3 * 2^192 + p4 * 2^256)
      mod secp256k1_N.
Proof.
  intros p0 p1 p2 p3 p4 q0 q1 q2 q3 b0 b1 b2 b3 r0 r1 r2 r3 d0 d1 d2 d3
    Hp0 Hp1 Hp2 Hp3 Hp4 Hq0 Hq1 Hq2 Hq3 Hr0 Hr1 Hr2 Hr3 Hb3
    Hf0 Hf1 Hf2 Hf3 Hs0 Hs1 Hs2 Hs3.

  (* Setup: telescope each pass into one identity on whole numbers *)
  assert (Hfirst : q0 + q1 * 2^64 + q2 * 2^128 + q3 * 2^192 + b3 * 2^256
    = p0 + p1 * 2^64 + p2 * 2^128 + p3 * 2^192
      + (p4 + 1) * (2^256 - secp256k1_N)).
  { rewrite secp256k1_N_C_limbs.
    unfold N_C_2.
    lia. }
  assert (Hsecond : r0 + r1 * 2^64 + r2 * 2^128 + r3 * 2^192 + d3 * 2^256
    = q0 + q1 * 2^64 + q2 * 2^128 + q3 * 2^192 + (1 - b3) * secp256k1_N).
  { rewrite secp256k1_N_limbs.
    destruct Hb3 as [Hb3 | Hb3];
      subst b3;
      lia. }

  (* Main: the whole-number argument; the remaining premises are limb ranges *)
  apply (reduce_512_tail_core _ p4 (q0 + q1 * 2^64 + q2 * 2^128 + q3 * 2^192) b3 _ d3);
    first [exact Hfirst | exact Hsecond | exact Hb3 | lia].
Qed.

(* ----------------------------------------------------------------- *)
(** *** Local tactics *)
(** Every accumulator step is a [forward_call] on the stack [acc] followed by
    the same bookkeeping, so it is bundled here.  An accumulator value is
    always tracked as one equation [Hacc : u128_val acc = E] in terms of the
    previous round's carry and the inputs; a step folds [Hacc] into the new
    equation and clears the old accumulator.  The [_first] variants start a
    round from a carry, whose value is given by the round identity instead
    of an equation, so they neither fold nor clear. *)

(** [secp256k1_u128_from_u64(&acc, a)]: [init(a)]. *)
Ltac forward_call_acc_init acc_ptr a acc' Hacc' :=
  forward_call (acc_ptr, a, Tsh);
  [ try solve_param_match ..
  | Intros acc';
    match goal with H : u128_val acc' = _ |- _ => rename H into Hacc' end;
    rewrite ?u64_val_mk in Hacc';
    try deadvars! ].

(** Name the result of a [*_carry] helper.  Its return value lands in a
    [carry] temp that the C discards ([(void)carry]); when the call is the
    last statement of its block, that copy is a separate [Sset], which is
    stepped over here so [deadvars!] can drop both temps. *)
Ltac intros_carry acc' c Hc Hraw :=
  let vret := fresh "vret" in
  Intros vret;
  destruct vret as [acc' c];
  simpl fst in *;
  simpl snd in *;
  lazymatch goal with
  | |- semax _ _ (Ssequence (Sset _ (Etempvar _ tint)) _) _ => forward
  | _ => idtac
  end;
  match goal with H : c = 0 \/ c = 1 |- _ => rename H into Hc end;
  match goal with H : (u128_val acc' + c * 2^128)%Z = _ |- _ => rename H into Hraw end;
  rewrite ?u64_val_mk, ?u64_val_N_C_0_u64, ?u64_val_N_C_1_u64 in Hraw;
  try deadvars!.

(** Discharge the carry with [u128_no_carry]: [rep_lia] proves the exact
    sum is below [2^128] from the accumulator equation and carry bounds in
    context.  This is where each [muladd_fast] / [sumadd_fast] is shown not
    to overflow the 128-bit accumulator ([N_C_0], [N_C_1] < 2^63 keep every
    partial sum near [0.52 * 2^128]). *)
Ltac drop_carry acc' c Hc Hraw Hacc' :=
  match type of Hraw with
  | _ = ?s =>
      assert (Hacc' : u128_val acc' = s)
        by (apply (u128_no_carry _ c); [exact Hc | apply u128_range | exact Hraw | rep_lia])
  end;
  clear c Hc Hraw.

Ltac close_carry acc acc' Hacc Hacc' :=
  let c := fresh "c" in
  let Hc := fresh "Hc" in
  let Hraw := fresh "Hraw" in
  intros_carry acc' c Hc Hraw;
  rewrite Hacc in Hraw;
  drop_carry acc' c Hc Hraw Hacc';
  clear Hacc acc.

Ltac close_carry_first acc' Hacc' :=
  let c := fresh "c" in
  let Hc := fresh "Hc" in
  let Hraw := fresh "Hraw" in
  intros_carry acc' c Hc Hraw;
  drop_carry acc' c Hc Hraw Hacc'.

(** [muladd_fast(a, b)] = [secp256k1_u128_accum_mul_carry(&acc, a, b)]. *)
Ltac forward_call_mul_carry acc_ptr acc Hacc a b acc' Hacc' :=
  forward_call (acc_ptr, acc, a, b, Tsh);
  [ try solve_param_match .. | close_carry acc acc' Hacc Hacc' ].

Ltac forward_call_mul_carry_first acc_ptr acc a b acc' Hacc' :=
  forward_call (acc_ptr, acc, a, b, Tsh);
  [ try solve_param_match .. | close_carry_first acc' Hacc' ].

(** [sumadd_fast(a)] = [secp256k1_u128_accum_u64_carry(&acc, a)]. *)
Ltac forward_call_add_carry acc_ptr acc Hacc a acc' Hacc' :=
  forward_call (acc_ptr, acc, a, Tsh);
  [ try solve_param_match .. | close_carry acc acc' Hacc Hacc' ].

Ltac forward_call_add_carry_first acc_ptr acc a acc' Hacc' :=
  forward_call (acc_ptr, acc, a, Tsh);
  [ try solve_param_match .. | close_carry_first acc' Hacc' ].

(** [extract_fast(lo)] = [lo = secp256k1_u128_to_u64(&acc);
    secp256k1_u128_rshift(&acc, 64)]: leaves the round identity
    [Hround : u64_val lo + u128_val carry * 2^64 = E]. *)
Ltac forward_call_acc_extract acc_ptr acc Hacc lo carry Hround :=
  let Hlo := fresh "Hlo" in
  let Hcarry := fresh "Hcarry" in
  forward_call (acc_ptr, acc, Tsh);
  [ ..
  | Intros lo;
    match goal with H : lo = u128_lo acc |- _ => rename H into Hlo end;
    forward_call (acc_ptr, acc, 64, Tsh);
    [ try (simpl; rep_lia) ..
    | Intros carry;
      match goal with H : u128_val carry = _ |- _ => rename H into Hcarry end;
      pose proof (u128_round_identity acc lo carry Hlo Hcarry) as Hround;
      rewrite Hacc in Hround;
      clear Hlo Hcarry Hacc acc;
      try deadvars! ] ].

(** [secp256k1_u128_accum_u64(&acc, a)] in the tail, whose no-overflow
    precondition [rep_lia] proves from the accumulator equation. *)
Ltac forward_call_add acc_ptr acc Hacc a acc' Hacc' :=
  forward_call (acc_ptr, acc, a, Tsh);
  [ first [solve_param_match | rewrite Hacc; rep_lia] ..
  | Intros acc';
    match goal with H : u128_val acc' = _ |- _ => rename H into Hacc' end;
    rewrite ?u64_val_mk in Hacc';
    rewrite Hacc in Hacc';
    clear Hacc acc;
    try deadvars! ].

Ltac forward_call_add_first acc_ptr acc a acc' Hacc' :=
  forward_call (acc_ptr, acc, a, Tsh);
  [ first [solve_param_match | rep_lia] ..
  | Intros acc';
    match goal with H : u128_val acc' = _ |- _ => rename H into Hacc' end;
    rewrite ?u64_val_mk in Hacc';
    try deadvars! ].

(** [secp256k1_u128_accum_mul(&acc, a, b)] at the start of a tail round. *)
Ltac forward_call_mul_first acc_ptr acc a b acc' Hacc' :=
  forward_call (acc_ptr, acc, a, b, Tsh);
  [ first [solve_param_match | rep_lia] ..
  | Intros acc';
    match goal with H : u128_val acc' = _ |- _ => rename H into Hacc' end;
    rewrite ?u64_val_mk, ?u64_val_N_C_1_u64 in Hacc';
    try deadvars! ].

(** [secp256k1_u128_accum_u64(&acc, p4 & N_i)]: the argument goal is closed
    by [Harg], which states the masked C value as [uint64_to_val a]. *)
Ltac forward_call_add_mask acc_ptr acc Hacc a Harg acc' Hacc' :=
  forward_call (acc_ptr, acc, a, Tsh);
  [ first [apply prop_right; rewrite Harg; reflexivity | rewrite Hacc; rep_lia] ..
  | Intros acc';
    match goal with H : u128_val acc' = _ |- _ => rename H into Hacc' end;
    rewrite ?u64_val_mk in Hacc';
    rewrite Hacc in Hacc';
    clear Hacc acc;
    try deadvars! ].

(* ----------------------------------------------------------------- *)
(** *** Main proof *)

Lemma body_secp256k1_scalar_reduce_512:
  semax_body Vprog Gprog
    f_secp256k1_scalar_reduce_512 spec_secp256k1_scalar_reduce_512.
Proof.
  start_function.
  rename SH into Hsh_r_writable.
  rename SH0 into Hsh_l_readable.

  (* ===== Stage 0: Setup -- name the eight input limbs ===== *)

  assert_PROP (field_compatible (tarray tulong 8) [] l_ptr) as Hfc
    by entailer!.

  set (l0 := limb (2^64) (u512_val l) 0).
  set (l1 := limb (2^64) (u512_val l) 1).
  set (l2 := limb (2^64) (u512_val l) 2).
  set (l3 := limb (2^64) (u512_val l) 3).
  set (n0 := limb (2^64) (u512_val l) 4).
  set (n1 := limb (2^64) (u512_val l) 5).
  set (n2 := limb (2^64) (u512_val l) 6).
  set (n3 := limb (2^64) (u512_val l) 7).

  assert (Hl0 : 0 <= l0 < 2^64) by (subst l0; apply Z.mod_pos_bound; lia).
  assert (Hl1 : 0 <= l1 < 2^64) by (subst l1; apply Z.mod_pos_bound; lia).
  assert (Hl2 : 0 <= l2 < 2^64) by (subst l2; apply Z.mod_pos_bound; lia).
  assert (Hl3 : 0 <= l3 < 2^64) by (subst l3; apply Z.mod_pos_bound; lia).
  assert (Hn0 : 0 <= n0 < 2^64) by (subst n0; apply Z.mod_pos_bound; lia).
  assert (Hn1 : 0 <= n1 < 2^64) by (subst n1; apply Z.mod_pos_bound; lia).
  assert (Hn2 : 0 <= n2 < 2^64) by (subst n2; apply Z.mod_pos_bound; lia).
  assert (Hn3 : 0 <= n3 < 2^64) by (subst n3; apply Z.mod_pos_bound; lia).

  (* Inhabitant for Scalar -- needed by deadvars! *)
  assert (Inh_Scalar : Scalar)
    by exact (mkScalar 0 ltac:(unfold secp256k1_N; lia)).

  (* n0 = l[4] *)
  forward.

  (* n1 = l[5] *)
  forward.

  (* n2 = l[6] *)
  forward.

  (* n3 = l[7] *)
  forward.

  (* ===== Stage 1, Round 0: init(l[0]); muladd_fast(n0, N_C_0); extract_fast(m0) ===== *)
  (* m[0..6] = l[0..3] + n[0..3] * SECP256K1_N_C, every partial sum below 2^128 *)

  forward. (* _t'51 = l[0] *)

  (* init(l[0]) *)
  forward_call_acc_init v_acc (mkUInt64 l0 Hl0) acc_s1_init Hacc_s1_init.

  (* muladd_fast(n0, SECP256K1_N_C_0) *)
  forward_call_mul_carry v_acc acc_s1_init Hacc_s1_init
    (mkUInt64 n0 Hn0) N_C_0_u64 acc_s1_0 Hacc_s1_0.

  (* extract_fast(m0) *)
  forward_call_acc_extract v_acc acc_s1_0 Hacc_s1_0 m0 carry_s1_0 HR_s1_0.
  assert (Hcarry_s1_0_ub : u128_val carry_s1_0 <= N_C_0) by rep_lia.

  (* ===== Stage 1, Round 1: sumadd_fast(l[1]); muladd_fast(n1, N_C_0); muladd_fast(n0, N_C_1) ===== *)

  forward. (* _t'50 = l[1] *)

  (* sumadd_fast(l[1]) *)
  forward_call_add_carry_first v_acc carry_s1_0 (mkUInt64 l1 Hl1) acc_s1_1a Hacc_s1_1a.

  (* muladd_fast(n1, SECP256K1_N_C_0) *)
  forward_call_mul_carry v_acc acc_s1_1a Hacc_s1_1a
    (mkUInt64 n1 Hn1) N_C_0_u64 acc_s1_1b Hacc_s1_1b.

  (* muladd_fast(n0, SECP256K1_N_C_1) *)
  forward_call_mul_carry v_acc acc_s1_1b Hacc_s1_1b
    (mkUInt64 n0 Hn0) N_C_1_u64 acc_s1_1 Hacc_s1_1.

  (* extract_fast(m1) *)
  forward_call_acc_extract v_acc acc_s1_1 Hacc_s1_1 m1 carry_s1_1 HR_s1_1.
  assert (Hcarry_s1_1_ub : u128_val carry_s1_1 <= N_C_0 + N_C_1) by rep_lia.

  (* ===== Stage 1, Round 2: sumadd_fast(l[2]); muladd_fast(n2, N_C_0); muladd_fast(n1, N_C_1); sumadd_fast(n0) ===== *)

  forward. (* _t'49 = l[2] *)

  (* sumadd_fast(l[2]) *)
  forward_call_add_carry_first v_acc carry_s1_1 (mkUInt64 l2 Hl2) acc_s1_2a Hacc_s1_2a.

  (* muladd_fast(n2, SECP256K1_N_C_0) *)
  forward_call_mul_carry v_acc acc_s1_2a Hacc_s1_2a
    (mkUInt64 n2 Hn2) N_C_0_u64 acc_s1_2b Hacc_s1_2b.

  (* muladd_fast(n1, SECP256K1_N_C_1) *)
  forward_call_mul_carry v_acc acc_s1_2b Hacc_s1_2b
    (mkUInt64 n1 Hn1) N_C_1_u64 acc_s1_2c Hacc_s1_2c.

  (* sumadd_fast(n0) *)
  forward_call_add_carry v_acc acc_s1_2c Hacc_s1_2c (mkUInt64 n0 Hn0) acc_s1_2 Hacc_s1_2.

  (* extract_fast(m2) *)
  forward_call_acc_extract v_acc acc_s1_2 Hacc_s1_2 m2 carry_s1_2 HR_s1_2.
  assert (Hcarry_s1_2_ub : u128_val carry_s1_2 <= N_C_0 + N_C_1 + 1) by rep_lia.

  (* ===== Stage 1, Round 3: sumadd_fast(l[3]); muladd_fast(n3, N_C_0); muladd_fast(n2, N_C_1); sumadd_fast(n1) ===== *)

  forward. (* _t'48 = l[3] *)

  (* sumadd_fast(l[3]) *)
  forward_call_add_carry_first v_acc carry_s1_2 (mkUInt64 l3 Hl3) acc_s1_3a Hacc_s1_3a.

  (* muladd_fast(n3, SECP256K1_N_C_0) *)
  forward_call_mul_carry v_acc acc_s1_3a Hacc_s1_3a
    (mkUInt64 n3 Hn3) N_C_0_u64 acc_s1_3b Hacc_s1_3b.

  (* muladd_fast(n2, SECP256K1_N_C_1) *)
  forward_call_mul_carry v_acc acc_s1_3b Hacc_s1_3b
    (mkUInt64 n2 Hn2) N_C_1_u64 acc_s1_3c Hacc_s1_3c.

  (* sumadd_fast(n1) *)
  forward_call_add_carry v_acc acc_s1_3c Hacc_s1_3c (mkUInt64 n1 Hn1) acc_s1_3 Hacc_s1_3.

  (* extract_fast(m3) *)
  forward_call_acc_extract v_acc acc_s1_3 Hacc_s1_3 m3 carry_s1_3 HR_s1_3.
  assert (Hcarry_s1_3_ub : u128_val carry_s1_3 <= N_C_0 + N_C_1 + 1) by rep_lia.

  (* ===== Stage 1, Round 4: muladd_fast(n3, N_C_1); sumadd_fast(n2); extract_fast(m4) ===== *)

  (* muladd_fast(n3, SECP256K1_N_C_1) *)
  forward_call_mul_carry_first v_acc carry_s1_3
    (mkUInt64 n3 Hn3) N_C_1_u64 acc_s1_4a Hacc_s1_4a.

  (* sumadd_fast(n2) *)
  forward_call_add_carry v_acc acc_s1_4a Hacc_s1_4a (mkUInt64 n2 Hn2) acc_s1_4 Hacc_s1_4.

  (* extract_fast(m4) *)
  forward_call_acc_extract v_acc acc_s1_4 Hacc_s1_4 m4 carry_s1_4 HR_s1_4.
  assert (Hcarry_s1_4_ub : u128_val carry_s1_4 <= N_C_1 + 1) by rep_lia.

  (* ===== Stage 1, Round 5: sumadd_fast(n3); extract_fast(m5) ===== *)

  (* sumadd_fast(n3) *)
  forward_call_add_carry_first v_acc carry_s1_4 (mkUInt64 n3 Hn3) acc_s1_5 Hacc_s1_5.

  (* extract_fast(m5) *)
  forward_call_acc_extract v_acc acc_s1_5 Hacc_s1_5 m5 carry_s1_5 HR_s1_5.
  assert (Hcarry_s1_5_ub : u128_val carry_s1_5 <= 1) by rep_lia.

  (* ===== Stage 1, Round 6: extract_fast(m6) into the uint32_t m6 ===== *)

  (* VST's forward_call only fuses a call with a following cast when the
     cast is neutral; uint64_t -> uint32_t is not, so the call is brought to
     the head of the sequence and the cast is stepped separately. *)
  rewrite <- seq_assoc.
  rewrite <- seq_assoc.

  (* _t'22 = secp256k1_u128_to_u64(&acc) *)
  forward_call (v_acc, carry_s1_5, Tsh).
  Intros m6_lo.
  rename H into Hm6_lo.

  (* m6 = (uint32_t)_t'22 -- exact, since the Stage 1 top carry is at most 1 *)
  forward.
  assert (Hm6_val : Int64.unsigned (Int64.repr (u64_val m6_lo)) = u128_val carry_s1_5).
  { rewrite Int64.unsigned_repr by rep_lia.
    rewrite Hm6_lo, u128_lo_val.
    apply Z.mod_small.
    rep_lia. }
  rewrite Hm6_val.
  clear Hm6_val.

  (* secp256k1_u128_rshift(&acc, 64) *)
  forward_call (v_acc, carry_s1_5, 64, Tsh).
  Intros carry_s1_6.
  clear H.
  deadvars!.
  clear Hm6_lo m6_lo.

  (* Stage 1 congruence: the seven limbs m0..m6 are l mod N *)
  assert (Hstage1_mod :
    (u64_val m0 + u64_val m1 * 2^64 + u64_val m2 * 2^128
     + u64_val m3 * 2^192 + u64_val m4 * 2^256
     + u64_val m5 * 2^320 + u128_val carry_s1_5 * 2^384)
    mod secp256k1_N = u512_val l mod secp256k1_N).
  { pose proof (eval8_limbs (2^64) (u512_val l) ltac:(lia)
      ltac:(change ((2^64)^8) with (2^512); exact (u512_range l))) as He8.
    fold l0 l1 l2 l3 n0 n1 n2 n3 in He8.
    eapply reduce_512_stage1_mod; eassumption. }

  (* ===== Stage 2, Round 0: init(m0); muladd_fast(m4, N_C_0); extract_fast(p0) ===== *)
  (* p[0..4] = m[0..3] + m[4..6] * SECP256K1_N_C *)

  (* init(m0) -- overwrites the spent Stage 1 accumulator *)
  forward_call_acc_init v_acc m0 acc_s2_init Hacc_s2_init.
  clear carry_s1_6.

  (* muladd_fast(m4, SECP256K1_N_C_0) *)
  forward_call_mul_carry v_acc acc_s2_init Hacc_s2_init m4 N_C_0_u64 acc_s2_0 Hacc_s2_0.

  (* extract_fast(p0) *)
  forward_call_acc_extract v_acc acc_s2_0 Hacc_s2_0 p0 carry_s2_0 HR_s2_0.
  assert (Hcarry_s2_0_ub : u128_val carry_s2_0 <= N_C_0) by rep_lia.

  (* ===== Stage 2, Round 1: sumadd_fast(m1); muladd_fast(m5, N_C_0); muladd_fast(m4, N_C_1) ===== *)

  (* sumadd_fast(m1) *)
  forward_call_add_carry_first v_acc carry_s2_0 m1 acc_s2_1a Hacc_s2_1a.

  (* muladd_fast(m5, SECP256K1_N_C_0) *)
  forward_call_mul_carry v_acc acc_s2_1a Hacc_s2_1a m5 N_C_0_u64 acc_s2_1b Hacc_s2_1b.

  (* muladd_fast(m4, SECP256K1_N_C_1) *)
  forward_call_mul_carry v_acc acc_s2_1b Hacc_s2_1b m4 N_C_1_u64 acc_s2_1 Hacc_s2_1.

  (* extract_fast(p1) *)
  forward_call_acc_extract v_acc acc_s2_1 Hacc_s2_1 p1 carry_s2_1 HR_s2_1.
  assert (Hcarry_s2_1_ub : u128_val carry_s2_1 <= N_C_0 + N_C_1) by rep_lia.

  (* ===== Stage 2, Round 2: sumadd_fast(m2); muladd_fast(m6, N_C_0); muladd_fast(m5, N_C_1); sumadd_fast(m4) ===== *)

  (* sumadd_fast(m2) *)
  forward_call_add_carry_first v_acc carry_s2_1 m2 acc_s2_2a Hacc_s2_2a.

  (* m6 widens back to uint64_t at each use; its value is the Stage 1 top carry *)
  assert (Hm6_range : 0 <= u128_val carry_s1_5 < 2^64) by rep_lia.

  (* muladd_fast(m6, SECP256K1_N_C_0) *)
  forward_call_mul_carry v_acc acc_s2_2a Hacc_s2_2a
    (mkUInt64 (u128_val carry_s1_5) Hm6_range) N_C_0_u64 acc_s2_2b Hacc_s2_2b.

  (* muladd_fast(m5, SECP256K1_N_C_1) *)
  forward_call_mul_carry v_acc acc_s2_2b Hacc_s2_2b m5 N_C_1_u64 acc_s2_2c Hacc_s2_2c.

  (* sumadd_fast(m4) *)
  forward_call_add_carry v_acc acc_s2_2c Hacc_s2_2c m4 acc_s2_2 Hacc_s2_2.

  (* extract_fast(p2) *)
  forward_call_acc_extract v_acc acc_s2_2 Hacc_s2_2 p2 carry_s2_2 HR_s2_2.
  assert (Hcarry_s2_2_ub : u128_val carry_s2_2 <= N_C_0 + N_C_1 + 1) by rep_lia.

  (* ===== Stage 2, Round 3: sumadd_fast(m3); muladd_fast(m6, N_C_1); sumadd_fast(m5) ===== *)

  (* sumadd_fast(m3) *)
  forward_call_add_carry_first v_acc carry_s2_2 m3 acc_s2_3a Hacc_s2_3a.

  (* muladd_fast(m6, SECP256K1_N_C_1) *)
  forward_call_mul_carry v_acc acc_s2_3a Hacc_s2_3a
    (mkUInt64 (u128_val carry_s1_5) Hm6_range) N_C_1_u64 acc_s2_3b Hacc_s2_3b.

  (* sumadd_fast(m5) *)
  forward_call_add_carry v_acc acc_s2_3b Hacc_s2_3b m5 acc_s2_3 Hacc_s2_3.

  (* extract_fast(p3) *)
  forward_call_acc_extract v_acc acc_s2_3 Hacc_s2_3 p3 carry_s2_3 HR_s2_3.
  assert (Hcarry_s2_3_ub : u128_val carry_s2_3 <= 2) by rep_lia.

  (* ===== Stage 2, Round 4: extract_fast(p4); p4 += m6 ===== *)

  (* _t'38 = secp256k1_u128_to_u64(&acc); p4 = _t'38 *)
  forward_call (v_acc, carry_s2_3, Tsh).
  Intros p4_lo.
  rename H into Hp4_lo.

  (* secp256k1_u128_rshift(&acc, 64) *)
  forward_call (v_acc, carry_s2_3, 64, Tsh).
  Intros carry_s2_4.
  rename H into Hcarry_s2_4.

  (* p4 += m6 *)
  forward.

  (* ++p4 -- the tail adds (p4 + 1) * N_C *)
  forward.

  assert (Hp4_eq :
    Int64.add
      (Int64.add (Int64.repr (u64_val p4_lo))
         (Int64.repr (Int.unsigned (Int.repr (u128_val carry_s1_5)))))
      (Int64.repr (Int.signed (Int.repr 1)))
    = Int64.repr (u128_val carry_s2_3 + u128_val carry_s1_5 + 1)).
  { rewrite Int.unsigned_repr by rep_lia.
    change (Int.signed (Int.repr 1)) with 1.
    rewrite !add64_repr.
    rewrite Hp4_lo, u128_lo_val, Z.mod_small by rep_lia.
    reflexivity. }
  rewrite Hp4_eq.
  clear Hp4_eq.
  deadvars!.
  clear Hp4_lo p4_lo Hcarry_s2_4.

  (* Stage 2 congruence: p[0..3] + p4 * 2^256 is l mod N *)
  assert (Hstage2_mod :
    (u64_val p0 + u64_val p1 * 2^64 + u64_val p2 * 2^128 + u64_val p3 * 2^192
     + (u128_val carry_s2_3 + u128_val carry_s1_5) * 2^256)
    mod secp256k1_N = u512_val l mod secp256k1_N).
  { eapply (reduce_512_stage2_mod _ _ _ _ _ _
      (u128_val carry_s1_5) (u128_val carry_s1_5));
      try eassumption;
      reflexivity. }

  assert (Hp4_range : 0 <= u128_val carry_s2_3 + u128_val carry_s1_5 <= 3) by rep_lia.
  remember (u128_val carry_s2_3 + u128_val carry_s1_5) as p4v eqn:Hp4v.

  (* --- Clear Stages 1 and 2, keep only the 258-bit value and its congruence --- *)
  clear - Hsh_r_writable Hsh_l_readable Hfc Inh_Scalar
          p0 p1 p2 p3 p4v Hp4_range Hstage2_mod.

  assert (Hq_range : 0 <= p4v + 1 < 2^64) by lia.

  (* ===== Stage 3, first pass, Round 0: acc = p4 * N_C_0 + p0 ===== *)
  (* p[0..3] + p4 * N_C, i.e. R + N_C, with the carry out of limb 3 left in p4 *)

  (* secp256k1_u128_mul(&acc, p4, SECP256K1_N_C_0) *)
  forward_call (v_acc, mkUInt64 (p4v + 1) Hq_range, N_C_0_u64, Tsh).
  Intros t0.
  assert (Ht0 : u128_val t0 = (p4v + 1) * N_C_0) by (rewrite H; reflexivity).
  clear H carry_s2_4.

  (* secp256k1_u128_accum_u64(&acc, p0) *)
  forward_call_add v_acc t0 Ht0 p0 t0a Ht0a.

  (* p0 = secp256k1_u128_to_u64(&acc); secp256k1_u128_rshift(&acc, 64) *)
  forward_call_acc_extract v_acc t0a Ht0a q0 b0 HT0.

  (* ===== Stage 3, first pass, Round 1: acc += p4 * N_C_1 + p1 ===== *)

  (* secp256k1_u128_accum_mul(&acc, p4, SECP256K1_N_C_1) *)
  forward_call_mul_first v_acc b0 (mkUInt64 (p4v + 1) Hq_range) N_C_1_u64 t1 Ht1.

  (* secp256k1_u128_accum_u64(&acc, p1) *)
  forward_call_add v_acc t1 Ht1 p1 t1a Ht1a.

  (* p1 = secp256k1_u128_to_u64(&acc); secp256k1_u128_rshift(&acc, 64) *)
  forward_call_acc_extract v_acc t1a Ht1a q1 b1 HT1.

  (* ===== Stage 3, first pass, Round 2: acc += p4 + p2 (N_C_2 = 1) ===== *)

  (* secp256k1_u128_accum_u64(&acc, p4) *)
  forward_call_add_first v_acc b1 (mkUInt64 (p4v + 1) Hq_range) t2 Ht2.

  (* secp256k1_u128_accum_u64(&acc, p2) *)
  forward_call_add v_acc t2 Ht2 p2 t2a Ht2a.

  (* p2 = secp256k1_u128_to_u64(&acc); secp256k1_u128_rshift(&acc, 64) *)
  forward_call_acc_extract v_acc t2a Ht2a q2 b2 HT2.

  (* ===== Stage 3, first pass, Round 3: acc += p3; p4 = carry ===== *)

  (* secp256k1_u128_accum_u64(&acc, p3) *)
  forward_call_add_first v_acc b2 p3 t3 Ht3.

  (* p3 = secp256k1_u128_to_u64(&acc); secp256k1_u128_rshift(&acc, 64) *)
  forward_call_acc_extract v_acc t3 Ht3 q3 b3 HT3.

  (* p4 = secp256k1_u128_to_u64(&acc) *)
  forward_call (v_acc, b3, Tsh).
  Intros c_lo.
  rename H into Hc_lo.

  assert (Hc_val : u64_val c_lo = u128_val b3).
  { rewrite Hc_lo, u128_lo_val.
    apply Z.mod_small.
    rep_lia. }
  assert (Hb3 : u128_val b3 = 0 \/ u128_val b3 = 1).
  { apply (reduce_512_tail_carry (u64_val p0) (u64_val p1) (u64_val p2) (u64_val p3)
      p4v (u64_val q0) (u64_val q1) (u64_val q2) (u64_val q3)
      (u128_val b0) (u128_val b1) (u128_val b2) (u128_val b3));
      rep_lia. }

  (* ===== Stage 3, second pass, Round 0: --p4; acc = p0 + (p4 & N_0) ===== *)
  (* p[0..3] + N if the first pass did not carry, else p[0..3], modulo 2^256 *)

  (* --p4 -- all ones for carry 0, zero for carry 1 *)
  forward.
  assert (Hmask :
    Int64.sub (Int64.repr (u64_val c_lo)) (Int64.repr (Int.signed (Int.repr 1)))
    = Int64.repr (u128_val b3 - 1)).
  { change (Int.signed (Int.repr 1)) with 1.
    rewrite sub64_repr, Hc_val.
    reflexivity. }
  rewrite Hmask.
  clear Hmask.
  try deadvars!.
  clear Hc_val Hc_lo c_lo.

  (* secp256k1_u128_from_u64(&acc, p0) *)
  forward_call_acc_init v_acc q0 s0 Hs0.

  assert (HM0 : 0 <= (1 - u128_val b3) * N_0 < 2^64)
    by (destruct Hb3 as [Hz | Hz]; rewrite Hz; rep_lia).
  assert (Harg0 : uint64_to_val (mkUInt64 ((1 - u128_val b3) * N_0) HM0)
    = Vlong (Int64.and (Int64.repr (u128_val b3 - 1))
                       (Int64.repr (-4624529908474429119)))).
  { unfold uint64_to_val.
    rewrite u64_val_mk.
    rewrite (mask_and_eq _ _ N_0 Hb3) by rep_lia.
    reflexivity. }

  (* secp256k1_u128_accum_u64(&acc, p4 & SECP256K1_N_0) *)
  forward_call_add_mask v_acc s0 Hs0
    (mkUInt64 ((1 - u128_val b3) * N_0) HM0) Harg0 s0a Hs0a.

  (* p0 = secp256k1_u128_to_u64(&acc); secp256k1_u128_rshift(&acc, 64) *)
  forward_call_acc_extract v_acc s0a Hs0a r0 d0 HS0.

  (* ===== Stage 3, second pass, Round 1: acc += p1 + (p4 & N_1) ===== *)

  (* secp256k1_u128_accum_u64(&acc, p1) *)
  forward_call_add_first v_acc d0 q1 s1 Hs1.

  assert (HM1 : 0 <= (1 - u128_val b3) * N_1 < 2^64)
    by (destruct Hb3 as [Hz | Hz]; rewrite Hz; rep_lia).
  assert (Harg1 : uint64_to_val (mkUInt64 ((1 - u128_val b3) * N_1) HM1)
    = Vlong (Int64.and (Int64.repr (u128_val b3 - 1))
                       (Int64.repr (-4994812053365940165)))).
  { unfold uint64_to_val.
    rewrite u64_val_mk.
    rewrite (mask_and_eq _ _ N_1 Hb3) by rep_lia.
    reflexivity. }

  (* secp256k1_u128_accum_u64(&acc, p4 & SECP256K1_N_1) *)
  forward_call_add_mask v_acc s1 Hs1
    (mkUInt64 ((1 - u128_val b3) * N_1) HM1) Harg1 s1a Hs1a.

  (* p1 = secp256k1_u128_to_u64(&acc); secp256k1_u128_rshift(&acc, 64) *)
  forward_call_acc_extract v_acc s1a Hs1a r1 d1 HS1.

  (* ===== Stage 3, second pass, Round 2: acc += p2 + (p4 & N_2) ===== *)

  (* secp256k1_u128_accum_u64(&acc, p2) *)
  forward_call_add_first v_acc d1 q2 s2 Hs2.

  assert (HM2 : 0 <= (1 - u128_val b3) * N_2 < 2^64)
    by (destruct Hb3 as [Hz | Hz]; rewrite Hz; rep_lia).
  assert (Harg2 : uint64_to_val (mkUInt64 ((1 - u128_val b3) * N_2) HM2)
    = Vlong (Int64.and (Int64.repr (u128_val b3 - 1)) (Int64.repr (-2)))).
  { unfold uint64_to_val.
    rewrite u64_val_mk.
    rewrite (mask_and_eq _ _ N_2 Hb3) by rep_lia.
    reflexivity. }

  (* secp256k1_u128_accum_u64(&acc, p4 & SECP256K1_N_2) *)
  forward_call_add_mask v_acc s2 Hs2
    (mkUInt64 ((1 - u128_val b3) * N_2) HM2) Harg2 s2a Hs2a.

  (* p2 = secp256k1_u128_to_u64(&acc); secp256k1_u128_rshift(&acc, 64) *)
  forward_call_acc_extract v_acc s2a Hs2a r2 d2 HS2.

  (* ===== Stage 3, second pass, Round 3: acc += p3 + (p4 & N_3), final carry discarded ===== *)

  (* secp256k1_u128_accum_u64(&acc, p3) *)
  forward_call_add_first v_acc d2 q3 s3 Hs3.

  assert (HM3 : 0 <= (1 - u128_val b3) * N_3 < 2^64)
    by (destruct Hb3 as [Hz | Hz]; rewrite Hz; rep_lia).
  assert (Harg3 : uint64_to_val (mkUInt64 ((1 - u128_val b3) * N_3) HM3)
    = Vlong (Int64.and (Int64.repr (u128_val b3 - 1)) (Int64.repr (-1)))).
  { unfold uint64_to_val.
    rewrite u64_val_mk.
    rewrite (mask_and_eq _ _ N_3 Hb3) by rep_lia.
    reflexivity. }

  (* secp256k1_u128_accum_u64(&acc, p4 & SECP256K1_N_3) *)
  forward_call_add_mask v_acc s3 Hs3
    (mkUInt64 ((1 - u128_val b3) * N_3) HM3) Harg3 s3a Hs3a.

  (* p3 = secp256k1_u128_to_u64(&acc); secp256k1_u128_rshift(&acc, 64) *)
  forward_call_acc_extract v_acc s3a Hs3a r3 d3 HS3.

  (* ===== Stores: r->d[i] = p_i ===== *)

  (* r->d[0] = p0 *)
  forward.

  (* r->d[1] = p1 *)
  forward.

  (* r->d[2] = p2 *)
  forward.

  (* r->d[3] = p3 *)
  forward.

  (* ===== Postcondition: r = l mod N ===== *)

  (* Both passes of the tail, then the Stage 2 congruence *)
  assert (Hresult :
    u64_val r0 + u64_val r1 * 2^64 + u64_val r2 * 2^128 + u64_val r3 * 2^192
    = u512_val l mod secp256k1_N).
  { rewrite <- Hstage2_mod.
    apply (reduce_512_tail_mod (u64_val p0) (u64_val p1) (u64_val p2) (u64_val p3) p4v
      (u64_val q0) (u64_val q1) (u64_val q2) (u64_val q3)
      (u128_val b0) (u128_val b1) (u128_val b2) (u128_val b3)
      (u64_val r0) (u64_val r1) (u64_val r2) (u64_val r3)
      (u128_val d0) (u128_val d1) (u128_val d2) (u128_val d3));
      first [exact Hb3 | rep_lia]. }

  Exists (mkScalar (u512_val l mod secp256k1_N)
            ltac:(apply Z.mod_pos_bound; unfold secp256k1_N; lia)).
  entailer!.

  (* Reduce to list equality *)
  apply derives_refl'.
  f_equal.

  assert (Hr_range :
    0 <= u64_val r0 + u64_val r1 * 2^64 + u64_val r2 * 2^128 + u64_val r3 * 2^192
      < 2^256) by rep_lia.

  (* Remove all VST/pointer/bounds context -- keep only pure Z facts *)
  clear - Hresult Hr_range.

  (* Collapse the [upd_Znth] chain to a plain 4-element list *)
  transitivity [uint64_to_val r0; uint64_to_val r1;
                uint64_to_val r2; uint64_to_val r3].
  { unfold default_val.
    reflexivity. }

  rewrite (uint256_from_limbs r0 r1 r2 r3 Hr_range).
  unfold uint256_to_val, scalar_to_val.
  (* cbn, not simpl: simpl would also turn the 2^64 powers into Z.pow_pos
     and break the match with Hresult *)
  cbn [u256_val scalar_val].
  rewrite Hresult.
  reflexivity.
Qed.
