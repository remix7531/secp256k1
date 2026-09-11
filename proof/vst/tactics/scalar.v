(** * vst.tactics.scalar: scalar-subsystem automation (N constants, carry bridges,
    forward_call wrappers). *)
(** Copyright (C) 2026 remix7531
    SPDX-License-Identifier: MIT *)

(** Everything scalar-specific that the old monolithic automation carried:
    the [N]/[N_C] rep_lia hints and [N_C_*_u64] wrappers, the muladd/sumadd
    VST carry-bridge lemmas, the C-expression lemmas for [~N_i (+1)], and the
    scalar [forward_call_*] wrappers with their parameter-matching solvers. *)

Require Export secp256k1.vst.tactics.core.
Require Import secp256k1.vst.helper.repr.

(* ================================================================= *)
(** ** rep_lia constant hints -- [N] / [N_C] unfoldings.

    Registering the N and N_C limb values with the [rep_lia] hint
    database lets [rep_lia] expand these constants automatically,
    replacing manual [unfold N_C_0; lia] patterns. *)

Lemma N_C_0_eq : N_C_0 = 4624529908474429119. Proof. reflexivity. Qed.
Lemma N_C_1_eq : N_C_1 = 4994812053365940164. Proof. reflexivity. Qed.
Lemma N_C_2_eq : N_C_2 = 1. Proof. reflexivity. Qed.
Lemma N_0_eq : N_0 = 13822214165235122497. Proof. reflexivity. Qed.
Lemma N_1_eq : N_1 = 13451932020343611451. Proof. reflexivity. Qed.
Lemma N_2_eq : N_2 = 18446744073709551614. Proof. reflexivity. Qed.
Lemma N_3_eq : N_3 = 18446744073709551615. Proof. reflexivity. Qed.
(** [secp256k1_N]'s value bridge ([secp256k1_N_unfold]) lives in
    [theory/scalar.v] and is registered with [rep_lia] there: the constant is
    sealed [Opaque], so its value is recovered by rewriting, not unfolding. *)
#[export] Hint Rewrite N_C_0_eq N_C_1_eq N_C_2_eq
                       N_0_eq N_1_eq N_2_eq N_3_eq : rep_lia.

(** UInt64 wrappers for the N_C limb constants, so call sites don't
    keep rebuilding the same [mkUInt64 N_C_i N_C_i_range] term. *)
Definition N_C_0_u64 : UInt64 := mkUInt64 N_C_0 N_C_0_range.
Definition N_C_1_u64 : UInt64 := mkUInt64 N_C_1 N_C_1_range.
Definition N_C_2_u64 : UInt64 := mkUInt64 N_C_2 N_C_2_range.

Lemma u64_val_N_C_0_u64 : u64_val N_C_0_u64 = N_C_0. Proof. reflexivity. Qed.
Lemma u64_val_N_C_1_u64 : u64_val N_C_1_u64 = N_C_1. Proof. reflexivity. Qed.
Lemma u64_val_N_C_2_u64 : u64_val N_C_2_u64 = N_C_2. Proof. reflexivity. Qed.
#[export] Hint Rewrite u64_val_N_C_0_u64 u64_val_N_C_1_u64 u64_val_N_C_2_u64 : rep_lia.


(** The C expression [~(int64_t)N_0 + 1] evaluates to [N_C_0]. *)
Lemma N_C_0_expr :
  Int64.add (Int64.not (Int64.repr (-4624529908474429119))) (Int64.repr 1)
  = Int64.repr N_C_0.
Proof.
  unfold N_C_0.
  apply Int64.eqm_samerepr.
  vm_compute.
  exists 0.
  lia.
Qed.

(** The C expression [~(int64_t)N_1] evaluates to [N_C_1]. *)
Lemma N_C_1_expr :
  Int64.not (Int64.repr (-4994812053365940165)) = Int64.repr N_C_1.
Proof.
  unfold N_C_1.
  apply Int64.eqm_samerepr.
  vm_compute.
  exists 0.
  lia.
Qed.

(* ================================================================= *)
(** ** forward_call wrappers + parameter-matching solvers. *)

(** Solve the parameter-matching [firstn ... = [...]] equation that
    appears when the C-representation uses inline splits but the spec
    arguments are [u256_limb x k] / [uint64_to_val _].  Rewrites with
    the bridge lemmas [uint128/acc/uint256/uint512_to_val_limb] to
    convert inline splits to [limb (2^64) v i] form. *)
Ltac solve_param_match :=
  entailer!;
  autorewrite with to_val_limb;
  unfold u256_limb, uint64_to_val;
  simpl;
  reflexivity.

(** Accumulator helpers (muladd, muladd_fast, sumadd, sumadd_fast). *)

Ltac forward_call_muladd acc_ptr acc a b acc' Hacc' :=
  forward_call (acc_ptr, acc, a, b, Tsh);
  [ try solve_param_match; try (simpl; rep_lia) .. | Intros acc'; rename H into Hacc'; try deadvars!].

Ltac forward_call_muladd_fast acc_ptr acc a b acc' Hacc' :=
  forward_call (acc_ptr, acc, a, b, Tsh);
  [ try solve_param_match; try (simpl; rep_lia) .. | Intros acc'; rename H into Hacc'; try deadvars!].

Ltac forward_call_sumadd acc_ptr acc a acc' Hacc' :=
  forward_call (acc_ptr, acc, a, Tsh);
  [ try solve_param_match; try (simpl; rep_lia) .. | Intros acc'; rename H into Hacc'; try deadvars!].

Ltac forward_call_sumadd_fast acc_ptr acc a acc' Hacc' :=
  forward_call (acc_ptr, acc, a, Tsh);
  [ try solve_param_match; try (simpl; rep_lia) .. | Intros acc'; rename H into Hacc'; try deadvars!].

(** Extract helpers (extract, extract_fast).
    Returns a [(UInt64 * Acc)] pair that is destructured. *)

Ltac forward_call_extract acc_ptr acc n_ptr sh sh_n lo carry Hlo Hcarry :=
  forward_call (acc_ptr, acc, n_ptr, sh, sh_n);
  [ try (simpl; rep_lia) .. | let vret := fresh "vret" in
        Intros vret; destruct vret as [lo carry];
        rename H into Hlo; rename H0 into Hcarry;
        simpl fst in *; simpl snd in *;
        try deadvars!].

Ltac forward_call_extract_fast acc_ptr acc n_ptr sh sh_n lo carry Hlo Hcarry :=
  forward_call (acc_ptr, acc, n_ptr, sh, sh_n);
  [ try (simpl; rep_lia) .. | let vret := fresh "vret" in
        Intros vret; destruct vret as [lo carry];
        rename H into Hlo; rename H0 into Hcarry;
        simpl fst in *; simpl snd in *;
        try deadvars!].

(** Higher-level functions. *)

Ltac forward_call_scalar_check_overflow a_ptr a sh :=
  forward_call (a_ptr, a, sh).

Ltac forward_call_scalar_reduce r_ptr r overflow sh r' Hr' :=
  forward_call (r_ptr, r, overflow, sh);
  [.. | Intros r'; rename H into Hr'; try deadvars!].

Ltac forward_call_scalar_mul_512 l8_ptr a_ptr b_ptr a b sh_l sh_a sh_b r Hr :=
  forward_call (l8_ptr, a_ptr, b_ptr, a, b, sh_l, sh_a, sh_b);
  [.. | Intros r; rename H into Hr; try deadvars!].

Ltac forward_call_scalar_reduce_512 r_ptr l_ptr l sh_r sh_l r' Hr' :=
  forward_call (r_ptr, l_ptr, l, sh_r, sh_l);
  [.. | Intros r'; rename H into Hr'; try deadvars!].

(* ================================================================= *)
(** ** scalar_reduce expr matching -- [solve_reduce_expr_match] for [overflow * N_C_i].

    Solves the VST parameter-matching goal for [(uint64_t)overflow * N_C_i]
    expressions that arise in [secp256k1_scalar_reduce].  Tries each
    constant in order: [N_C_0], [N_C_1], [N_C_2]. *)

(** Solve VST expression-matching goals for [(uint64_t)overflow * N_C_i]. *)
Ltac solve_reduce_expr_match :=
  entailer!; simpl; unfold uint64_to_val; simpl u64_val;
  f_equal; f_equal; f_equal; simpl;
  first
    [ rewrite N_C_0_expr; apply Int64_mul_repr; rep_lia
    | rewrite N_C_1_expr; apply Int64_mul_repr; rep_lia
    | unfold N_C_2; rewrite Z.mul_1_r; reflexivity ].
