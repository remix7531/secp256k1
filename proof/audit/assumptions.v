(** * audit.assumptions: whole-surface assumption audit for the public proof. *)
(** Copyright (C) 2026 remix7531
    SPDX-License-Identifier: MIT *)

(** This file packages EVERY body proof in the development into one list,
    [verified_surface], runs [Print Assumptions] on it, and machine-checks
    three completeness facts that used to be human-asserted:

    - [surface_complete]: the audited spec list IS the global funspec table
      ([Gprog_all_list], contract/gprog/all.v), entry for entry.  A funspec
      added to any per-subsystem context without a Qed body breaks this line.
    - [surface_binds_prog]: each audited body is bound, BY THE SPEC'S IDENT,
      to exactly that function in the extracted AST -- the spec/function
      association is no longer nominal.
    - [prog_covered]: every internal function clightgen retained in the AST
      is either audited or on the explicit [exempted] debt register.  A new
      extraction target fails the gate until its body proof lands.

    The assumption audit itself does not rely on [Print Assumptions] being
    transitive across [forward_call]s -- a VST [semax_body] discharges its
    calls against the callee's funspec drawn from its Gprog context, not the
    callee's body lemma, so a caller's assumption set does NOT close over its
    callees' bodies; enumerating every body here is what makes the audit
    complete.  Each entry carries the per-subsystem context it was proved
    against (contract/gprog/).

    What this file still does NOT give (the delta a future [semax_func]
    master theorem in audit/linked.v would add): global-environment
    well-formedness, no-duplicate-ident checks, and soundness of the
    external/builtin specs.  VST 2.16's full [semax_prog] is out of reach
    for a library (it hard-requires a [main]); the [semax_func] component is
    the pre-publication milestone.

    [make axioms] compiles this file, captures the [Print Assumptions]
    output, and fails (audit/check-axioms.sh) if any reported assumption is
    absent from the documented whitelist (audit/AXIOM_WHITELIST).  The gate
    cares only about axioms WE introduce; the foundational VST / CompCert /
    Coq axioms that floyd rests on are whitelisted there.

    This file is NOT listed in _RocqProject: it is compiled standalone by
    the [make axioms] target (after [make proof] has built every
    dependency), so a normal [make proof] is not flooded with assumption
    dumps. *)

Require Import VST.floyd.proofauto.
Require Import secp256k1.vst.base.
Require Import secp256k1.contract.gprog.all.

(* Every body proof in the development (one [semax_body] per C function). *)
Require Import secp256k1.verif.field.fe_add.
Require Import secp256k1.verif.int128.i128_accum_mul.
Require Import secp256k1.verif.int128.i128_check_pow2.
Require Import secp256k1.verif.int128.i128_det.
Require Import secp256k1.verif.int128.i128_eq_var.
Require Import secp256k1.verif.int128.i128_from_i64.
Require Import secp256k1.verif.int128.i128_load.
Require Import secp256k1.verif.int128.i128_mul.
Require Import secp256k1.verif.int128.i128_rshift.
Require Import secp256k1.verif.int128.i128_to_i64.
Require Import secp256k1.verif.int128.i128_to_u64.
Require Import secp256k1.verif.int128.impl.i128_dissip_mul.
Require Import secp256k1.verif.int128.impl.mul128.
Require Import secp256k1.verif.int128.impl.umul128.
Require Import secp256k1.verif.int128.u128_accum_mul.
Require Import secp256k1.verif.int128.u128_accum_u64.
Require Import secp256k1.verif.int128.u128_check_bits.
Require Import secp256k1.verif.int128.u128_from_u64.
Require Import secp256k1.verif.int128.u128_hi_u64.
Require Import secp256k1.verif.int128.u128_load.
Require Import secp256k1.verif.int128.u128_mul.
Require Import secp256k1.verif.int128.u128_rshift.
Require Import secp256k1.verif.int128.u128_to_u64.
Require Import secp256k1.verif.modinv.impl.modinv64_divsteps_59.
Require Import secp256k1.verif.modinv.impl.modinv64_divsteps_62_var.
Require Import secp256k1.verif.modinv.impl.modinv64_normalize_62.
Require Import secp256k1.verif.modinv.impl.modinv64_signed62_assign.
Require Import secp256k1.verif.modinv.impl.modinv64_update_de_62.
Require Import secp256k1.verif.modinv.impl.modinv64_update_de_limb.
Require Import secp256k1.verif.modinv.impl.modinv64_update_fg_62.
Require Import secp256k1.verif.modinv.impl.modinv64_update_fg_62_var.
Require Import secp256k1.verif.modinv.modinv64.
Require Import secp256k1.verif.modinv.modinv64_var.
Require Import secp256k1.verif.scalar.get_bits_limb32.
Require Import secp256k1.verif.scalar.get_bits_var.
Require Import secp256k1.verif.scalar.impl.scalar_check_overflow.
Require Import secp256k1.verif.scalar.impl.scalar_extract.
Require Import secp256k1.verif.scalar.impl.scalar_extract_fast.
Require Import secp256k1.verif.scalar.impl.scalar_from_signed62.
Require Import secp256k1.verif.scalar.impl.scalar_mul_512.
Require Import secp256k1.verif.scalar.impl.scalar_muladd.
Require Import secp256k1.verif.scalar.impl.scalar_muladd_fast.
Require Import secp256k1.verif.scalar.impl.scalar_reduce.
Require Import secp256k1.verif.scalar.impl.scalar_reduce_512.
Require Import secp256k1.verif.scalar.impl.scalar_shift_limb.
Require Import secp256k1.verif.scalar.impl.scalar_sumadd.
Require Import secp256k1.verif.scalar.impl.scalar_sumadd_fast.
Require Import secp256k1.verif.scalar.impl.scalar_to_signed62.
Require Import secp256k1.verif.scalar.scalar_add.
Require Import secp256k1.verif.scalar.scalar_cadd_bit.
Require Import secp256k1.verif.scalar.scalar_clear.
Require Import secp256k1.verif.scalar.scalar_cmov.
Require Import secp256k1.verif.scalar.scalar_cond_negate.
Require Import secp256k1.verif.scalar.scalar_eq.
Require Import secp256k1.verif.scalar.scalar_get_b32.
Require Import secp256k1.verif.scalar.scalar_half.
Require Import secp256k1.verif.scalar.scalar_inverse.
Require Import secp256k1.verif.scalar.scalar_inverse_var.
Require Import secp256k1.verif.scalar.scalar_is_even.
Require Import secp256k1.verif.scalar.scalar_is_high.
Require Import secp256k1.verif.scalar.scalar_is_one.
Require Import secp256k1.verif.scalar.scalar_is_zero.
Require Import secp256k1.verif.scalar.scalar_mul.
Require Import secp256k1.verif.scalar.scalar_mul_shift_var.
Require Import secp256k1.verif.scalar.scalar_negate.
Require Import secp256k1.verif.scalar.scalar_set_b32.
Require Import secp256k1.verif.scalar.scalar_set_b32_seckey.
Require Import secp256k1.verif.scalar.scalar_set_int.
Require Import secp256k1.verif.scalar.scalar_split_128.
Require Import secp256k1.verif.scalar.scalar_split_lambda.
Require Import secp256k1.verif.scalar.scalar_verify.
Require Import secp256k1.verif.util.ctz64_var.
Require Import secp256k1.verif.util.ctz64_var_debruijn.
Require Import secp256k1.verif.util.memclear_explicit.
Require Import secp256k1.verif.util.memzero_explicit.
Require Import secp256k1.verif.util.read_be64.
Require Import secp256k1.verif.util.write_be64.

(* ================================================================= *)
(** ** The audited surface -- one list entry per body proof. *)

(** An audited body: a [semax_body] fact packaged with the funspec context it
    was proved against, its (ident, funspec), and its AST function. *)
Definition audited_body : Type :=
  { ctx : funspecs &
    { s : ident * funspec &
      { f : function | semax_body Vprog ctx f s } } }.

Definition abody {ctx : funspecs} {s : ident * funspec} {f : function}
  (p : semax_body Vprog ctx f s) : audited_body :=
  existT _ ctx (existT _ s (exist _ f p)).

(** The whole verified surface.  One line per function, in [Gprog_all_list]
    order (int128 ++ util ++ scalar ++ field ++ modinv) so that
    [surface_complete] is a one-step conversion. *)
Definition verified_surface : list audited_body := [
  (* int128 *)
  abody body_secp256k1_umul128;
  abody body_secp256k1_u128_load;
  abody body_secp256k1_u128_mul;
  abody body_secp256k1_u128_accum_mul;
  abody body_secp256k1_u128_accum_u64;
  abody body_secp256k1_u128_rshift;
  abody body_secp256k1_u128_to_u64;
  abody body_secp256k1_u128_hi_u64;
  abody body_secp256k1_u128_from_u64;
  abody body_secp256k1_u128_check_bits;
  abody body_secp256k1_mul128;
  abody body_secp256k1_i128_load;
  abody body_secp256k1_i128_mul;
  abody body_secp256k1_i128_accum_mul;
  abody body_secp256k1_i128_dissip_mul;
  abody body_secp256k1_i128_det;
  abody body_secp256k1_i128_rshift;
  abody body_secp256k1_i128_to_u64;
  abody body_secp256k1_i128_to_i64;
  abody body_secp256k1_i128_from_i64;
  abody body_secp256k1_i128_eq_var;
  abody body_secp256k1_i128_check_pow2;
  (* util *)
  abody body_secp256k1_read_be64;
  abody body_secp256k1_write_be64;
  abody body_secp256k1_memzero_explicit;
  abody body_secp256k1_memclear_explicit;
  abody body_secp256k1_ctz64_var_debruijn;
  abody body_secp256k1_ctz64_var;
  (* scalar *)
  abody body_secp256k1_scalar_muladd;
  abody body_secp256k1_scalar_muladd_fast;
  abody body_secp256k1_scalar_sumadd;
  abody body_secp256k1_scalar_sumadd_fast;
  abody body_secp256k1_scalar_extract;
  abody body_secp256k1_scalar_extract_fast;
  abody body_secp256k1_scalar_check_overflow;
  abody body_secp256k1_scalar_reduce;
  abody body_secp256k1_scalar_mul_512;
  abody body_secp256k1_scalar_reduce_512;
  abody body_secp256k1_scalar_mul;
  abody body_secp256k1_scalar_set_int;
  abody body_secp256k1_scalar_clear;
  abody body_secp256k1_scalar_cmov;
  abody body_secp256k1_scalar_verify;
  abody body_secp256k1_scalar_is_zero;
  abody body_secp256k1_scalar_is_one;
  abody body_secp256k1_scalar_is_even;
  abody body_secp256k1_scalar_is_high;
  abody body_secp256k1_scalar_eq;
  abody body_secp256k1_scalar_negate;
  abody body_secp256k1_scalar_half;
  abody body_secp256k1_scalar_add;
  abody body_secp256k1_scalar_cadd_bit;
  abody body_secp256k1_scalar_cond_negate;
  abody body_secp256k1_scalar_split_128;
  abody body_secp256k1_scalar_set_b32;
  abody body_secp256k1_scalar_set_b32_seckey;
  abody body_secp256k1_scalar_get_b32;
  abody body_secp256k1_scalar_shift_limb;
  abody body_secp256k1_scalar_mul_shift_var;
  abody body_secp256k1_scalar_split_lambda;
  abody body_secp256k1_scalar_get_bits_limb32;
  abody body_secp256k1_scalar_get_bits_var;
  (* field *)
  abody body_secp256k1_fe_impl_add;
  (* modinv *)
  abody body_secp256k1_modinv64_signed62_assign;
  abody body_secp256k1_modinv64_normalize_62;
  abody body_secp256k1_modinv64_divsteps_62_var;
  abody body_secp256k1_modinv64_divsteps_59;
  abody body_secp256k1_modinv64_update_de_limb;
  abody body_secp256k1_modinv64_update_de_62;
  abody body_secp256k1_modinv64_update_fg_62_var;
  abody body_secp256k1_modinv64_update_fg_62;
  abody body_secp256k1_modinv64_var;
  abody body_secp256k1_scalar_to_signed62;
  abody body_secp256k1_scalar_from_signed62;
  abody body_secp256k1_scalar_inverse_var;
  abody body_secp256k1_modinv64;
  abody body_secp256k1_scalar_inverse
].

(* ================================================================= *)
(** ** Completeness -- the three facts that close the audit gaps. *)

Definition surface_specs : list (ident * funspec) :=
  map (fun a => projT1 (projT2 a)) verified_surface.

(** Every funspec in the global table is backed by an audited Qed body --
    entry for entry, spec for spec.  (The Admitted jacobi spec is not in
    [Gprog_all_list]; it lives only in the jacobi context.) *)
Lemma surface_complete : surface_specs = Gprog_all_list.
Proof. reflexivity. Qed.

(** Association-list lookup over the AST's definitions. *)
Definition prog_fun (i : ident) : option (globdef (fundef function) type) :=
  match List.find (fun d => Pos.eqb (fst d) i) (prog_defs prog) with
  | Some d => Some (snd d)
  | None => None
  end.

(** Each audited body's function IS the AST's function at its spec's ident:
    the spec/function association is machine-checked, not nominal. *)
Lemma surface_binds_prog :
  map (fun a => prog_fun (fst (projT1 (projT2 a)))) verified_surface
  = map (fun a => Some (Gfun (Internal (proj1_sig (projT2 (projT2 a))))))
        verified_surface.
Proof. reflexivity. Qed.

(** The explicit debt register: retained internal functions outside the
    verified surface.  Today exactly the jacobi path -- [jacobi64_maybe_var]
    has a spec but no body proof, and its [posdivsteps_62_var] helper has no
    spec yet. *)
Definition exempted : list ident :=
  [_secp256k1_jacobi64_maybe_var; _secp256k1_modinv64_posdivsteps_62_var].

Definition is_internal (d : ident * globdef (fundef function) type) : bool :=
  match snd d with Gfun (Internal _) => true | _ => false end.

(** Every internal function clightgen retained in the AST is audited or
    exempted.  Adding a C function to extraction_targets[] fails this line
    until its body proof lands (or it is consciously added to [exempted]). *)
Lemma prog_covered :
  forallb
    (fun i => existsb (Pos.eqb i) (map fst surface_specs ++ exempted))
    (map fst (filter is_internal (prog_defs prog))) = true.
Proof. vm_compute. reflexivity. Qed.

(* ================================================================= *)
(** ** The assumption dump the gate parses. *)

Print Assumptions verified_surface.
