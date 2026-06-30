(** * secp256k1_fv: the reviewer-facing headline of the verified surface. *)
(** Copyright (C) 2026 remix7531
    SPDX-License-Identifier: MIT *)

(** This file states, in one place, exactly what the proof tree under [proof/]
    establishes.  It is deliberately the LAST file a reviewer reads, not the
    first: everything it references (the model, the contracts, the body
    proofs) is defined and proved elsewhere; this file only names those
    pieces and packages them into one theorem.  Nothing in the tree imports
    this file -- it is a leaf, checked standalone by [audit/statement.v]
    (see "How to check" below).

    (1) The claim
    -------------
    The C functions covered are exactly those with a PUBLIC funspec in
    [contract/] (the files that are NOT under [contract/impl/]): the full
    unsigned/signed 128-bit family of [src/int128.h]
    ([secp256k1_u128_load/mul/accum_mul/accum_u64/rshift/to_u64/hi_u64/
    from_u64/check_bits] and [secp256k1_i128_load/mul/accum_mul/det/rshift/
    to_u64/to_i64/from_i64/eq_var/check_pow2]); the [src/util.h] byte-order and
    secure-clear helpers ([secp256k1_read_be64], [secp256k1_write_be64],
    [secp256k1_memzero_explicit], [secp256k1_memclear_explicit],
    [secp256k1_ctz64_var_debruijn], [secp256k1_ctz64_var]); the whole public
    [src/scalar.h] API ([secp256k1_scalar_mul], [set_int], [clear], [cmov],
    [verify], [is_zero], [is_one], [is_even], [is_high], [eq], [negate],
    [half], [add], [cadd_bit], [cond_negate], [split_128], [set_b32],
    [set_b32_seckey], [get_b32], [mul_shift_var], [split_lambda] (the GLV
    endomorphism split), [get_bits]/[get_bits_var], and the two modular-inverse
    entry points [secp256k1_scalar_inverse] / [_var]); the first
    [src/field.h] operation, [secp256k1_fe_add] (VERIFY-off, so it compiles
    straight to its leaf [secp256k1_fe_impl_add]); and the safegcd modular
    inverse drivers [secp256k1_modinv64] / [secp256k1_modinv64_var] from
    [src/modinv64.h].  That is 53 funspecs, enumerated in [secp256k1_verified]
    below in the order int128 (19), util (6), scalar (25), field (1),
    modinv (2).  A further 24 [static] (internal-linkage) helper functions
    ([contract/impl/]) are proved as building blocks of the above and are
    covered by [audit/assumptions.v]'s [verified_surface] (77 = 53 + 24
    entries total) but are not restated here.

    Each is proved to satisfy its [contract/<sub>.v] funspec (a [semax_body]
    fact) against a pure functional MODEL in [model/] -- [model.int128],
    [model.scalar], [model.field], [model.modinv] -- the trust boundary: a
    reviewer who accepts the model as "what the function should do" and the
    toolchain listed under "Trust surface" below gets, for each conjunct, "the
    real C function computes what the model says".

    The C is the library's own, unmodified [src/] source, taken through
    CompCert's [clightgen] from [proof/extraction.c] -- an extraction unit that
    [#include]s the real headers ([scalar.h]/[scalar_impl.h],
    [int128.h]/[int128_impl.h], [modinv64.h]/[modinv64_impl.h],
    [field.h]/[field_impl.h]) and forces retention of the call graph reachable
    from [extraction_targets[]] in [extraction.c] into
    one Clight AST, [clight/extraction.v], that every proof in the tree
    shares.  The build configuration (Makefile's [FV_DEFINES] /
    [CLIGHTGEN_FLAGS]):
    - [-DUSE_FORCE_WIDEMUL_INT128_STRUCT=1]: the pure-C struct 128-bit
      backend (CompCert has no [__int128] and no inline assembly), not the
      platform-native backend a normal build picks.
    - [-U__has_builtin]: forces [util.h]'s [ctz64_var] onto the portable
      De Bruijn software fallback, since [clightgen] cannot translate
      [__builtin_ctzll].
    - no [-DVERIFY]: the [VERIFY_CHECK] assertions and the verify-only helpers
      ([abs]/[mul_62]/[mul_cmp_62]/[det_check_pow2] in modinv,
      [secp256k1_scalar_verify]'s no-op precondition macro) are absent from
      the AST, so the proofs reason about exactly the production computation.
    - [SECP256K1_NO_LIBC]: the freestanding build, so [memzero_explicit] /
      [memclear_explicit] lower to a self-contained byte loop rather than a
      libc call, and the scalar constant-time helpers ([cmov], [cadd_bit],
      [cond_negate], [clear]) build without [<string.h>].
    - [volatile] is preprocessor-neutralized ([#define volatile]): a few
      locals in [normalize_62] and the scalar constant-time helpers are marked
      [volatile] purely as a constant-time hardening hint (it stops the
      compiler collapsing a branchless conditional); VST/CompCert do not model
      volatile local memory in forward symbolic execution, and dropping the
      qualifier does not change the value any function computes.
    This is one extraction, VERIFY-off: there is no second AST anywhere in the
    tree, so every conjunct below is checked against the identical
    [clight/extraction.v].

    (2) Trust surface
    -----------------
    [Print Assumptions secp256k1_verified] at the end of this file lists
    exactly 60 names (cross-checked against [audit/AXIOM_WHITELIST], the
    reviewed whitelist [make axioms] / [make audit] enforce against
    [audit/assumptions.v]'s own, larger [Print Assumptions] over all 77
    bodies -- the two lists coincide because no [semax_body] proof introduces
    an assumption outside this set):

    Foundational (58 -- trusted toolchain, none introduced by this project):
    - 7 classical-logic and extensionality axioms VST's [floyd]
      separation-logic automation is built on; not discharge-able without
      replacing floyd:
      - [Axioms.prop_ext] / [prop_ext] (propositional extensionality)
      - [Classical_Prop.classic] (excluded middle)
      - [ClassicalDedekindReals.sig_forall_dec]
      - [ClassicalDedekindReals.sig_not_dec]
      - [Ensembles.Extensionality_Ensembles]
      - [Eqdep.Eq_rect_eq.eq_rect_eq]
      - [FunctionalExtensionality.functional_extensionality_dep] /
        [functional_extensionality_dep]
      (two spellings each for the last and the first: [Print Assumptions]
      prints a shorter or fully-qualified name depending on what the gate
      file [Import]s; both are the same axiom.)
    - 51 Rocq primitive 63-bit integer axioms ([Uint63Axioms.*] /
      [PrimInt63.*]), pulled in by coqprime's [BigN]-based certificate
      checker: [model/constants.v]'s [secp256k1_N_prime] (the group order
      [n] is prime) is PROVED, not axiomatized, by a Pocklington certificate
      for the literal [n] ([theory/primality/n.v]'s
      [secp256k1_N_prime_cert], ~1 second to check).  [Print Assumptions]
      on that [Qed] proof closes over the certificate checker's own trust
      base instead of a project axiom -- the same toolchain trust any
      coqprime user accepts, not introduced by this development.  See
      [audit/AXIOM_WHITELIST] for the full name list.

    Project (2 -- introduced by this development, each an [Axiom] in
    [theory/modinv/divsteps/{bound724,bound590}.v]):
    - [bound724.example724] / [bound590.example590]: the safegcd 724- and
      590-divstep convergence-bound reflections.  COMPUTE-blocked, not
      tactic-blocked: [vm_compute] works on this toolchain, but the
      convex-hull check over a 256-bit modulus is superlinear in the
      iteration count (roughly k^4; multi-day and tens of GB at k = 724).
      Discharging either means running the reflection to completion on
      bigger hardware, or porting a sharper certificate (upstream
      sipa/safegcd-bounds assumes them too).

    (3) Not claimed
    ----------------
    - No [semax_prog] / whole-program linking theorem.  VST 2.16's
      [semax_prog] hard-requires a [main], which a library extraction unit
      does not have; what is established is 53 independent [semax_body]
      facts plus (in [audit/assumptions.v]) that each is bound, by its spec's
      ident, to the AST's function at that ident, and that the global
      [Gprog] table is exactly the audited surface.  A [semax_func] whole-
      program theorem is future work, not claimed here.
    - The Jacobi path is OUT of scope: no body proof is included for
      [secp256k1_jacobi64_maybe_var], and its
      [secp256k1_modinv64_posdivsteps_62_var] helper has no funspec.
      Both are named on the explicit debt register
      ([audit/assumptions.v]'s [exempted]) rather than silently dropped, but
      neither is in [verified_surface] or in this theorem.
    - The extraction configuration above is NOT the library's default shipped
      build (a normal build uses a native int128 backend, links libc, leaves
      [volatile] and [VERIFY] as the source has them).  A different build
      configuration is a different Clight AST and is not covered.
    - The semantics is whatever CompCert's [clightgen] and operational
      semantics assign to the C in [src/]; a CompCert front-end bug or a
      construct outside the modeled subset would be outside this proof's
      reach, same as for any CompCert-based verification.
    - No side-channel / constant-time claim.  This is a functional-
      correctness proof only.  The [volatile] hardening hint mentioned above
      is neutralized for extraction, and no timing or cache-behavior model is
      used anywhere in the tree.
    - [secp256k1_fe_impl_add] is the ONLY field function proved.  The rest of
      [field.h] ([mul], [sqr], [normalize], [inverse], [normalizes_to_zero],
      ...) is unverified.

    (4) How to check
    -----------------
    From the repository root: [nix develop] (or [direnv allow]) for the
    toolchain, then in [proof/]: [make proof] builds every [.v] including
    this file; [make audit] runs all seven mechanical gates: build
    freshness, the AST fingerprint, no proof gaps, axiom confinement, this
    file's headline pin via [audit/statement.v], the assumption cone vs.
    [audit/AXIOM_WHITELIST], and the style greps. See the Gates section in
    [STYLE.md] for the full list.
    [make axioms] alone re-runs the model/theory purity check and the
    assumption-cone gate. *)

Require Import secp256k1.vst.base.
Require Import Coq.ZArith.Znumtheory.

(* Bare (no [Import]): every reference below stays explicitly qualified as
   [secp256k1.model.constants.X] rather than pulling the module's short
   names into scope.  (Now that [secp256k1_N_prime] is a [Qed] lemma rather
   than an [Axiom], it no longer appears in [Print Assumptions] itself --
   only the certificate's own [Uint63Axioms.*] / [PrimInt63.*] cone does,
   see [audit/AXIOM_WHITELIST].) *)
Require secp256k1.model.constants.

Require Import secp256k1.contract.int128.
Require Import secp256k1.contract.util.
Require Import secp256k1.contract.scalar.
Require Import secp256k1.contract.field.
Require Import secp256k1.contract.modinv.

Require secp256k1.contract.gprog.int128.
Require secp256k1.contract.gprog.util.
Require secp256k1.contract.gprog.scalar.
Require secp256k1.contract.gprog.field.
Require secp256k1.contract.gprog.modinv.

(* The 53 public body proofs, one [Require Import] per C function, in the
   same int128/util/scalar/field/modinv order as the theorem below. *)
Require Import secp256k1.verif.int128.u128_load.
Require Import secp256k1.verif.int128.u128_mul.
Require Import secp256k1.verif.int128.u128_accum_mul.
Require Import secp256k1.verif.int128.u128_accum_u64.
Require Import secp256k1.verif.int128.u128_rshift.
Require Import secp256k1.verif.int128.u128_to_u64.
Require Import secp256k1.verif.int128.u128_hi_u64.
Require Import secp256k1.verif.int128.u128_from_u64.
Require Import secp256k1.verif.int128.u128_check_bits.
Require Import secp256k1.verif.int128.i128_load.
Require Import secp256k1.verif.int128.i128_mul.
Require Import secp256k1.verif.int128.i128_accum_mul.
Require Import secp256k1.verif.int128.i128_det.
Require Import secp256k1.verif.int128.i128_rshift.
Require Import secp256k1.verif.int128.i128_to_u64.
Require Import secp256k1.verif.int128.i128_to_i64.
Require Import secp256k1.verif.int128.i128_from_i64.
Require Import secp256k1.verif.int128.i128_eq_var.
Require Import secp256k1.verif.int128.i128_check_pow2.
Require Import secp256k1.verif.util.read_be64.
Require Import secp256k1.verif.util.write_be64.
Require Import secp256k1.verif.util.memzero_explicit.
Require Import secp256k1.verif.util.memclear_explicit.
Require Import secp256k1.verif.util.ctz64_var_debruijn.
Require Import secp256k1.verif.util.ctz64_var.
Require Import secp256k1.verif.scalar.scalar_mul.
Require Import secp256k1.verif.scalar.scalar_set_int.
Require Import secp256k1.verif.scalar.scalar_clear.
Require Import secp256k1.verif.scalar.scalar_cmov.
Require Import secp256k1.verif.scalar.scalar_verify.
Require Import secp256k1.verif.scalar.scalar_is_zero.
Require Import secp256k1.verif.scalar.scalar_is_one.
Require Import secp256k1.verif.scalar.scalar_is_even.
Require Import secp256k1.verif.scalar.scalar_is_high.
Require Import secp256k1.verif.scalar.scalar_eq.
Require Import secp256k1.verif.scalar.scalar_negate.
Require Import secp256k1.verif.scalar.scalar_half.
Require Import secp256k1.verif.scalar.scalar_add.
Require Import secp256k1.verif.scalar.scalar_cadd_bit.
Require Import secp256k1.verif.scalar.scalar_cond_negate.
Require Import secp256k1.verif.scalar.scalar_split_128.
Require Import secp256k1.verif.scalar.scalar_set_b32.
Require Import secp256k1.verif.scalar.scalar_set_b32_seckey.
Require Import secp256k1.verif.scalar.scalar_get_b32.
Require Import secp256k1.verif.scalar.scalar_mul_shift_var.
Require Import secp256k1.verif.scalar.scalar_split_lambda.
Require Import secp256k1.verif.scalar.get_bits_limb32.
Require Import secp256k1.verif.scalar.get_bits_var.
Require Import secp256k1.verif.scalar.scalar_inverse_var.
Require Import secp256k1.verif.scalar.scalar_inverse.
Require Import secp256k1.verif.field.fe_add.
Require Import secp256k1.verif.modinv.modinv64_var.
Require Import secp256k1.verif.modinv.modinv64.

(* ================================================================= *)
(** ** Numeric pins -- the headline values, checked against the decimal
    literal a reviewer can verify externally (SEC2 / the C headers). *)

(** [model/constants.v] seals [secp256k1_N] [Opaque] only within that file
    (the seal is file-local, per its own header comment), so it is transparent
    here and [reflexivity] unfolds it directly against the literal. *)
Lemma n_pin :
  secp256k1.model.constants.secp256k1_N
  = 115792089237316195423570985008687907852837564279074904382605163141518161494337.
Proof. reflexivity. Qed.

Lemma p_pin :
  secp256k1.model.constants.secp256k1_P
  = 115792089237316195423570985008687907853269984665640564039457584007908834671663.
Proof. reflexivity. Qed.

Lemma lambda_pin :
  secp256k1.model.constants.secp256k1_lambda
  = 37718080363155996902926221483475020450927657555482586988616620542887997980018.
Proof. reflexivity. Qed.

(** The exact statement of the one project axiom this file's claim depends on
    through the scalar-inverse specs (dropping the coprimality precondition):
    printed here, next to the pins, rather than re-derived. *)
(** This is now a [Lemma] in [model/constants.v] (a coqprime Pocklington
    certificate, [theory/primality/n.v], discharges it), not an [Axiom]; the
    statement is unchanged, so this [Check] and every downstream user
    (the scalar-inverse specs, this file) are untouched by the switch. *)
Check secp256k1.model.constants.secp256k1_N_prime
  : prime secp256k1.model.constants.secp256k1_N.

(* ================================================================= *)
(** ** The headline -- one conjunct per PUBLIC funspec, [Gprog] context named
    explicitly (qualified, since five different [Gprog] contexts coexist in
    this file) so each line is checkable against its own [verif/] file. *)

Theorem secp256k1_verified :
  (* ----- int128 (19): src/int128.h public u128_*/i128_* family ----- *)
  semax_body Vprog secp256k1.contract.gprog.int128.Gprog
    f_secp256k1_u128_load spec_secp256k1_u128_load /\
  semax_body Vprog secp256k1.contract.gprog.int128.Gprog
    f_secp256k1_u128_mul spec_secp256k1_u128_mul /\
  semax_body Vprog secp256k1.contract.gprog.int128.Gprog
    f_secp256k1_u128_accum_mul spec_secp256k1_u128_accum_mul /\
  semax_body Vprog secp256k1.contract.gprog.int128.Gprog
    f_secp256k1_u128_accum_u64 spec_secp256k1_u128_accum_u64 /\
  semax_body Vprog secp256k1.contract.gprog.int128.Gprog
    f_secp256k1_u128_rshift spec_secp256k1_u128_rshift /\
  semax_body Vprog secp256k1.contract.gprog.int128.Gprog
    f_secp256k1_u128_to_u64 spec_secp256k1_u128_to_u64 /\
  semax_body Vprog secp256k1.contract.gprog.int128.Gprog
    f_secp256k1_u128_hi_u64 spec_secp256k1_u128_hi_u64 /\
  semax_body Vprog secp256k1.contract.gprog.int128.Gprog
    f_secp256k1_u128_from_u64 spec_secp256k1_u128_from_u64 /\
  semax_body Vprog secp256k1.contract.gprog.int128.Gprog
    f_secp256k1_u128_check_bits spec_secp256k1_u128_check_bits /\
  semax_body Vprog secp256k1.contract.gprog.int128.Gprog
    f_secp256k1_i128_load spec_secp256k1_i128_load /\
  semax_body Vprog secp256k1.contract.gprog.int128.Gprog
    f_secp256k1_i128_mul spec_secp256k1_i128_mul /\
  semax_body Vprog secp256k1.contract.gprog.int128.Gprog
    f_secp256k1_i128_accum_mul spec_secp256k1_i128_accum_mul /\
  semax_body Vprog secp256k1.contract.gprog.int128.Gprog
    f_secp256k1_i128_det spec_secp256k1_i128_det /\
  semax_body Vprog secp256k1.contract.gprog.int128.Gprog
    f_secp256k1_i128_rshift spec_secp256k1_i128_rshift /\
  semax_body Vprog secp256k1.contract.gprog.int128.Gprog
    f_secp256k1_i128_to_u64 spec_secp256k1_i128_to_u64 /\
  semax_body Vprog secp256k1.contract.gprog.int128.Gprog
    f_secp256k1_i128_to_i64 spec_secp256k1_i128_to_i64 /\
  semax_body Vprog secp256k1.contract.gprog.int128.Gprog
    f_secp256k1_i128_from_i64 spec_secp256k1_i128_from_i64 /\
  semax_body Vprog secp256k1.contract.gprog.int128.Gprog
    f_secp256k1_i128_eq_var spec_secp256k1_i128_eq_var /\
  semax_body Vprog secp256k1.contract.gprog.int128.Gprog
    f_secp256k1_i128_check_pow2 spec_secp256k1_i128_check_pow2 /\
  (* ----- util (6): src/util.h byte-order + secure-clear + ctz64 ----- *)
  semax_body Vprog secp256k1.contract.gprog.util.Gprog
    f_secp256k1_read_be64 spec_secp256k1_read_be64 /\
  semax_body Vprog secp256k1.contract.gprog.util.Gprog
    f_secp256k1_write_be64 spec_secp256k1_write_be64 /\
  semax_body Vprog secp256k1.contract.gprog.util.Gprog
    f_secp256k1_memzero_explicit spec_secp256k1_memzero_explicit /\
  semax_body Vprog secp256k1.contract.gprog.util.Gprog
    f_secp256k1_memclear_explicit spec_secp256k1_memclear_explicit /\
  semax_body Vprog secp256k1.contract.gprog.util.Gprog
    f_secp256k1_ctz64_var_debruijn spec_secp256k1_ctz64_var_debruijn /\
  semax_body Vprog secp256k1.contract.gprog.util.Gprog
    f_secp256k1_ctz64_var spec_secp256k1_ctz64_var /\
  (* ----- scalar (25): src/scalar.h public API (23 under Gprog_scalar, ---- *)
  (* ----- 2 modular-inverse entry points under Gprog_modinv) -------------- *)
  semax_body Vprog secp256k1.contract.gprog.scalar.Gprog
    f_secp256k1_scalar_mul spec_secp256k1_scalar_mul /\
  semax_body Vprog secp256k1.contract.gprog.scalar.Gprog
    f_secp256k1_scalar_set_int spec_secp256k1_scalar_set_int /\
  semax_body Vprog secp256k1.contract.gprog.scalar.Gprog
    f_secp256k1_scalar_clear spec_secp256k1_scalar_clear /\
  semax_body Vprog secp256k1.contract.gprog.scalar.Gprog
    f_secp256k1_scalar_cmov spec_secp256k1_scalar_cmov /\
  semax_body Vprog secp256k1.contract.gprog.scalar.Gprog
    f_secp256k1_scalar_verify spec_secp256k1_scalar_verify /\
  semax_body Vprog secp256k1.contract.gprog.scalar.Gprog
    f_secp256k1_scalar_is_zero spec_secp256k1_scalar_is_zero /\
  semax_body Vprog secp256k1.contract.gprog.scalar.Gprog
    f_secp256k1_scalar_is_one spec_secp256k1_scalar_is_one /\
  semax_body Vprog secp256k1.contract.gprog.scalar.Gprog
    f_secp256k1_scalar_is_even spec_secp256k1_scalar_is_even /\
  semax_body Vprog secp256k1.contract.gprog.scalar.Gprog
    f_secp256k1_scalar_is_high spec_secp256k1_scalar_is_high /\
  semax_body Vprog secp256k1.contract.gprog.scalar.Gprog
    f_secp256k1_scalar_eq spec_secp256k1_scalar_eq /\
  semax_body Vprog secp256k1.contract.gprog.scalar.Gprog
    f_secp256k1_scalar_negate spec_secp256k1_scalar_negate /\
  semax_body Vprog secp256k1.contract.gprog.scalar.Gprog
    f_secp256k1_scalar_half spec_secp256k1_scalar_half /\
  semax_body Vprog secp256k1.contract.gprog.scalar.Gprog
    f_secp256k1_scalar_add spec_secp256k1_scalar_add /\
  semax_body Vprog secp256k1.contract.gprog.scalar.Gprog
    f_secp256k1_scalar_cadd_bit spec_secp256k1_scalar_cadd_bit /\
  semax_body Vprog secp256k1.contract.gprog.scalar.Gprog
    f_secp256k1_scalar_cond_negate spec_secp256k1_scalar_cond_negate /\
  semax_body Vprog secp256k1.contract.gprog.scalar.Gprog
    f_secp256k1_scalar_split_128 spec_secp256k1_scalar_split_128 /\
  semax_body Vprog secp256k1.contract.gprog.scalar.Gprog
    f_secp256k1_scalar_set_b32 spec_secp256k1_scalar_set_b32 /\
  semax_body Vprog secp256k1.contract.gprog.scalar.Gprog
    f_secp256k1_scalar_set_b32_seckey spec_secp256k1_scalar_set_b32_seckey /\
  semax_body Vprog secp256k1.contract.gprog.scalar.Gprog
    f_secp256k1_scalar_get_b32 spec_secp256k1_scalar_get_b32 /\
  semax_body Vprog secp256k1.contract.gprog.scalar.Gprog
    f_secp256k1_scalar_mul_shift_var spec_secp256k1_scalar_mul_shift_var /\
  semax_body Vprog secp256k1.contract.gprog.scalar.Gprog
    f_secp256k1_scalar_split_lambda spec_secp256k1_scalar_split_lambda /\
  semax_body Vprog secp256k1.contract.gprog.scalar.Gprog
    f_secp256k1_scalar_get_bits_limb32 spec_secp256k1_scalar_get_bits_limb32 /\
  semax_body Vprog secp256k1.contract.gprog.scalar.Gprog
    f_secp256k1_scalar_get_bits_var spec_secp256k1_scalar_get_bits_var /\
  semax_body Vprog secp256k1.contract.gprog.modinv.Gprog
    f_secp256k1_scalar_inverse_var spec_secp256k1_scalar_inverse_var /\
  semax_body Vprog secp256k1.contract.gprog.modinv.Gprog
    f_secp256k1_scalar_inverse spec_secp256k1_scalar_inverse /\
  (* ----- field (1): src/field.h -- the first op, VERIFY-off leaf ----- *)
  semax_body Vprog secp256k1.contract.gprog.field.Gprog
    f_secp256k1_fe_impl_add spec_secp256k1_fe_impl_add /\
  (* ----- modinv (2): src/modinv64.h -- the two public safegcd drivers - *)
  semax_body Vprog secp256k1.contract.gprog.modinv.Gprog
    f_secp256k1_modinv64_var spec_secp256k1_modinv64_var /\
  semax_body Vprog secp256k1.contract.gprog.modinv.Gprog
    f_secp256k1_modinv64 spec_secp256k1_modinv64.
Proof.
  (* One [exact] per conjunct, in the order stated above -- explicit, no
     search.  The 24 [impl/] helper bodies these call through [forward_call]
     are proved separately (against their own contracts) and are audited by
     [audit/assumptions.v]'s [verified_surface] and its three completeness
     lemmas ([surface_complete], [surface_binds_prog], [prog_covered]); this
     theorem restates only the 53 PUBLIC funspecs. *)
  split; [exact body_secp256k1_u128_load|].
  split; [exact body_secp256k1_u128_mul|].
  split; [exact body_secp256k1_u128_accum_mul|].
  split; [exact body_secp256k1_u128_accum_u64|].
  split; [exact body_secp256k1_u128_rshift|].
  split; [exact body_secp256k1_u128_to_u64|].
  split; [exact body_secp256k1_u128_hi_u64|].
  split; [exact body_secp256k1_u128_from_u64|].
  split; [exact body_secp256k1_u128_check_bits|].
  split; [exact body_secp256k1_i128_load|].
  split; [exact body_secp256k1_i128_mul|].
  split; [exact body_secp256k1_i128_accum_mul|].
  split; [exact body_secp256k1_i128_det|].
  split; [exact body_secp256k1_i128_rshift|].
  split; [exact body_secp256k1_i128_to_u64|].
  split; [exact body_secp256k1_i128_to_i64|].
  split; [exact body_secp256k1_i128_from_i64|].
  split; [exact body_secp256k1_i128_eq_var|].
  split; [exact body_secp256k1_i128_check_pow2|].
  split; [exact body_secp256k1_read_be64|].
  split; [exact body_secp256k1_write_be64|].
  split; [exact body_secp256k1_memzero_explicit|].
  split; [exact body_secp256k1_memclear_explicit|].
  split; [exact body_secp256k1_ctz64_var_debruijn|].
  split; [exact body_secp256k1_ctz64_var|].
  split; [exact body_secp256k1_scalar_mul|].
  split; [exact body_secp256k1_scalar_set_int|].
  split; [exact body_secp256k1_scalar_clear|].
  split; [exact body_secp256k1_scalar_cmov|].
  split; [exact body_secp256k1_scalar_verify|].
  split; [exact body_secp256k1_scalar_is_zero|].
  split; [exact body_secp256k1_scalar_is_one|].
  split; [exact body_secp256k1_scalar_is_even|].
  split; [exact body_secp256k1_scalar_is_high|].
  split; [exact body_secp256k1_scalar_eq|].
  split; [exact body_secp256k1_scalar_negate|].
  split; [exact body_secp256k1_scalar_half|].
  split; [exact body_secp256k1_scalar_add|].
  split; [exact body_secp256k1_scalar_cadd_bit|].
  split; [exact body_secp256k1_scalar_cond_negate|].
  split; [exact body_secp256k1_scalar_split_128|].
  split; [exact body_secp256k1_scalar_set_b32|].
  split; [exact body_secp256k1_scalar_set_b32_seckey|].
  split; [exact body_secp256k1_scalar_get_b32|].
  split; [exact body_secp256k1_scalar_mul_shift_var|].
  split; [exact body_secp256k1_scalar_split_lambda|].
  split; [exact body_secp256k1_scalar_get_bits_limb32|].
  split; [exact body_secp256k1_scalar_get_bits_var|].
  split; [exact body_secp256k1_scalar_inverse_var|].
  split; [exact body_secp256k1_scalar_inverse|].
  split; [exact body_secp256k1_fe_impl_add|].
  split; [exact body_secp256k1_modinv64_var|].
  exact body_secp256k1_modinv64.
Qed.

(** For a human reading a compile log rather than running [make axioms]: the
    same 10-name cone documented above, in this file's own words.  The gate
    ([audit/check.sh] gate 4) parses [audit/assumptions.log] -- the output of
    compiling [audit/assumptions.v], which closes over all 77 bodies -- NOT
    this line; this [Print Assumptions] is for the reader, not the gate. *)
Print Assumptions secp256k1_verified.
