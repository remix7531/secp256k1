/* Extraction unit for formal verification.
 *
 * Pulls in the library's real scalar arithmetic (scalar_impl.h), the struct-based
 * 128-bit helpers (int128_impl.h), the safegcd modular inverse (modinv64_impl.h),
 * and the 5x52 field (field_impl.h), compiled with
 * -DUSE_FORCE_WIDEMUL_INT128_STRUCT=1 and no assembly, so the unit is the pure-C
 * form clightgen accepts. Nothing is copied: the proofs reason about exactly the
 * code that ships. This is the single VERIFY-off AST for the whole proof tree; the
 * VERIFY_CHECK asserts and the verify-only helpers are absent here.
 *
 * Taking a function's address forces clightgen to retain it AND its whole call
 * graph; every primitive has internal linkage and would otherwise be pruned as
 * unused. extraction_targets[] below lists the call-graph roots. See Makefile.
 *
 * Extern-tables convention (decided ahead of the ecmult work): the precomputed
 * point tables (precomputed_ecmult*.c, ~2.4 MB of static initializers) must
 * NEVER be #included here -- they would reify into a multi-megabyte AST that
 * every proof file loads. When ecmult lands, this unit sees the tables as
 * `extern` declarations only (bare global variables, type but no initializer);
 * the table CONTENTS live in a second extraction unit (clight/tables.v, see
 * EXTRACT_SRCS in the Makefile) consumed by exactly one bridge file, with the
 * odd-multiples-of-G characterization proved by reflection over the group
 * model rather than axiomatized. */

#define SECP256K1_BUILD

/* Build in the libc-free (freestanding) configuration. SECP256K1_NO_LIBC makes the
 * library use its own pure-C memset/memcpy/memmove instead of libc and drops
 * <string.h>, so the proofs carry no trusted libc dependency (e.g.
 * secp256k1_memzero_explicit lowers to the self-contained byte loop). A normal
 * build leaves SECP256K1_NO_LIBC undefined and is byte-for-byte unchanged. */
#define SECP256K1_NO_LIBC

/* Neutralize `volatile` for the extraction. modinv64's normalize_62, and the scalar
 * cmov / cadd_bit / cond_negate constant-time helpers, mark a few locals `volatile`
 * purely as a constant-time hardening hint: it stops the compiler collapsing
 * branchless conditionals but does not change the value computed. VST/CompCert do
 * not model volatile local memory in their forward automation, so we drop the
 * qualifier; functional correctness, the property we verify, is identical. */
#define volatile

#include "secp256k1.h"

#include "util.h"

/* The scalar API wraps its invariant checks in SECP256K1_SCALAR_VERIFY, which
 * expands to a call to secp256k1_scalar_verify(): a no-op unless VERIFY is enabled
 * (its body is empty here), so it does not affect the production computation.
 * Neutralize the macro for the extraction so the AST is free of spurious no-op
 * calls. scalar.h is included first; its include guard then suppresses the original
 * definition when scalar_impl.h pulls it in, leaving our override in force where
 * scalar_4x64_impl.h uses it. */
#include "scalar.h"
#undef SECP256K1_SCALAR_VERIFY
#define SECP256K1_SCALAR_VERIFY(r)

#include "scalar_impl.h"
#include "int128_impl.h"
#include "modinv64_impl.h"
#include "field_impl.h"

/* Listing a function's address forces clightgen to emit it AND its whole call
 * graph, so to verify a function add its address below (no need to list helpers it
 * already calls). Grouped by subsystem in the same order as audit/assumptions.v and
 * the verif/ tree: field, int128, modinv, scalar. util has no roots of its own
 * (read_be64 / write_be64 / ctz64_var / memzero are pulled in transitively). */
const void * const extraction_targets[] = {
    /* field.h: the 5x52 (base 2^52) field. VERIFY-off, so secp256k1_fe_add is
     * #defined to its leaf impl secp256k1_fe_impl_add. Pulls the secp256k1_fe
     * struct into the AST. */
    (const void *)&secp256k1_fe_add,

    /* int128.h, signed. secp256k1_mul128 / secp256k1_i128_dissip_mul are not
     * declared in int128.h but are pulled in transitively (by i128_mul / i128_det). */
    (const void *)&secp256k1_i128_load,
    (const void *)&secp256k1_i128_mul,
    (const void *)&secp256k1_i128_accum_mul,
    (const void *)&secp256k1_i128_det,
    (const void *)&secp256k1_i128_rshift,
    (const void *)&secp256k1_i128_to_u64,
    (const void *)&secp256k1_i128_to_i64,
    (const void *)&secp256k1_i128_from_i64,
    (const void *)&secp256k1_i128_eq_var,
    (const void *)&secp256k1_i128_check_pow2,

    /* int128.h, unsigned. */
    (const void *)&secp256k1_u128_load,
    (const void *)&secp256k1_u128_mul,
    (const void *)&secp256k1_u128_accum_mul,
    (const void *)&secp256k1_u128_accum_u64,
    (const void *)&secp256k1_u128_rshift,
    (const void *)&secp256k1_u128_to_u64,
    (const void *)&secp256k1_u128_hi_u64,
    (const void *)&secp256k1_u128_from_u64,
    (const void *)&secp256k1_u128_check_bits,

    /* modinv64.h: variable-time modular inverse (safegcd). Retaining the driver
     * pulls its whole call graph (divsteps_62_var, update_de_62, update_fg_62_var,
     * normalize_62, signed62_assign, ctz64_var) and the shared signed i128 helpers.
     * VERIFY-off, so the verify-only helpers (abs / mul_62 / mul_cmp_62 /
     * det_check_pow2) are NOT in this AST. */
    (const void *)&secp256k1_modinv64_var,

    /* modinv64.h: the Jacobi symbol (safegcd variant). EXTRACTED, but its body proof
     * is OUTSTANDING (an Admitted lemma, NOT a trusted axiom): off the Schnorr path
     * and research-grade. Listed so the gap is EXPLICIT; deliberately NOT part of
     * the audited verified_surface. */
    (const void *)&secp256k1_jacobi64_maybe_var,

    /* scalar.h: the whole public scalar API, plus the modular inverse and the
     * scalar<->signed62 converters. secp256k1_scalar_inverse retains the
     * constant-time driver secp256k1_modinv64 (divsteps_59 + the helpers shared with
     * the _var path); the two converters are listed so their bodies are in the AST
     * to verify directly. */
    (const void *)&secp256k1_scalar_clear,
    (const void *)&secp256k1_scalar_set_b32,
    (const void *)&secp256k1_scalar_set_b32_seckey,
    (const void *)&secp256k1_scalar_set_int,
    (const void *)&secp256k1_scalar_get_b32,
    (const void *)&secp256k1_scalar_add,
    (const void *)&secp256k1_scalar_cadd_bit,
    (const void *)&secp256k1_scalar_mul,
    (const void *)&secp256k1_scalar_negate,
    (const void *)&secp256k1_scalar_half,
    (const void *)&secp256k1_scalar_is_zero,
    (const void *)&secp256k1_scalar_is_one,
    (const void *)&secp256k1_scalar_is_even,
    (const void *)&secp256k1_scalar_is_high,
    (const void *)&secp256k1_scalar_cond_negate,
    (const void *)&secp256k1_scalar_eq,
    (const void *)&secp256k1_scalar_split_128,
    (const void *)&secp256k1_scalar_split_lambda,
    (const void *)&secp256k1_scalar_mul_shift_var,
    (const void *)&secp256k1_scalar_cmov,
    (const void *)&secp256k1_scalar_verify,
    (const void *)&secp256k1_scalar_get_bits_limb32,
    (const void *)&secp256k1_scalar_get_bits_var,
    (const void *)&secp256k1_scalar_to_signed62,
    (const void *)&secp256k1_scalar_from_signed62,
    (const void *)&secp256k1_scalar_inverse_var,
    (const void *)&secp256k1_scalar_inverse
};
