(** * model.constants: the secp256k1 curve numeric constants. *)
(** Copyright (C) 2026 remix7531
    SPDX-License-Identifier: MIT *)

(** Every trust-sensitive magic number of the proof, gathered in one file a
    reviewer can cross-check against an external source of truth:

    - the field prime [p] and the group order [n] against the SEC2 standard
      (the decimal value is given in a comment beside each);
    - the per-limb tables ([N_*], [N_C_*], [N_H_*]) against the C library
      headers ([src/scalar_4x64_impl.h]) they mirror limb-for-limb;
    - the derived facts ([n]'s limb decomposition, [n = 2*floor(n/2)+1],
      [2^256 - n]'s limbs) as machine-checked lemmas, so a reviewer checks a
      formula rather than trusting extra digits.

    The headline values ([p], [n], [lambda], the split-lambda basis) are sealed
    with a file-local [Opaque] at the end of the file: within this file they are
    never unfolded into their digits, and downstream proofs are expected to go
    through the exported lemmas (or the [secp256k1_N_val] rewrite bridge) rather
    than the digits.  The seal is deliberately not [Global]: existing proofs may
    still [unfold] the values where convenient.  The per-limb tables are left
    transparent -- downstream proofs match them against the literals in the
    Clight AST. *)

Require Import ZArith.
Require Import Coq.ZArith.Znumtheory.
Require Import Lia.
Require Import secp256k1.theory.primality.n.

Open Scope Z_scope.

(* ================================================================= *)
(** ** Field prime -- [secp256k1_P]. *)

(** The secp256k1 field modulus [p = 2^256 - 2^32 - 977]. *)
Definition secp256k1_P : Z := 2 ^ 256 - 2 ^ 32 - 977.

(** [p] is a positive modulus below [2^256]. *)
Lemma secp256k1_P_range : 0 < secp256k1_P < 2 ^ 256.
Proof.
  unfold secp256k1_P.
  assert (H32 : 2 ^ 32 = 4294967296) by reflexivity.
  assert (H256 : 2 ^ 256 = 2 ^ 32 * 2 ^ 224)
    by (rewrite <- Z.pow_add_r by lia; reflexivity).
  assert (H224 : 2 <= 2 ^ 224)
    by (replace 2 with (2 ^ 1) at 1 by reflexivity; apply Z.pow_le_mono_r; lia).
  assert (2 ^ 256 >= 2 * 2 ^ 32) by (rewrite H256; nia).
  lia.
Qed.

(* ================================================================= *)
(** ** Group order -- [secp256k1_N]. *)

(** The secp256k1 group order [n] (SEC2).
      hex : FFFFFFFF FFFFFFFF FFFFFFFF FFFFFFFE
            BAAEDCE6 AF48A03B BFD25E8C D0364141
      dec : 115792089237316195423570985008687907852
            837564279074904382605163141518161494337 *)
Definition secp256k1_N : Z :=
  0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEBAAEDCE6AF48A03BBFD25E8CD0364141.

(** [n] is a positive modulus below [2^256]. *)
Lemma secp256k1_N_range : 0 < secp256k1_N < 2 ^ 256.
Proof. unfold secp256k1_N. lia. Qed.

(** The GLV window bound: [n] exceeds [2^128], needed by
    [secp256k1_scalar_split_lambda]'s output-range split. *)
Lemma N_gt_2_128 : 2 ^ 128 < secp256k1_N.
Proof. unfold secp256k1_N; lia. Qed.

(** Value bridge (decimal), registered with [rep_lia] so automation can expand
    [secp256k1_N] by rewriting even after it is sealed below. *)
Lemma secp256k1_N_val :
  secp256k1_N = 115792089237316195423570985008687907852837564279074904382605163141518161494337.
Proof. reflexivity. Qed.

(* ----------------------------------------------------------------- *)
(** *** Group order limbs -- [N_0 .. N_3] (mirror [SECP256K1_N_*]). *)

(** Limbs of [n], byte-for-byte the [SECP256K1_N_0..3] macros of
    [src/scalar_4x64_impl.h]. *)
Definition N_0 : Z := 0xBFD25E8CD0364141.
Definition N_1 : Z := 0xBAAEDCE6AF48A03B.
Definition N_2 : Z := 0xFFFFFFFFFFFFFFFE.
Definition N_3 : Z := 0xFFFFFFFFFFFFFFFF.

(** [n] decomposes into its four 64-bit limbs. *)
Lemma secp256k1_N_limbs :
  secp256k1_N = N_0 + N_1 * 2^64 + N_2 * 2^128 + N_3 * 2^192.
Proof. unfold secp256k1_N, N_0, N_1, N_2, N_3. lia. Qed.

(** Limbs of [2^256 - n] (the "complement"), matching the C's [~N_i (+1)]. *)
Definition N_C_0 : Z := 0x402DA1732FC9BEBF.
Definition N_C_1 : Z := 0x4551231950B75FC4.
Definition N_C_2 : Z := 1.

(** [2^256 - n] decomposes into its three 64-bit limbs. *)
Lemma secp256k1_N_C_limbs :
  2^256 - secp256k1_N = N_C_0 + N_C_1 * 2^64 + N_C_2 * 2^128.
Proof. unfold secp256k1_N, N_C_0, N_C_1, N_C_2. lia. Qed.

(** Range facts for the limb constants. *)
Lemma N_0_range : 0 <= N_0 < 2^64. Proof. unfold N_0; lia. Qed.
Lemma N_1_range : 0 <= N_1 < 2^64. Proof. unfold N_1; lia. Qed.
Lemma N_2_range : 0 <= N_2 < 2^64. Proof. unfold N_2; lia. Qed.
Lemma N_3_range : 0 <= N_3 < 2^64. Proof. unfold N_3; lia. Qed.
Lemma N_C_0_range : 0 <= N_C_0 < 2^64. Proof. unfold N_C_0; lia. Qed.
Lemma N_C_1_range : 0 <= N_C_1 < 2^64. Proof. unfold N_C_1; lia. Qed.
Lemma N_C_2_range : 0 <= N_C_2 < 2^64. Proof. unfold N_C_2; lia. Qed.

(* ================================================================= *)
(** ** Half the group order -- [secp256k1_N_H] = [floor(n/2)]. *)

(** Limbs of [floor(n/2)] (the [SECP256K1_N_H_*] macros), used by
    [secp256k1_scalar_is_high] and [secp256k1_scalar_half]. *)
Definition N_H_0 : Z := 0xDFE92F46681B20A0.
Definition N_H_1 : Z := 0x5D576E7357A4501D.
Definition N_H_2 : Z := 0xFFFFFFFFFFFFFFFF.
Definition N_H_3 : Z := 0x7FFFFFFFFFFFFFFF.

(** [floor(n/2)]: the threshold above which a scalar is "high" (as the sum of
    its limbs; [secp256k1_N_as_2H] ties it to [n]). *)
Definition secp256k1_N_H : Z :=
  N_H_0 + N_H_1 * 2^64 + N_H_2 * 2^128 + N_H_3 * 2^192.

(** [n] is odd, so [n = 2*floor(n/2) + 1]. *)
Lemma secp256k1_N_as_2H : secp256k1_N = 2 * secp256k1_N_H + 1.
Proof. unfold secp256k1_N, secp256k1_N_H, N_H_0, N_H_1, N_H_2, N_H_3. lia. Qed.

Lemma secp256k1_N_H_range : 0 <= secp256k1_N_H < secp256k1_N.
Proof. unfold secp256k1_N, secp256k1_N_H, N_H_0, N_H_1, N_H_2, N_H_3. lia. Qed.

(* ================================================================= *)
(** ** Group order primality -- [secp256k1_N_prime]. *)

(** The group order [n] is prime, proved by a coqprime Pocklington
    certificate for the exact literal ([theory/primality/n.v]'s
    [secp256k1_N_prime_cert]; checks in about 1 second).  This is NOT a
    project [Axiom]: [Print Assumptions secp256k1_N_prime] closes over
    [secp256k1_N_prime_cert]'s own proof and lists Rocq's primitive 63-bit
    integer axioms ([Uint63Axioms.*] / [PrimInt63.*], pulled in by
    coqprime's [BigN]-based certificate checker) instead -- the same trust
    surface any coqprime user accepts, whitelisted as foundational
    (toolchain) rather than project trust in [audit/AXIOM_WHITELIST].

    It is used to drop the coprimality precondition from the public scalar
    inverse specs: since [n] is prime, every nonzero scalar in [[0, n)] is
    coprime to [n], so [secp256k1_scalar_inverse] / [_var] need only the trivial
    "input is a scalar" hypothesis. *)
Lemma secp256k1_N_prime : prime secp256k1_N.
Proof.
  exact secp256k1_N_prime_cert.
Qed.

(* ================================================================= *)
(** ** GLV endomorphism constant -- [secp256k1_lambda] (cube root of 1 mod n). *)

(** [lambda]: the GLV endomorphism scalar (a primitive cube root of unity
    mod [n]), used by [secp256k1_scalar_split_lambda].
      hex : 5363AD4C C05C30E0 A5261C02 8812645A
            122E22EA 20816678 DF02967C 1B23BD72 *)
Definition secp256k1_lambda : Z :=
  0x5363AD4CC05C30E0A5261C028812645A122E22EA20816678DF02967C1B23BD72.

(* ================================================================= *)
(** ** split_lambda basis -- [minus_b1] / [minus_b2] / [g1] / [g2] tables. *)

(** The remaining [secp256k1_scalar_split_lambda] tables (the C [minus_b1],
    [minus_b2], [g1], [g2] file-scope constants), as raw 256-bit values. *)
Definition minus_b1_z : Z :=
  0x00000000000000000000000000000000E4437ED6010E88286F547FA90ABFE4C3.
Definition minus_b2_z : Z :=
  0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFE8A280AC50774346DD765CDA83DB1562C.
Definition g1_z : Z :=
  0x3086D221A7D46BCDE86C90E49284EB153DAA8A1471E8CA7FE893209A45DBB031.
Definition g2_z : Z :=
  0xE4437ED6010E88286F547FA90ABFE4C4221208AC9DF506C61571B4AE8AC47F71.

(* ================================================================= *)
(** ** Sealing -- the headline values are opaque within this file; the limb
    tables stay transparent (matched against the Clight AST downstream).
    File-local on purpose: a [Global] seal would break the existing downstream
    [unfold] sites (and vanilla Rocq's [Opaque] takes no [#[export]] -- the
    previous spelling only parsed under floyd and never propagated anyway). *)

(** Registered into floyd's [rep_lia] autorewrite database.  This file stays
    VST-free: rewrite databases are string-keyed and merge at use site, so the
    registration compiles here and takes effect wherever floyd is loaded. *)
#[export] Hint Rewrite secp256k1_N_val : rep_lia.

Opaque secp256k1_P secp256k1_N secp256k1_N_H secp256k1_lambda
       minus_b1_z minus_b2_z g1_z g2_z.
