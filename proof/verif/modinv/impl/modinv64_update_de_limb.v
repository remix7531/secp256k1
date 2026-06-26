(** * verif.modinv.impl.modinv64_update_de_limb: body proof for secp256k1_modinv64_update_de_limb. *)
(** Copyright (C) 2026 remix7531
    SPDX-License-Identifier: MIT *)

(** One limb-n accumulation step extracted from secp256k1_modinv64_update_de_62
    (so the four identical per-limb blocks of that function become forward_calls). *)

Require Import secp256k1.vst.base.
Require Import secp256k1.contract.int128.
Require Import secp256k1.model.int128.
Require Import secp256k1.contract.helper.notations.
Require Import secp256k1.contract.impl.modinv.
Require Import secp256k1.contract.gprog.modinv.
Require Import secp256k1.theory.extra_math.
Require Import secp256k1.tactics.core.
Require Import secp256k1.tactics.hygiene.

Lemma body_secp256k1_modinv64_update_de_limb:
  semax_body Vprog Gprog f_secp256k1_modinv64_update_de_limb spec_secp256k1_modinv64_update_de_limb.
Proof.
  start_function.

  (* ===== cd += u*dn + v*en; ce += q*dn + r*en =====
     each i128_accum_mul yields a fresh Int128 to Intros; the overflow PREs
     discharge from the spec's running-sum bounds + the chain *)

  (* cd += u*dn *)
  forward_call (ptrcd, cd0, u, dn, shcd).
  Intros cd1.
  (* cd += v*en *)
  forward_call (ptrcd, cd1, v, en, shcd).
  Intros cd2.

  (* ce += q*dn *)
  forward_call (ptrce, ce0, q, dn, shce).
  Intros ce1.
  (* ce += r*en *)
  forward_call (ptrce, ce1, r, en, shce).
  Intros ce2.

  (* ===== if (mod_n) { cd += mod_n*md; ce += mod_n*me; } ===== *)

  (* if (mod_n) *)
  forward_if.
  - (* branch: mod_n <> 0 -- fold in the modulus terms *)
    specialize (H3 H9'). specialize (H4 H9').
    (* cd += mod_n*md *)
    forward_call (ptrcd, cd2, mod_n, md, shcd).
    Intros cd3.
    (* ce += mod_n*me *)
    forward_call (ptrce, ce2, mod_n, me, shce).
    Intros ce3.
    Exists cd3 ce3.
    rewrite !(proj2 (Z.eqb_neq (i64_val mod_n) 0) H9').
    entailer!!.
  - (* branch: mod_n = 0 -- the modulus terms vanish *)
    forward.
    apply (f_equal Int64.signed) in H9.
    rewrite Int64.signed_repr in H9 by (pose proof (i64_range mod_n); rep_lia).
    rewrite Int64.signed_zero in H9.
    Exists cd2 ce2.
    rewrite H9, Z.eqb_refl.
    entailer!!.
Qed.
