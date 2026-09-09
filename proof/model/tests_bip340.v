(** * model.tests_bip340: known-answer checks for [model.bip340]. *)
(** Copyright (C) 2026 remix7531
    SPDX-License-Identifier: MIT *)

(** Executable sanity checks of [model/bip340.v] against independently known
    values, so a reviewer can see what the BIP-340 nonce / challenge / sign /
    verify / x-only model means before reading any VST proof.  Every check is
    a closed equation discharged by [vm_compute; reflexivity]; each names
    where its expected value comes from.  This file is VST-free (imports
    [model.bip340] and [theory.bytes]) and carries no axioms.

    COST -- WHY THERE IS NO "bip340_sign reproduces the vector" /
    "bip340_verify returns true" CHECK HERE.  [bip340_verify]'s
    [ecmult_model] step, and [bip340_sign]'s nonce-point step, each run
    [model.group]'s [smul] on a near-uniform 256-bit scalar (the hash-derived
    challenge / nonce / signature value -- never a small number the way a toy
    private key can be).  [model/tests_group.v]'s own header measured
    [fe_inv] (the [pow_mod] Fermat-inverse engine every [padd]/[pdouble] call
    makes once) at about 6 seconds under [vm_compute], and a full-width
    [smul] (~380 point operations) at "on the order of ... tens of minutes";
    that file's KAT list ends up EXCLUDING [smul secp256k1_N G] entirely for
    exactly this reason ("outside any reasonable build-step
    budget"), not even placing it in a slow file.  A single passing
    [bip340_verify] call needs TWO such [smul]s; a single [bip340_sign] call
    needs one (the nonce point -- always full-width) plus, unless the secret
    key happens to be tiny, a second for [bip340_keygen].  Three BIP-340
    test-vectors.csv vectors, each checked both ways, would therefore cost
    several CPU-hours combined. A probe (a single
    [on_curve (smul k G)] at a real 256-bit [k], run standalone) did not
    finish inside a 120-second budget, consistent with that estimate. These
    checks remain unverified.

    What IS cheap, and checked below: the [zero_mask32] constant and the
    [aux_rand32 == NULL] branch it feeds (pure SHA-256, no field/group ops);
    one BIP-340 vector whose [bip340_verify] call is rejected before any
    field or group op runs at all (an out-of-range signature field, a plain
    integer comparison); one vector whose public key is rejected by
    [xonly_parse] the same cheap way; and the [xonly_parse]/[xonly_serialize]
    round trip on a REAL vector's public key, which costs exactly ONE
    [fe_sqrt] (one [lift_x_even] call, ~6-10s per the group file's own
    measurement of the identical call on [G]'s x coordinate -- cheap enough
    to keep in this fast file, not a dedicated slow one). *)

From Stdlib Require Import ZArith.
From Stdlib Require Import List.
Import ListNotations.

Require Import secp256k1.theory.bytes.
Require Import secp256k1.model.hash.
Require Import secp256k1.model.group.
Require Import secp256k1.model.bip340.

Open Scope Z_scope.

(* ================================================================= *)
(** ** The [aux_rand32 == NULL] branch -- [zero_mask32] / [bip340_nonce].

    [zero_mask32]'s doc comment in [model/bip340.v] claims it is
    literally [TaggedHash("BIP0340/aux", 0x00...00)], transcribed from the
    C's own comment on its [ZERO_MASK] constant
    ([src/modules/schnorrsig/main_impl.h:57-65]); this RECOMPUTES that hash
    from [tag_bip340_aux] and 32 zero bytes and checks it against the
    literal, the check that catches a transcription error in either. *)

(** [zero_mask32] really is [tagged_hash "BIP0340/aux" (32 zero bytes)]. *)
Lemma chk_zero_mask32_is_tagged_hash_of_zero32 :
  zero_mask32 = tagged_hash tag_bip340_aux (repeat 0 32).
Proof. vm_compute. reflexivity. Qed.

(** [bip340_nonce]'s [None] branch (no auxiliary randomness supplied) agrees
    with explicitly passing 32 zero bytes as the auxiliary randomness -- the
    C-level equivalence [zero_mask32] exists to shortcut.  Checked on
    arbitrary concrete 32-byte [key32]/[pk32]/[msg] (their values do not
    matter to the identity; only that [None] and [Some (32 zero bytes)] take
    the same path through [xor_bytes] and [tagged_hash]). *)
Lemma chk_bip340_nonce_none_matches_explicit_zero32 :
  bip340_nonce None (repeat 1 32) (repeat 2 32) (repeat 3 32)
  = bip340_nonce (Some (repeat 0 32)) (repeat 1 32) (repeat 2 32) (repeat 3 32).
Proof. vm_compute. reflexivity. Qed.

(* ================================================================= *)
(** ** A failing vector, cheaply -- [bip340_verify], BIP-340
    test-vectors.csv index 12 ("sig[0:32] is equal to field size").

    [r32] here is exactly [secp256k1_P] (BIP-340 test-vectors.csv, row 12's
    signature), so [bip340_verify]'s very first range check
    ([rval < secp256k1_P]) already fails -- no [fe_sqrt], no [smul], not even
    a [Point] is built.  [pk32] is the row's own public key, converted with
    [fe_of_bytes] to match [bip340_verify]'s [Fe] parameter (it is never
    forced: the range check short-circuits before that branch is reached). *)

(** BIP-340 test-vectors.csv row 12's public key. *)
Definition v12_pk : Fe :=
  fe_of_bytes
    (be_bytes_of_Z
       0xDFF1D77F2A671C5F36183726DB2341BE58FEAE1DA2DECED843240F7B502BA659
       32).

(** Row 12's message. *)
Definition v12_msg : list Z :=
  be_bytes_of_Z
    0x243F6A8885A308D313198A2E03707344A4093822299F31D0082EFA98EC4E6C89
    32.

(** Row 12's 64-byte signature: [r = secp256k1_P] (out of range), the [s]
    half is otherwise a well-formed value. *)
Definition v12_sig : list Z :=
  be_bytes_of_Z
    0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEFFFFFC2F69E89B4C5564D00349106B8497785DD7D1D713A8AE82B32FA79D5F7FC407D39B
    64.

(** [bip340_verify] rejects row 12 (BIP-340 test-vectors.csv index 12,
    comment "sig[0:32] is equal to field size"). *)
Lemma chk_bip340_verify_rejects_v12_sig_field_size :
  bip340_verify v12_sig v12_msg v12_pk = false.
Proof. vm_compute. reflexivity. Qed.

(* ================================================================= *)
(** ** A rejected public key, cheaply -- [xonly_parse], BIP-340
    test-vectors.csv index 14 ("public key is not a valid X coordinate
    because it exceeds the field size").

    Row 14's public key bytes decode to exactly [secp256k1_P + 1]:
    [xonly_parse]'s own leading range check ([Z_of_be_bytes input32 >=
    secp256k1_P]) rejects it before [fe_sqrt] ever runs, the [xonly_parse]
    counterpart to [chk_bip340_verify_rejects_v12_sig_field_size] above. *)

(** BIP-340 test-vectors.csv row 14's public key, [secp256k1_P + 1] read as
    32 big-endian bytes. *)
Definition v14_pk_bytes : list Z :=
  be_bytes_of_Z
    0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEFFFFFC30
    32.

(** [xonly_parse] rejects row 14 (BIP-340 test-vectors.csv index 14). *)
Lemma chk_xonly_parse_rejects_v14_oversize_x :
  xonly_parse v14_pk_bytes = None.
Proof. vm_compute. reflexivity. Qed.

(* ================================================================= *)
(** ** [xonly_parse] / [xonly_serialize] round trip on a passing vector's
    public key -- BIP-340 test-vectors.csv index 0.

    One [fe_sqrt] ([lift_x_even]'s square-root call), the same cost
    [model/tests_slow_group.v]'s [chk_liftx_even_G] measured at ~6-10s on
    [G]'s own x coordinate; cheap enough to sit in this fast file alongside
    the near-free checks above rather than a dedicated slow file. *)

(** BIP-340 test-vectors.csv row 0's public key (secret key [3]'s x-only
    pubkey). *)
Definition v0_pk_bytes : list Z :=
  be_bytes_of_Z
    0xF9308A019258C31049344F85F89D5229B531C845836F99B08601F113BCE036F9
    32.

(** Parsing then re-serializing row 0's public key reproduces the same 32
    bytes -- [xonly_parse] always lifts to the EVEN-y point, and
    [xonly_serialize] only ever emits a point's x coordinate, so the round
    trip holds for any valid x-only encoding; row 0's is the witness. *)
Lemma chk_xonly_roundtrip_v0_pk :
  match xonly_parse v0_pk_bytes with
  | Some pt => xonly_serialize pt = Some v0_pk_bytes
  | None => False
  end.
Proof. vm_compute. reflexivity. Qed.
