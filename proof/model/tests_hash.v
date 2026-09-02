(** * model.tests_hash: known-answer checks for [model.hash]. *)
(** Copyright (C) 2026 remix7531
    SPDX-License-Identifier: MIT *)

(** Executable sanity checks of [model/hash.v] against independently known
    values, so a reviewer can see what the SHA-256 / HMAC-SHA256 / RFC 6979
    model means before reading any VST proof.  Every check is a closed
    equation discharged by [vm_compute; reflexivity]; each names where its
    expected value comes from.  This file is VST-free (imports only
    [model.hash] and the byte<->[Z] bridge [theory.bytes]) and carries no
    axioms. *)

From Stdlib Require Import ZArith.
From Stdlib Require Import List.
Import ListNotations.

Require Import secp256k1.theory.bytes.
Require Import secp256k1.model.hash.

Open Scope Z_scope.

(* ================================================================= *)
(** ** SHA-256 message vectors -- [sha256], against FIPS 180-4 / the NIST
    CAVS short-message test vectors. *)

(** The empty message ([sha256("")]). *)
Definition msg_empty : list Z := [].

(** ["abc"], FIPS 180-4's one-block example message. *)
Definition msg_abc : list Z := [97; 98; 99].

(** ["abcdbcdecdefdefgefghfghighijhijkijkljklmklmnlmnomnopnopq"] (56 bytes,
    the NIST CAVS two-block short-message vector). *)
Definition msg_multiblock : list Z :=
  [ 97; 98; 99; 100; 98; 99; 100; 101; 99; 100; 101; 102; 100; 101; 102; 103;
    101; 102; 103; 104; 102; 103; 104; 105; 103; 104; 105; 106; 104; 105;
    106; 107; 105; 106; 107; 108; 106; 107; 108; 109; 107; 108; 109; 110;
    108; 109; 110; 111; 109; 110; 111; 112; 110; 111; 112; 113 ].

(** [sha256("")] (FIPS 180-4 / NIST CAVS). *)
Lemma chk_sha256_empty :
  Z_of_be_bytes (sha256 msg_empty) =
  0xe3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855.
Proof. vm_compute. reflexivity. Qed.

(** [sha256("abc")] (FIPS 180-4's own worked example). *)
Lemma chk_sha256_abc :
  Z_of_be_bytes (sha256 msg_abc) =
  0xba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad.
Proof. vm_compute. reflexivity. Qed.

(** [sha256] of the 56-byte multi-block vector (NIST CAVS short-message
    test, two 64-byte blocks after padding). *)
Lemma chk_sha256_multiblock :
  Z_of_be_bytes (sha256 msg_multiblock) =
  0x248d6a61d20638b8e5c026930c3e6039a33ce45964ff2167f6ecedd419db06c1.
Proof. vm_compute. reflexivity. Qed.

(* ================================================================= *)
(** ** BIP-340 tagged midstates -- [sha256_midstate], recomputed as
    [sha256(tag) || sha256(tag)] compressed from the IV and compared against
    the hard-coded [uint32_t midstate[8]] constants in
    [src/modules/schnorrsig/main_impl.h].  This is the check that catches a
    wrong [tagged_hash] or a wrong midstate constant: the expected words were
    independently cross-checked by re-deriving them with a from-scratch
    Python SHA-256 compression function (not this model, not [hashlib]'s
    opaque digest), applied to [sha256(tag) || sha256(tag)]. *)

(** ["BIP0340/nonce"]. *)
Definition tag_nonce : list Z :=
  [66; 73; 80; 48; 51; 52; 48; 47; 110; 111; 110; 99; 101].

(** ["BIP0340/aux"]. *)
Definition tag_aux : list Z :=
  [66; 73; 80; 48; 51; 52; 48; 47; 97; 117; 120].

(** ["BIP0340/challenge"]. *)
Definition tag_challenge : list Z :=
  [66; 73; 80; 48; 51; 52; 48; 47; 99; 104; 97; 108; 108; 101; 110; 103; 101].

(** The nonce-tag midstate ([main_impl.h:16-24]'s [midstate[8]] in
    [secp256k1_nonce_function_bip340_sha256_tagged]). *)
Lemma chk_midstate_nonce :
  sha256_midstate (sha256 tag_nonce ++ sha256 tag_nonce) 1 =
  [ 0x46615b35; 0xf4bfbff7; 0x9f8dc671; 0x83627ab3;
    0x60217180; 0x57358661; 0x21a29e54; 0x68b07b4c ].
Proof. vm_compute. reflexivity. Qed.

(** The aux-tag midstate ([main_impl.h:26-32]'s [midstate[8]] in
    [secp256k1_nonce_function_bip340_sha256_tagged_aux]). *)
Lemma chk_midstate_aux :
  sha256_midstate (sha256 tag_aux ++ sha256 tag_aux) 1 =
  [ 0x24dd3219; 0x4eba7e70; 0xca0fabb9; 0x0fa3166d;
    0x3afbe4b1; 0x4c44df97; 0x4aac2739; 0x249e850a ].
Proof. vm_compute. reflexivity. Qed.

(** The challenge-tag midstate ([main_impl.h:98-104]'s [midstate[8]] in
    [secp256k1_schnorrsig_sha256_tagged]). *)
Lemma chk_midstate_challenge :
  sha256_midstate (sha256 tag_challenge ++ sha256 tag_challenge) 1 =
  [ 0x9cecba11; 0x23925381; 0x11679112; 0xd1627e0f;
    0x97c87550; 0x003cc765; 0x90f61164; 0x33e9b66a ].
Proof. vm_compute. reflexivity. Qed.

(* ================================================================= *)
(** ** HMAC-SHA256 -- [hmac_sha256], against RFC 4231's test cases. *)

(** RFC 4231 test case 1: key = [0x0b] x 20, data = ["Hi There"]. *)
Lemma chk_hmac_rfc4231_case1 :
  Z_of_be_bytes (hmac_sha256 (repeat 11 20) [72; 105; 32; 84; 104; 101; 114; 101]) =
  0xb0344c61d8db38535ca8afceaf0bf12b881dc200c9833da726e9376c2e32cff7.
Proof. vm_compute. reflexivity. Qed.

(** RFC 4231 test case 2: key = ["Jefe"],
    data = ["what do ya want for nothing?"]. *)
Lemma chk_hmac_rfc4231_case2 :
  Z_of_be_bytes
    (hmac_sha256 [74; 101; 102; 101]
       [ 119; 104; 97; 116; 32; 100; 111; 32; 121; 97; 32; 119; 97; 110; 116;
         32; 102; 111; 114; 32; 110; 111; 116; 104; 105; 110; 103; 63 ]) =
  0x5bdcc146bf60754e6a042426089575c75a003f089d2739839dec58b964ec3843.
Proof. vm_compute. reflexivity. Qed.

(** RFC 4231 test case 4: key = [0x01 .. 0x19] (25 bytes),
    data = [0xcd] x 50. *)
Lemma chk_hmac_rfc4231_case4 :
  Z_of_be_bytes
    (hmac_sha256
       [ 1; 2; 3; 4; 5; 6; 7; 8; 9; 10; 11; 12; 13; 14; 15; 16; 17; 18; 19;
         20; 21; 22; 23; 24; 25 ]
       (repeat 205 50)) =
  0x82558a389a443c0ea4cc819899f2083a85f0faa3e578f8077a2e3ff46729665b.
Proof. vm_compute. reflexivity. Qed.

(* ================================================================= *)
(** ** RFC 6979 HMAC-DRBG round trip -- [rfc6979_init] / [rfc6979_generate].
    [rfc6979_init] is the generic HMAC-DRBG seeding of RFC 6979 section 3.2
    steps b/c/d/f, over an arbitrary demo key ([[1;2;3;4]]; this model layer
    does not do the private-key/message-hash-to-seed mapping, so no EC
    domain parameters are involved here).  The expected [V]/[K] and the two
    generated outputs were cross-checked against an independent
    re-implementation of the same RFC 6979 section 3.2 steps a-h, built
    directly from the RFC text with Python's own [hmac]/[hashlib], not by
    re-running this model's [hmac_sha256]. *)

Definition rfc_key : list Z := [1; 2; 3; 4].

(** [V] after [rfc6979_init]. *)
Lemma chk_rfc6979_init_v :
  Z_of_be_bytes (rfc6979_v (rfc6979_init rfc_key)) =
  0xb1e7df8d863ece5ffa25fec2ac564e217f854947d0ba1eeec9031e60056aab40.
Proof. vm_compute. reflexivity. Qed.

(** [K] after [rfc6979_init]. *)
Lemma chk_rfc6979_init_k :
  Z_of_be_bytes (rfc6979_k (rfc6979_init rfc_key)) =
  0xe0e0bb1e508bd4066387ba8b7f0976e9340163a873da1f912570c5c567bf286b.
Proof. vm_compute. reflexivity. Qed.

(** The first [rfc6979_generate] call (32 bytes, no retry chain yet). *)
Lemma chk_rfc6979_gen1 :
  Z_of_be_bytes (fst (rfc6979_generate (rfc6979_init rfc_key) 32)) =
  0x5f440f9338798e38923f21bde6b1cfd12d44e11f22f27b571e4bc9f6d367cde9.
Proof. vm_compute. reflexivity. Qed.

(** The second [rfc6979_generate] call, on the state left by the first
    (its [retry] flag is now set, so this call extends the chain with the
    extra [0]-tagged HMAC round before emitting). *)
Lemma chk_rfc6979_gen2 :
  Z_of_be_bytes
    (fst (rfc6979_generate (snd (rfc6979_generate (rfc6979_init rfc_key) 32)) 32)) =
  0x512f49bd73c75bff42baf25cffb0477a8d15c7f0f4f44d86ba38874d30b527b8.
Proof. vm_compute. reflexivity. Qed.
