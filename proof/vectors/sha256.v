(** * vectors.sha256: the SHA-256 known answers. *)
(** Copyright (C) 2026 remix7531
    SPDX-License-Identifier: MIT *)

(** Known-answer tests of [proof/specification.v], run by [vm_compute] under
    [make vectors], each in well under a second: the three FIPS 180-2
    example digests, the three BIP-340 tag midstates the C stores as
    constants, and the C's precomputed zero mask. *)

From Stdlib Require Import Lia.
From Stdlib Require Import List.
From Stdlib Require Import ZArith.
Import ListNotations.

Require secp256k1.specification.
Import specification.Math.
Import specification.Math.bytes.
Import specification.Math.sha256.
Import specification.Math.schnorr.

Open Scope Z_scope.
Local Open Scope array_scope.
Local Obligation Tactic := (repeat constructor; lia).

(* ================================================================= *)
(** ** The FIPS 180-2 examples -- one block, a spilling block, two blocks. *)

Lemma sha256_fips_abc :
  Z_of_bytes (sha256 (words 8 [97; 98; 99]
    (values_range := ltac:(repeat constructor; lia))) (ltac:(cbn; lia))) =
  0xba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad.
Proof.
  vm_compute.
  reflexivity.
Qed.

Lemma sha256_fips_empty :
  Z_of_bytes (sha256 (words 8 [] (values_range := Forall_nil _))
    (ltac:(cbn; lia))) =
  0xe3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855.
Proof.
  vm_compute.
  reflexivity.
Qed.

(** ["abcdbcdecdefdefgefghfghighijhijkijkljklmklmnlmnomnopnopq"], 56
    bytes, so the padding needs a second block. *)
Lemma sha256_fips_two_blocks :
  Z_of_bytes (sha256 (words 8
    [97; 98; 99; 100; 98; 99; 100; 101; 99; 100; 101; 102; 100; 101; 102; 103;
     101; 102; 103; 104; 102; 103; 104; 105; 103; 104; 105; 106; 104; 105; 106; 107;
     105; 106; 107; 108; 106; 107; 108; 109; 107; 108; 109; 110; 108; 109; 110; 111;
     109; 110; 111; 112; 110; 111; 112; 113]
    (values_range := ltac:(repeat constructor; lia)))
    (ltac:(cbn; lia))) =
  0x248d6a61d20638b8e5c026930c3e6039a33ce45964ff2167f6ecedd419db06c1.
Proof.
  vm_compute.
  reflexivity.
Qed.

(* ================================================================= *)
(** ** The BIP-340 midstates -- the three constants of [main_impl.h].

    Each is the state after the one block [sha256 tag ++ sha256 tag],
    stored by [src/modules/schnorrsig/main_impl.h] as a [uint32_t
    midstate[8]] literal. *)

Lemma midstate_bip340_nonce :
  let digest := sha256 tag_bip340_nonce (ltac:(cbn; lia)) in
  map word_val (sha256_state_words
    (sha256_midstate (array_of_list [digest ++ digest]))) =
  [0x46615b35; 0xf4bfbff7; 0x9f8dc671; 0x83627ab3;
   0x60217180; 0x57358661; 0x21a29e54; 0x68b07b4c].
Proof.
  vm_compute.
  reflexivity.
Qed.

Lemma midstate_bip340_aux :
  let digest := sha256 tag_bip340_aux (ltac:(cbn; lia)) in
  map word_val (sha256_state_words
    (sha256_midstate (array_of_list [digest ++ digest]))) =
  [0x24dd3219; 0x4eba7e70; 0xca0fabb9; 0x0fa3166d;
   0x3afbe4b1; 0x4c44df97; 0x4aac2739; 0x249e850a].
Proof.
  vm_compute.
  reflexivity.
Qed.

Lemma midstate_bip340_challenge :
  let digest := sha256 tag_bip340_challenge (ltac:(cbn; lia)) in
  map word_val (sha256_state_words
    (sha256_midstate (array_of_list [digest ++ digest]))) =
  [0x9cecba11; 0x23925381; 0x11679112; 0xd1627e0f;
   0x97c87550; 0x003cc765; 0x90f61164; 0x33e9b66a].
Proof.
  vm_compute.
  reflexivity.
Qed.

(* ================================================================= *)
(** ** The zero mask -- the C's [ZERO_MASK] is the aux hash of 32 zero bytes.

    BIP-340 says that absent auxiliary randomness is 32 zero bytes, and
    [nonce_function_bip340_impl] ([src/modules/schnorrsig/main_impl.h:57-65])
    stores the resulting mask as a constant.  Here it is re-derived. *)

Lemma zero_mask_is_aux_hash_of_zeros :
  bytes_Z (tagged_hash tag_bip340_aux
    (bytes_of_Z 0 32 (ltac:(lia)))
    (ltac:(cbn; lia)) (ltac:(cbn; lia))) =
  [84; 241; 105; 207; 201; 226; 229; 114;
   116; 128; 68; 31; 144; 186; 37; 196;
   136; 244; 97; 199; 11; 94; 165; 220;
   170; 247; 175; 105; 39; 10; 165; 20].
Proof.
  vm_compute.
  reflexivity.
Qed.

(* ================================================================= *)
(** ** Padding boundaries.

    These expected digests were independently computed by Python's
    hashlib.sha256 on the stated number of ASCII a bytes. The cases
    straddle the length-field boundary and a complete input block. *)

Lemma sha256_padding_boundary_55 :
  Z_of_bytes (sha256
    (array_repeat ((word_of_Z 8) 0x61 (ltac:(lia))) 55)
    (ltac:(cbn; lia))) =
  0x9f4390f8d30c2dd92ec9f095b65e2b9ae9b0a925a5258e241c9f1e910f734318.
Proof.
  vm_compute.
  reflexivity.
Qed.

Lemma sha256_padding_boundary_56 :
  Z_of_bytes (sha256
    (array_repeat ((word_of_Z 8) 0x61 (ltac:(lia))) 56)
    (ltac:(cbn; lia))) =
  0xb35439a4ac6f0948b6d6f9e3c6af0f5f590ce20f1bde7090ef7970686ec6738a.
Proof.
  vm_compute.
  reflexivity.
Qed.

Lemma sha256_padding_boundary_63 :
  Z_of_bytes (sha256
    (array_repeat ((word_of_Z 8) 0x61 (ltac:(lia))) 63)
    (ltac:(cbn; lia))) =
  0x7d3e74a05d7db15bce4ad9ec0658ea98e3f06eeecf16b4c6fff2da457ddc2f34.
Proof.
  vm_compute.
  reflexivity.
Qed.

Lemma sha256_padding_boundary_64 :
  Z_of_bytes (sha256
    (array_repeat ((word_of_Z 8) 0x61 (ltac:(lia))) 64)
    (ltac:(cbn; lia))) =
  0xffe054fe7ae0cb6dc65c3af9b61d5209f439851db43d0ba5997337df154668eb.
Proof.
  vm_compute.
  reflexivity.
Qed.

(** The hash interfaces reject lengths outside the FIPS byte domain. *)
Fail Definition sha256_oversized {n : nat} (msg : Array (Word 8) n)
    (too_long : 2^61 <= Z.of_nat n) : Array (Word 8) 32 :=
  sha256 msg (ltac:(lia)).

Fail Definition tagged_hash_oversized {n : nat} (msg : Array (Word 8) n)
    (too_long : 2^61 <= Z.of_nat (64 + n)) : Array (Word 8) 32 :=
  tagged_hash tag_bip340_aux msg (ltac:(cbn; lia)) (ltac:(lia)).

Fail Definition tagged_hash_oversized_tag {t : nat} (tag : Array (Word 8) t)
    (too_long : 2^61 <= Z.of_nat t) : Array (Word 8) 32 :=
  tagged_hash tag (array_nil : Array (Word 8) 0)
    (ltac:(lia)) (ltac:(cbn; lia)).
