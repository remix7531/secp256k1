(** * model.hash: pure functional model of SHA-256, HMAC-SHA256 and RFC 6979. *)
(** Copyright (C) 2026 remix7531
    SPDX-License-Identifier: MIT *)

(** The trust boundary for the hash subsystem: SHA-256 as a pure function
    [list Z -> list Z] over byte lists (each element in [[0, 256)]), built
    exactly the way [src/hash_impl.h] builds it -- 64-round compression,
    length-suffix padding, and the [tag||tag||msg] BIP-340 tagged-hash
    trick -- plus HMAC-SHA256 and the RFC 6979 HMAC-DRBG layered on top.
    [theory.hash.sha256_bits] carries the 32-bit word arithmetic
    ([rotr32]/[shr32]/[xor32]/[and32]/[or32]) this file composes; the
    byte<->[Z] conversions come from [theory.bytes].

    FUNCTION-POINTER DISCLAIMER: the fork reaches the compression step
    through a function pointer ([secp256k1_hash_ctx.fn_sha256_compression],
    [src/hash.h:13-15]), set once at [src/hash_impl.h:141] and pinned in the
    static context to [secp256k1_sha256_transform] at [src/secp256k1.c:71].
    This model does NOT model the pointer indirection -- it models the ONE
    function the pointer is pinned to.  A caller that swapped the
    compression function (via [secp256k1_context_set_sha256_compression],
    itself outside this Schnorr surface) is outside this file's claim. *)

Require Import ZArith.
Require Import Lia.
Require Import List.
Import ListNotations.
Require Import secp256k1.theory.bytes.
Require Import secp256k1.theory.hash.sha256_bits.

Open Scope Z_scope.

(* ================================================================= *)
(** ** SHA-256 constants -- [sha256_iv] / [sha256_k].
    Both copied byte-for-byte from [secp256k1_sha256_initialize]
    ([src/hash_impl.h:30-40]) and the [Round] call sites of
    [secp256k1_sha256_transform_impl] ([src/hash_impl.h:50-130]).
    See https://wuille.net/posts/secp256k1-tutorial/#32-the-main-library-code-secp256k1c *)

(** The eight SHA-256 initial hash values (the fractional parts of the
    square roots of the first eight primes, in IEEE-754 fixed-point). *)
Definition sha256_iv : list Z :=
  [ 0x6a09e667; 0xbb67ae85; 0x3c6ef372; 0xa54ff53a;
    0x510e527f; 0x9b05688c; 0x1f83d9ab; 0x5be0cd19 ].

(** The 64 SHA-256 round constants (the fractional parts of the cube roots
    of the first 64 primes), in round order. *)
Definition sha256_k : list Z :=
  [ 0x428a2f98; 0x71374491; 0xb5c0fbcf; 0xe9b5dba5;
    0x3956c25b; 0x59f111f1; 0x923f82a4; 0xab1c5ed5;
    0xd807aa98; 0x12835b01; 0x243185be; 0x550c7dc3;
    0x72be5d74; 0x80deb1fe; 0x9bdc06a7; 0xc19bf174;
    0xe49b69c1; 0xefbe4786; 0x0fc19dc6; 0x240ca1cc;
    0x2de92c6f; 0x4a7484aa; 0x5cb0a9dc; 0x76f988da;
    0x983e5152; 0xa831c66d; 0xb00327c8; 0xbf597fc7;
    0xc6e00bf3; 0xd5a79147; 0x06ca6351; 0x14292967;
    0x27b70a85; 0x2e1b2138; 0x4d2c6dfc; 0x53380d13;
    0x650a7354; 0x766a0abb; 0x81c2c92e; 0x92722c85;
    0xa2bfe8a1; 0xa81a664b; 0xc24b8b70; 0xc76c51a3;
    0xd192e819; 0xd6990624; 0xf40e3585; 0x106aa070;
    0x19a4c116; 0x1e376c08; 0x2748774c; 0x34b0bcb5;
    0x391c0cb3; 0x4ed8aa4a; 0x5b9cca4f; 0x682e6ff3;
    0x748f82ee; 0x78a5636f; 0x84c87814; 0x8cc70208;
    0x90befffa; 0xa4506ceb; 0xbef9a3f7; 0xc67178f2 ].

(* ================================================================= *)
(** ** Round-function words -- [sha256_ch] / [sha256_maj] / the Sigma family.
    Copied from the [Ch] / [Maj] / [Sigma0] / [Sigma1] / [sigma0] / [sigma1]
    macros of [src/hash_impl.h:16-21], each built on [theory.hash.sha256_bits].
    See https://wuille.net/posts/secp256k1-tutorial/#32-the-main-library-code-secp256k1c *)

(** The SHA-256 choice function: bit [i] of the result is bit [i] of [y] if
    bit [i] of [x] is set, else bit [i] of [z] ([Ch] in [hash_impl.h]). *)
Definition sha256_ch (x y z : Z) : Z := xor32 z (and32 x (xor32 y z)).

(** The SHA-256 majority function: bit [i] of the result is the majority
    vote of bit [i] of [x], [y], [z] ([Maj] in [hash_impl.h]). *)
Definition sha256_maj (x y z : Z) : Z := or32 (and32 x y) (and32 z (or32 x y)).

(** The compression round's "big" Sigma0 ([Sigma0] in [hash_impl.h]). *)
Definition sha256_bigsigma0 (x : Z) : Z :=
  xor32 (xor32 (rotr32 x 2) (rotr32 x 13)) (rotr32 x 22).

(** The compression round's "big" Sigma1 ([Sigma1] in [hash_impl.h]). *)
Definition sha256_bigsigma1 (x : Z) : Z :=
  xor32 (xor32 (rotr32 x 6) (rotr32 x 11)) (rotr32 x 25).

(** The message schedule's "little" sigma0 ([sigma0] in [hash_impl.h]). *)
Definition sha256_sigma0 (x : Z) : Z :=
  xor32 (xor32 (rotr32 x 7) (rotr32 x 18)) (shr32 x 3).

(** The message schedule's "little" sigma1 ([sigma1] in [hash_impl.h]). *)
Definition sha256_sigma1 (x : Z) : Z :=
  xor32 (xor32 (rotr32 x 17) (rotr32 x 19)) (shr32 x 10).

(* ================================================================= *)
(** ** Block words -- [sha256_words_of_block].
    The 16 big-endian 32-bit words [secp256k1_sha256_transform_impl] reads
    from a 64-byte block ([src/hash_impl.h:54-69]'s [secp256k1_read_be32]
    calls), via [theory.bytes.Z_of_be_bytes] on each 4-byte chunk.
    See https://wuille.net/posts/secp256k1-tutorial/#32-the-main-library-code-secp256k1c *)

(** Fuel-driven helper for [sha256_words_of_block]: decode [n] more 4-byte
    big-endian words from the front of [block]. *)
Fixpoint sha256_words_of_block_go (block : list Z) (n : nat) : list Z :=
  match n with
  | O => []
  | S n' => Z_of_be_bytes (firstn 4 block) :: sha256_words_of_block_go (skipn 4 block) n'
  end.

(** Split a 64-byte block into its 16 big-endian 32-bit words. *)
Definition sha256_words_of_block (block : list Z) : list Z :=
  sha256_words_of_block_go block 16.

(* ================================================================= *)
(** ** Message schedule -- [sha256_schedule].
    Extends the 16 block words to the full 64-word schedule
    [w0 += sigma1(w14) + w9 + sigma0(w1)] etc.
    ([src/hash_impl.h:71-120], folded back into the same 16 registers there;
    this model instead grows an explicit 64-long list, the same values in
    the same order).
    See https://wuille.net/posts/secp256k1-tutorial/#32-the-main-library-code-secp256k1c *)

(** Fuel-driven helper for [sha256_schedule]: extend [w] by [len] more
    schedule words, with [i] the index of the next word to produce. *)
Fixpoint sha256_schedule_go (w : list Z) (i len : nat) : list Z :=
  match len with
  | O => w
  | S l =>
    let wi16 := nth (Nat.sub i 16) w 0 in
    let wi15 := nth (Nat.sub i 15) w 0 in
    let wi7 := nth (Nat.sub i 7) w 0 in
    let wi2 := nth (Nat.sub i 2) w 0 in
    let wi := (wi16 + sha256_sigma0 wi15 + wi7 + sha256_sigma1 wi2) mod 2^32 in
    sha256_schedule_go (w ++ [wi]) (Nat.add i 1) l
  end.

(** The 64-word message schedule built from a block's 16 words. *)
Definition sha256_schedule (m : list Z) : list Z :=
  sha256_schedule_go m 16 48.

(* ================================================================= *)
(** ** One round / 64 rounds / state add -- [sha256_round] / [sha256_rounds] /
    [sha256_add_state].  The [Round] macro's [t1]/[t2] update and its
    register rotation ([src/hash_impl.h:23-28] and its 64 call sites).
    See https://wuille.net/posts/secp256k1-tutorial/#32-the-main-library-code-secp256k1c *)

(** One SHA-256 compression round: state [[a;b;c;d;e;f;g;h]] with round
    constant [k] and schedule word [w] steps to
    [[t1+t2; a; b; c; d+t1; e; f; g]] (mod [2^32]), matching the [Round]
    macro's [(d) += t1; (h) = t1 + t2] followed by the caller's argument
    rotation. *)
Definition sha256_round (st : list Z) (k w : Z) : list Z :=
  match st with
  | a :: b :: c :: d :: e :: f :: g :: h :: nil =>
    let t1 := (h + sha256_bigsigma1 e + sha256_ch e f g + k + w) mod 2^32 in
    let t2 := (sha256_bigsigma0 a + sha256_maj a b c) mod 2^32 in
    [ (t1 + t2) mod 2^32; a; b; c; (d + t1) mod 2^32; e; f; g ]
  | _ => st
  end.

(** All 64 rounds, pairing the schedule words with the round constants in
    order. *)
Fixpoint sha256_rounds (st ws ks : list Z) : list Z :=
  match ws, ks with
  | w :: ws', k :: ks' => sha256_rounds (sha256_round st k w) ws' ks'
  | _, _ => st
  end.

(** Elementwise mod-[2^32] add of two states, the compression's final
    [s[i] += <round result>[i]] step. *)
Definition sha256_add_state (s0 s1 : list Z) : list Z :=
  map (fun p => (fst p + snd p) mod 2^32) (combine s0 s1).

(* ================================================================= *)
(** ** One-block compression -- [sha256_compress].
    The 64-round compression core of a single 64-byte block: the model of
    [secp256k1_sha256_transform_impl] ([src/hash_impl.h:50-130]).
    See https://wuille.net/posts/secp256k1-tutorial/#32-the-main-library-code-secp256k1c *)

Definition sha256_compress (state block : list Z) : list Z :=
  let w := sha256_schedule (sha256_words_of_block block) in
  let final := sha256_rounds state w sha256_k in
  sha256_add_state state final.

(* ================================================================= *)
(** ** Multi-block transform -- [sha256_transform].
    [n_blocks] iterations of [sha256_compress] over consecutive 64-byte
    chunks of [blocks]: the model of [secp256k1_sha256_transform]
    ([src/hash_impl.h:132-137]), the one function the fork's
    [fn_sha256_compression] pointer is pinned to (see the file header).
    See https://wuille.net/posts/secp256k1-tutorial/#32-the-main-library-code-secp256k1c *)

Fixpoint sha256_transform (state blocks : list Z) (n_blocks : nat) : list Z :=
  match n_blocks with
  | O => state
  | S n =>
    let block := firstn 64 blocks in
    let rest := skipn 64 blocks in
    sha256_transform (sha256_compress state block) rest n
  end.

(* ================================================================= *)
(** ** Output bytes -- [sha256_bytes_of_state].
    Serializes the final 8-word state to 32 big-endian bytes: the model of
    [secp256k1_sha256_finalize]'s output loop ([src/hash_impl.h:187-190]).
    See https://wuille.net/posts/secp256k1-tutorial/#32-the-main-library-code-secp256k1c *)

Definition sha256_bytes_of_state (state : list Z) : list Z :=
  flat_map (fun w => be_bytes_of_Z w 4) state.

(* ================================================================= *)
(** ** Padding and the top-level digest -- [sha256_pad] / [sha256].
    The length-encoding padding and the one-shot digest: the model of
    [secp256k1_sha256_finalize]'s padding
    ([src/hash_impl.h:177-186]) composed with
    [secp256k1_sha256_initialize] + [secp256k1_sha256_write] +
    [secp256k1_sha256_finalize] end to end.
    See https://wuille.net/posts/secp256k1-tutorial/#32-the-main-library-code-secp256k1c *)

(** Append the SHA-256 padding: a [0x80] byte, enough zero bytes to reach 56
    (mod 64), then the 8-byte big-endian bit length -- the byte-string form
    of [hash_impl.h]'s [pad]/[sizedesc] write, computed directly from the
    message length rather than by tracking a byte counter. *)
Definition sha256_pad (msg : list Z) : list Z :=
  let nbytes := Z.of_nat (length msg) in
  let r := nbytes mod 64 in
  let padlen := if Z.leb r 55 then 56 - r else 120 - r in
  msg ++ (128 :: repeat 0 (Nat.sub (Z.to_nat padlen) 1)) ++ be_bytes_of_Z (nbytes * 8) 8.

(** The top-level SHA-256 digest of a byte list: pad, run the transform from
    the IV over every block, serialize the final state. *)
Definition sha256 (msg : list Z) : list Z :=
  let padded := sha256_pad msg in
  sha256_bytes_of_state (sha256_transform sha256_iv padded (Nat.div (length padded) 64)).

(* ================================================================= *)
(** ** Precomputed midstate -- [sha256_midstate].
    The state after a whole number of 64-byte blocks from the IV: the model
    of [secp256k1_sha256_initialize_midstate] ([src/hash_impl.h:42-47]),
    which loads a precomputed [(state, bytes)] pair rather than recomputing
    it.  Used to represent the three BIP-340 tag midstates
    ("BIP0340/challenge" / "BIP0340/aux" / "BIP0340/nonce"), each the state
    after hashing the one 64-byte block [sha256(tag) ++ sha256(tag)].
    See https://wuille.net/posts/secp256k1-tutorial/#32-the-main-library-code-secp256k1c *)

Definition sha256_midstate (prefix_blocks : list Z) (n_blocks : nat) : list Z :=
  sha256_transform sha256_iv prefix_blocks n_blocks.

(* ================================================================= *)
(** ** Tagged hash -- [tagged_hash].
    [sha256(sha256(tag) ++ sha256(tag) ++ msg)]: the model of
    [secp256k1_sha256_initialize_tagged] followed by writing [msg] and
    finalizing ([src/hash_impl.h:195-204]), the BIP-340 domain-separation
    trick every Schnorr hash (challenge / aux / nonce) uses.
    See https://wuille.net/posts/secp256k1-tutorial/#32-the-main-library-code-secp256k1c *)

Definition tagged_hash (tag msg : list Z) : list Z :=
  sha256 (sha256 tag ++ sha256 tag ++ msg).

(* ================================================================= *)
(** ** HMAC-SHA256 -- [hmac_key_block] / [hmac_sha256].
    The model of [secp256k1_hmac_sha256_initialize] /
    [_write] / [_finalize] end to end ([src/hash_impl.h:210-248]).
    See https://wuille.net/posts/secp256k1-tutorial/#32-the-main-library-code-secp256k1c *)

(** The 64-byte HMAC key block: the key itself, zero-padded, if it fits in
    64 bytes, else its SHA-256 digest zero-padded to 64
    ([secp256k1_hmac_sha256_initialize]'s [if (keylen <= sizeof(rkey))]). *)
Definition hmac_key_block (key : list Z) : list Z :=
  if Nat.leb (length key) 64
  then key ++ repeat 0 (Nat.sub 64 (length key))
  else sha256 key ++ repeat 0 32.

(** HMAC-SHA256: [sha256(opad_key ++ sha256(ipad_key ++ msg))], where
    [opad_key] / [ipad_key] are the key block XORed with [0x5c] / [0x36]
    (the two [rkey[n] ^=] loops chain to exactly this, see the comment at
    their call site). *)
Definition hmac_sha256 (key msg : list Z) : list Z :=
  let rkey := hmac_key_block key in
  let opad_key := map (fun b => Z.lxor b 92) rkey in
  let ipad_key := map (fun b => Z.lxor b 54) rkey in
  sha256 (opad_key ++ sha256 (ipad_key ++ msg)).

(* ================================================================= *)
(** ** RFC 6979 HMAC-DRBG -- [rfc6979_state] / [rfc6979_init] /
    [rfc6979_generate].  The model of
    [secp256k1_rfc6979_hmac_sha256_initialize] / [_generate]
    ([src/hash_impl.h:254-313]), including the [retry] flag that makes the
    second and later calls to [_generate] extend the chain rather than
    restart it.  ([_finalize] is the C no-op [(void) rng] and [_clear] is a
    memzero; neither has value-level content to model.)
    See https://wuille.net/posts/secp256k1-tutorial/#32-the-main-library-code-secp256k1c *)

(** The DRBG state: the 32-byte [V] and [K] registers plus the [retry] flag
    ([secp256k1_rfc6979_hmac_sha256]'s three fields). *)
Record rfc6979_state := mk_rfc6979_state {
  rfc6979_v : list Z;
  rfc6979_k : list Z;
  rfc6979_retry : bool
}.

(** Seed the DRBG from a key (RFC 6979 steps 3.2.b/c/d/f): [V] and [K] each
    start as 32 constant bytes, then two HMAC rounds mix in a [0]-tagged and
    a [1]-tagged pass over [V ++ key]. *)
Definition rfc6979_init (key : list Z) : rfc6979_state :=
  let v0 := repeat 1 32 in
  let k0 := repeat 0 32 in
  let k1 := hmac_sha256 k0 (v0 ++ [0] ++ key) in
  let v1 := hmac_sha256 k1 v0 in
  let k2 := hmac_sha256 k1 (v1 ++ [1] ++ key) in
  let v2 := hmac_sha256 k2 v1 in
  mk_rfc6979_state v2 k2 false.

(** Fuel-driven helper for [rfc6979_generate]'s output loop: re-key [v] and
    emit up to 32 bytes of it at a time until [outlen] bytes have been
    produced, returning the emitted bytes and the final [v].  [fuel] bounds
    the recursion; the caller always passes [outlen] itself, which suffices
    since each step emits at least one byte. *)
Fixpoint rfc6979_gen_loop (fuel : nat) (v k : list Z) (outlen : nat) : list Z * list Z :=
  match fuel with
  | O => ([], v)
  | S f =>
    match outlen with
    | O => ([], v)
    | _ =>
      let v' := hmac_sha256 k v in
      let now := Nat.min outlen 32 in
      let '(rest, vfinal) := rfc6979_gen_loop f v' k (Nat.sub outlen now) in
      (firstn now v' ++ rest, vfinal)
    end
  end.

(** Generate [outlen] bytes (RFC 6979 step 3.2.h): if this is a repeat call
    ([retry] set from a previous [rfc6979_generate]), extend the chain with
    an extra [0]-tagged HMAC round first; then repeatedly re-key [V] and
    emit up to 32 bytes of it until [outlen] bytes are produced.  [fuel] is
    [outlen] itself: each step emits at least one byte, so [outlen] steps
    always suffice.  Returns the generated bytes and the updated state
    (with [retry] now set, for a following call). *)
Definition rfc6979_generate (rng : rfc6979_state) (outlen : nat) : list Z * rfc6979_state :=
  let '(k1, v1) :=
    if rfc6979_retry rng
    then let k' := hmac_sha256 (rfc6979_k rng) (rfc6979_v rng ++ [0]) in
         (k', hmac_sha256 k' (rfc6979_v rng))
    else (rfc6979_k rng, rfc6979_v rng)
  in
  let '(bytes, vfinal) := rfc6979_gen_loop outlen v1 k1 outlen in
  (bytes, mk_rfc6979_state vfinal k1 true).
