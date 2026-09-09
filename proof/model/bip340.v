(** * model.bip340: pure functional model of BIP-340 Schnorr signatures. *)
(** Copyright (C) 2026 remix7531
    SPDX-License-Identifier: MIT *)

(** The trust boundary for the [schnorrsig] module: nonce derivation, the
    tagged challenge, signing and verification, all written on
    [model.group]'s [Point] / [smul] / [G] and [model.hash]'s [tagged_hash].
    Every quantity that is "a scalar mod n" here is a plain [Z], reduced by
    the definitions below rather than carried as a [model.scalar.Scalar] --
    exactly the convention [model.ecmult] / [model.ecmult_gen] already use
    for exponents, since a hash digest or an [option (list Z)] auxiliary
    input has no type-level in-range proof to build a [Scalar] from.

    OUT OF SCOPE: [secp256k1_schnorrsig_sign_custom] (an alternate
    nonce-function / auxiliary-data hook, locked out of this extraction --
    see [schnorr-manifest-excluded.tsv]).  [secp256k1_schnorrsig_sign32] and
    [secp256k1_schnorrsig_verify] are the two API roots this file specifies;
    [bip340_sign] models the [sign_internal] helper both that function and
    the deprecated [secp256k1_schnorrsig_sign] alias reduce to. *)

From Stdlib Require Import ZArith.
From Stdlib Require Import List.
Import ListNotations.

Require Import secp256k1.theory.bytes.
Require Import secp256k1.model.hash.
Require Import secp256k1.model.group.
Require Import secp256k1.model.ecmult.

Open Scope Z_scope.

(* ================================================================= *)
(** ** Domain tags -- [tag_bip340_aux] / [tag_bip340_challenge] / [tag_bip340_nonce].

    The three ASCII tag strings each [tagged_hash] call below hashes twice to
    seed its transcript.  [src/modules/schnorrsig/main_impl.h]'s three
    [midstate] constants are the precomputed result of exactly that, for the
    fixed-[algo] fast path -- [model.tests_hash]'s [chk_midstate_*] checks
    already cross-check those constants against these same byte lists.
    See https://wuille.net/posts/secp256k1-tutorial/#32-the-main-library-code-secp256k1c *)

(** ["BIP0340/aux"].
    See https://wuille.net/posts/secp256k1-tutorial/#32-the-main-library-code-secp256k1c *)
Definition tag_bip340_aux : list Z :=
  [66; 73; 80; 48; 51; 52; 48; 47; 97; 117; 120].

(** ["BIP0340/challenge"].
    See https://wuille.net/posts/secp256k1-tutorial/#32-the-main-library-code-secp256k1c *)
Definition tag_bip340_challenge : list Z :=
  [66; 73; 80; 48; 51; 52; 48; 47; 99; 104; 97; 108; 108; 101; 110; 103; 101].

(** ["BIP0340/nonce"].
    See https://wuille.net/posts/secp256k1-tutorial/#32-the-main-library-code-secp256k1c *)
Definition tag_bip340_nonce : list Z :=
  [66; 73; 80; 48; 51; 52; 48; 47; 110; 111; 110; 99; 101].

(* ================================================================= *)
(** ** Byte XOR -- [xor_bytes].

    Elementwise [Z.lxor] of two equal-length byte lists: the model of the
    "mask the key" loops [nonce_function_bip340_impl] runs over its 32-byte
    buffers ([src/modules/schnorrsig/main_impl.h:49-51] and [:59-61]).
    See https://wuille.net/posts/secp256k1-tutorial/#32-the-main-library-code-secp256k1c *)

Fixpoint xor_bytes (xs ys : list Z) : list Z :=
  match xs, ys with
  | x :: xs', y :: ys' => Z.lxor x y :: xor_bytes xs' ys'
  | _, _ => []
  end.

(* ================================================================= *)
(** ** Nonce derivation -- [zero_mask32] / [bip340_nonce].

    The [aux_rand32 == NULL] branch is IN SCOPE, which is why [bip340_nonce]
    takes an [option (list Z)] rather than a bare byte list (see the module
    notes).
    See https://wuille.net/posts/secp256k1-tutorial/#32-the-main-library-code-secp256k1c *)

(** The precomputed mask [nonce_function_bip340_impl] XORs into [key32] when
    no auxiliary randomness is supplied
    ([src/modules/schnorrsig/main_impl.h:57-65]), transcribed literally from
    its [ZERO_MASK] constant -- itself, per the C's own comment,
    [TaggedHash("BIP0340/aux", 0x00...00)].
    See https://wuille.net/posts/secp256k1-tutorial/#32-the-main-library-code-secp256k1c *)
Definition zero_mask32 : list Z :=
  [ 84; 241; 105; 207; 201; 226; 229; 114;
    116; 128; 68; 31; 144; 186; 37; 196;
    136; 244; 97; 199; 11; 94; 165; 220;
    170; 247; 175; 105; 39; 10; 165; 20 ].

(** BIP-340 nonce derivation: mask [key32] with [TaggedHash("BIP0340/aux",
    aux)] when auxiliary randomness [aux] is supplied, or with [zero_mask32]
    when it is [None], then tag-hash [masked_key ++ pk32 ++ msg] with
    ["BIP0340/nonce"].  Specifies [nonce_function_bip340_impl]
    ([src/modules/schnorrsig/main_impl.h:40-88]) at its one reachable [algo]
    (the [bip340_algo] fast path every caller in this extraction uses -- see
    the module notes), so this model carries no separate [algo] parameter.
    See https://wuille.net/posts/secp256k1-tutorial/#32-the-main-library-code-secp256k1c *)
Definition bip340_nonce (aux : option (list Z)) (key32 pk32 msg : list Z) : list Z :=
  let masked_key :=
    match aux with
    | Some a => xor_bytes (tagged_hash tag_bip340_aux a) key32
    | None => xor_bytes zero_mask32 key32
    end
  in
  tagged_hash tag_bip340_nonce (masked_key ++ pk32 ++ msg).

(* ================================================================= *)
(** ** The challenge -- [bip340_challenge].

    Specifies [secp256k1_schnorrsig_challenge]
    ([src/modules/schnorrsig/main_impl.h:106-120]): tag-hash [r32 ++ pk32 ++
    msg] and reduce the digest modulo the group order, exactly
    [secp256k1_scalar_set_b32]'s wrapping (non-overflow-checked) reduction.
    See https://wuille.net/posts/secp256k1-tutorial/#32-the-main-library-code-secp256k1c *)
Definition bip340_challenge (r32 pk32 msg : list Z) : Z :=
  Z_of_be_bytes (tagged_hash tag_bip340_challenge (r32 ++ pk32 ++ msg)) mod secp256k1_N.

(* ================================================================= *)
(** ** Signing-key normalisation -- [bip340_keygen].

    Specifies the key-adjustment half of [secp256k1_schnorrsig_sign_internal]
    ([src/modules/schnorrsig/main_impl.h:134-140]): from a raw secret scalar
    [sk] (already reduced mod [n], as the C's [Scalar] always is), compute
    [P = sk*G] and negate [sk] mod [n] exactly when [P] does not have an even
    y, since BIP-340 always signs for the x-only key [bytes_x(P)].  [P]'s x
    coordinate is unaffected by the negation (only its y flips), so it is
    returned unchanged alongside the (possibly negated) scalar.
    See https://wuille.net/posts/secp256k1-tutorial/#222-scalar-multiplication *)
Definition bip340_keygen (sk : Z) : Z * Fe :=
  match smul sk G with
  | PInf => (sk, fe_zero)
  | PAff x y => ((if fe_is_odd y then (secp256k1_N - sk) mod secp256k1_N else sk), x)
  end.

(* ================================================================= *)
(** ** Signing -- [bip340_sign].

    Specifies [secp256k1_schnorrsig_sign_internal]
    ([src/modules/schnorrsig/main_impl.h:122-186]) and, through it,
    [secp256k1_schnorrsig_sign32] ([:188-191]).  Fails ([None]) exactly when
    the derived nonce reduces to [0] mod [n] -- the one data-dependent branch
    the C guards against with its constant-time [cmov]/[memczero] dance;
    since [G] has prime order [n], [0 < k < n] also rules out [smul k G =
    PInf], so no second infinity check is needed.
    See https://wuille.net/posts/secp256k1-tutorial/#31-the-public-api *)
Definition bip340_sign (sk : Z) (msg : list Z) (aux : option (list Z)) : option (list Z) :=
  let '(d, px) := bip340_keygen sk in
  let px_bytes := fe_to_bytes px in
  let nonce32 := bip340_nonce aux (be_bytes_of_Z d 32) px_bytes msg in
  let k0 := Z_of_be_bytes nonce32 mod secp256k1_N in
  if Z.eqb k0 0 then None
  else
    match smul k0 G with
    | PInf => None
    | PAff rx ry =>
      let k := if fe_is_odd ry then (secp256k1_N - k0) mod secp256k1_N else k0 in
      let r_bytes := fe_to_bytes rx in
      let e := bip340_challenge r_bytes px_bytes msg in
      let s := (e * d + k) mod secp256k1_N in
      Some (r_bytes ++ be_bytes_of_Z s 32)
    end.

(* ================================================================= *)
(** ** Verification -- [bip340_verify].

    Specifies [secp256k1_schnorrsig_verify]
    ([src/modules/schnorrsig/main_impl.h:212-232]).  [ecmult_model]
    ([model.ecmult]) is [secp256k1_ecmult]'s own meaning ([na*a + ng*G]),
    matching the module note that verification goes through the
    single-point [secp256k1_ecmult], not [ecmult_multi].  [r32]/[s32] are
    rejected out of range exactly as [secp256k1_fe_set_b32_limit] (no wrap,
    unlike [fe_of_bytes]) and [secp256k1_scalar_set_b32]'s overflow flag do;
    the final [has_even_y] check is BIP-340's own "fail if not
    has_even_y(R)".
    See https://wuille.net/posts/secp256k1-tutorial/#31-the-public-api *)
Definition bip340_verify (sig64 msg : list Z) (pk32 : Fe) : bool :=
  let r32 := firstn 32 sig64 in
  let s32 := skipn 32 sig64 in
  let rval := Z_of_be_bytes r32 in
  let sval := Z_of_be_bytes s32 in
  if negb (Z.ltb rval secp256k1_P) then false
  else if negb (Z.ltb sval secp256k1_N) then false
  else
    match lift_x_even pk32 with
    | None => false
    | Some pk =>
      let e := bip340_challenge r32 (fe_to_bytes pk32) msg in
      match ecmult_model pk ((secp256k1_N - e) mod secp256k1_N) sval with
      | PInf => false
      | PAff rx _ as r => andb (has_even_y r) (Z.eqb (fe_val rx) rval)
      end
    end.

(* ================================================================= *)
(** ** X-only public keys -- [xonly_parse] / [xonly_serialize].

    Built on [model.group]'s [lift_x_even] (and, for verification's own
    "even y" test above, [has_even_y]).  Specifies
    [secp256k1_xonly_pubkey_parse] / [_serialize]
    ([src/modules/extrakeys/main_impl.h:22-57]).
    See https://wuille.net/posts/secp256k1-tutorial/#326-group-group-operations-on-the-secp256k1-curve-group *)

(** Parse a 32-byte x-only encoding: fail if the bytes are [>= p] (the C's
    [secp256k1_fe_set_b32_limit], which does not wrap the way [fe_of_bytes]
    does), else lift to the even-y point.  The C's further
    [secp256k1_ge_is_in_correct_subgroup] check is unconditionally true on
    secp256k1 (cofactor 1), so it adds no failure mode here.
    See https://wuille.net/posts/secp256k1-tutorial/#326-group-group-operations-on-the-secp256k1-curve-group *)
Definition xonly_parse (input32 : list Z) : option Point :=
  if Z.leb secp256k1_P (Z_of_be_bytes input32) then None
  else lift_x_even (fe_of_bytes input32).

(** Serialize a point's x coordinate, or [None] at infinity -- a state no
    valid x-only public key can actually be in, since every constructor of
    one goes through [secp256k1_ge_set_xo_var] or an equivalent lift; kept
    [option] so the model stays total on all of [Point].
    See https://wuille.net/posts/secp256k1-tutorial/#326-group-group-operations-on-the-secp256k1-curve-group *)
Definition xonly_serialize (a : Point) : option (list Z) :=
  match a with
  | PInf => None
  | PAff x _ => Some (fe_to_bytes x)
  end.
