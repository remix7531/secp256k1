(** * theory.primality.p: a Pocklington certificate for the secp256k1 field prime. *)
(** Copyright (C) 2026 remix7531
    SPDX-License-Identifier: MIT *)

(** Proves [prime P] for the literal field modulus

      P = 2^256 - 2^32 - 977
        = 115792089237316195423570985008687907853269984665640564039457584007908834671663

    the same digits as [model.constants.secp256k1_P] -- via a coqprime
    Pocklington certificate, exactly the route [theory.primality.n] takes for
    the group order [N].  [Pocklington_refl] reduces primality of a number
    [p] to a boolean check once [p - 1] is fully factored and each distinct
    prime factor is itself already proved prime, so the proof is a chain of
    leaf [Lemma prime_<q> : prime q] built bottom-up, each closed by

      apply (Pocklington_refl (Pock_certif q a [(q1,e1);...] 1)
              ((Proof_certif q1 primeq1) :: ... :: nil)).
      vm_cast_no_check (refl_equal true).

    down to the primes small enough for coqprime's own base certificates
    ([prime2] / [prime3], re-exported by [PocklingtonRefl]).

    The factorisation chain for [P] itself:

      P - 1 = 2 * 3 * 7 * 13441 * Q

      Q = 205115282021455665897114700593932402728804164701536103180137503955397371
        (237 bits)
        = 2 * 3 * 5 * 29^2 * 31 * 7723 * q1 * q2

      q1 = 132896956044521568488119                            (77 bits)
      q2 = 255515944373312847190720520512484175977             (128 bits)

    and recursively for every composite [q - 1] above, bottoming out at
    coqprime's base primes.  The witness for [P] is [3]; every intermediate
    [prime_<q>] lemma carries its own witness, found by brute-force search
    over small bases (the same [find_witness] routine [gencert.py] uses).

    UNLIKE [N]'s chain, [P - 1]'s two hardest cofactors ([q1] and, deeper,
    the two ~90-bit cofactors [q1 - 1] and [q2 - 1] bottom out on) are past
    what this machine's Pollard's rho (`gencert.py factor`, ~2-4 minutes of
    parallel search) could crack in the time available: [q1] and [q2] were
    instead looked up on <https://factordb.com> (a public factorization
    database) by the exact residual value, giving [(132896956044521568488119,
    1)] and a 10-way splitting of [q2 - 1] respectively.  Every value
    factordb returned was checked locally before use -- that it multiplies
    back to the exact target, and that each claimed prime factor passes the
    same Miller-Rabin test [gencert.py] uses -- but the *proof* does not rest
    on that check or on factordb's say-so: an incorrect factor or a
    misclassified composite would make the corresponding [Pock_certif]'s
    [vm_compute] check reduce to [false], and the closing
    [vm_cast_no_check (refl_equal true)] would fail to typecheck.  factordb
    is a finding aid, exactly like [gencert.py]'s own [pollard_rho_parallel]
    -- only the search method differs; regenerating this file (see below)
    means re-deriving the same kind of split for whichever cofactor is hard,
    by either tool.

    HOW TO REGENERATE: this file has no fully-scripted one-shot generator
    checked into the tree (unlike [n.v]'s [gencert.py], whose hard splits
    all fell to local Pollard's rho).  Reproduce it by extending
    [gencert.py]'s [emit_chain] / [factor_counts] / [find_witness] helpers
    with a factordb.com lookup for any residual cofactor that resists both
    trial division and a Pollard's-rho budget of a few minutes -- exactly
    the fallback [gencert.py]'s own [EXTRA] dict documents, sourced from a
    database instead of a fresh local search -- then emit the same
    leaves-first chain [gencert.py]'s [emit_chain] does.  This only needs
    re-running if the literal [P] ever changes (it will not: [P] is fixed by
    the secp256k1 standard).

    TRUST NOTE: [Print Assumptions secp256k1_P_prime_cert] lists Rocq's
    primitive 63-bit integer axioms ([Uint63Axioms.*] / [PrimInt63.*]),
    pulled in by coqprime's [BigN]-based certificate checker -- the same
    trust surface any coqprime user accepts, and the same one
    [theory.primality.n] already carries.  No [Admitted], no project [Axiom]
    here: [model.field.secp256k1_P_prime] is a [Qed] lemma ([exact
    secp256k1_P_prime_cert.]) over this certificate, so [Print Assumptions]
    on the headline closes over this file's [Uint63Axioms.*] /
    [PrimInt63.*] cone (whitelisted as foundational trust in
    [audit/AXIOM_WHITELIST]) instead of a project axiom. *)

From Coqprime Require Import PocklingtonRefl.
Local Open Scope positive_scope.

Lemma prime_7 : prime 7.
Proof.
 apply (Pocklington_refl (Pock_certif 7 3 ((2,1)::(3,1)::nil) 1)
        ((Proof_certif 2 prime2)::(Proof_certif 3 prime3)::nil)).
 vm_cast_no_check (refl_equal true).
Qed.

Lemma prime_5 : prime 5.
Proof.
 apply (Pocklington_refl (Pock_certif 5 2 ((2,2)::nil) 1)
        ((Proof_certif 2 prime2)::nil)).
 vm_cast_no_check (refl_equal true).
Qed.

Lemma prime_13441 : prime 13441.
Proof.
 apply (Pocklington_refl (Pock_certif 13441 11 ((2,7)::(3,1)::(5,1)::(7,1)::nil) 1)
        ((Proof_certif 2 prime2)::(Proof_certif 3 prime3)::(Proof_certif 5 prime_5)::(Proof_certif 7 prime_7)::nil)).
 vm_cast_no_check (refl_equal true).
Qed.

Lemma prime_29 : prime 29.
Proof.
 apply (Pocklington_refl (Pock_certif 29 2 ((2,2)::(7,1)::nil) 1)
        ((Proof_certif 2 prime2)::(Proof_certif 7 prime_7)::nil)).
 vm_cast_no_check (refl_equal true).
Qed.

Lemma prime_31 : prime 31.
Proof.
 apply (Pocklington_refl (Pock_certif 31 3 ((2,1)::(3,1)::(5,1)::nil) 1)
        ((Proof_certif 2 prime2)::(Proof_certif 3 prime3)::(Proof_certif 5 prime_5)::nil)).
 vm_cast_no_check (refl_equal true).
Qed.

Lemma prime_11 : prime 11.
Proof.
 apply (Pocklington_refl (Pock_certif 11 2 ((2,1)::(5,1)::nil) 1)
        ((Proof_certif 2 prime2)::(Proof_certif 5 prime_5)::nil)).
 vm_cast_no_check (refl_equal true).
Qed.

Lemma prime_13 : prime 13.
Proof.
 apply (Pocklington_refl (Pock_certif 13 2 ((2,2)::(3,1)::nil) 1)
        ((Proof_certif 2 prime2)::(Proof_certif 3 prime3)::nil)).
 vm_cast_no_check (refl_equal true).
Qed.

Lemma prime_7723 : prime 7723.
Proof.
 apply (Pocklington_refl (Pock_certif 7723 3 ((2,1)::(3,3)::(11,1)::(13,1)::nil) 1)
        ((Proof_certif 2 prime2)::(Proof_certif 3 prime3)::(Proof_certif 11 prime_11)::(Proof_certif 13 prime_13)::nil)).
 vm_cast_no_check (refl_equal true).
Qed.

Lemma prime_17 : prime 17.
Proof.
 apply (Pocklington_refl (Pock_certif 17 3 ((2,4)::nil) 1)
        ((Proof_certif 2 prime2)::nil)).
 vm_cast_no_check (refl_equal true).
Qed.

Lemma prime_443 : prime 443.
Proof.
 apply (Pocklington_refl (Pock_certif 443 2 ((2,1)::(13,1)::(17,1)::nil) 1)
        ((Proof_certif 2 prime2)::(Proof_certif 13 prime_13)::(Proof_certif 17 prime_17)::nil)).
 vm_cast_no_check (refl_equal true).
Qed.

Lemma prime_887 : prime 887.
Proof.
 apply (Pocklington_refl (Pock_certif 887 5 ((2,1)::(443,1)::nil) 1)
        ((Proof_certif 2 prime2)::(Proof_certif 443 prime_443)::nil)).
 vm_cast_no_check (refl_equal true).
Qed.

Lemma prime_5323 : prime 5323.
Proof.
 apply (Pocklington_refl (Pock_certif 5323 5 ((2,1)::(3,1)::(887,1)::nil) 1)
        ((Proof_certif 2 prime2)::(Proof_certif 3 prime3)::(Proof_certif 887 prime_887)::nil)).
 vm_cast_no_check (refl_equal true).
Qed.

Lemma prime_131 : prime 131.
Proof.
 apply (Pocklington_refl (Pock_certif 131 2 ((2,1)::(5,1)::(13,1)::nil) 1)
        ((Proof_certif 2 prime2)::(Proof_certif 5 prime_5)::(Proof_certif 13 prime_13)::nil)).
 vm_cast_no_check (refl_equal true).
Qed.

Lemma prime_2621 : prime 2621.
Proof.
 apply (Pocklington_refl (Pock_certif 2621 2 ((2,2)::(5,1)::(131,1)::nil) 1)
        ((Proof_certif 2 prime2)::(Proof_certif 5 prime_5)::(Proof_certif 131 prime_131)::nil)).
 vm_cast_no_check (refl_equal true).
Qed.

Lemma prime_24809 : prime 24809.
Proof.
 apply (Pocklington_refl (Pock_certif 24809 6 ((2,3)::(7,1)::(443,1)::nil) 1)
        ((Proof_certif 2 prime2)::(Proof_certif 7 prime_7)::(Proof_certif 443 prime_443)::nil)).
 vm_cast_no_check (refl_equal true).
Qed.

Lemma prime_97 : prime 97.
Proof.
 apply (Pocklington_refl (Pock_certif 97 5 ((2,5)::(3,1)::nil) 1)
        ((Proof_certif 2 prime2)::(Proof_certif 3 prime3)::nil)).
 vm_cast_no_check (refl_equal true).
Qed.

Lemma prime_971 : prime 971.
Proof.
 apply (Pocklington_refl (Pock_certif 971 6 ((2,1)::(5,1)::(97,1)::nil) 1)
        ((Proof_certif 2 prime2)::(Proof_certif 5 prime_5)::(Proof_certif 97 prime_97)::nil)).
 vm_cast_no_check (refl_equal true).
Qed.

Lemma prime_1373 : prime 1373.
Proof.
 apply (Pocklington_refl (Pock_certif 1373 2 ((2,2)::(7,3)::nil) 1)
        ((Proof_certif 2 prime2)::(Proof_certif 7 prime_7)::nil)).
 vm_cast_no_check (refl_equal true).
Qed.

Lemma prime_13331831 : prime 13331831.
Proof.
 apply (Pocklington_refl (Pock_certif 13331831 13 ((2,1)::(5,1)::(971,1)::(1373,1)::nil) 1)
        ((Proof_certif 2 prime2)::(Proof_certif 5 prime_5)::(Proof_certif 971 prime_971)::(Proof_certif 1373 prime_1373)::nil)).
 vm_cast_no_check (refl_equal true).
Qed.

Lemma prime_173378833005251801 : prime 173378833005251801.
Proof.
 apply (Pocklington_refl (Pock_certif 173378833005251801 6 ((2,3)::(5,2)::(2621,1)::(24809,1)::(13331831,1)::nil) 1)
        ((Proof_certif 2 prime2)::(Proof_certif 5 prime_5)::(Proof_certif 2621 prime_2621)::(Proof_certif 24809 prime_24809)::(Proof_certif 13331831 prime_13331831)::nil)).
 vm_cast_no_check (refl_equal true).
Qed.

Lemma prime_22149492674086928081353 : prime 22149492674086928081353.
Proof.
 apply (Pocklington_refl (Pock_certif 22149492674086928081353 5 ((2,3)::(3,1)::(5323,1)::(173378833005251801,1)::nil) 1)
        ((Proof_certif 2 prime2)::(Proof_certif 3 prime3)::(Proof_certif 5323 prime_5323)::(Proof_certif 173378833005251801 prime_173378833005251801)::nil)).
 vm_cast_no_check (refl_equal true).
Qed.

Lemma prime_132896956044521568488119 : prime 132896956044521568488119.
Proof.
 apply (Pocklington_refl (Pock_certif 132896956044521568488119 6 ((2,1)::(3,1)::(22149492674086928081353,1)::nil) 1)
        ((Proof_certif 2 prime2)::(Proof_certif 3 prime3)::(Proof_certif 22149492674086928081353 prime_22149492674086928081353)::nil)).
 vm_cast_no_check (refl_equal true).
Qed.

Lemma prime_271 : prime 271.
Proof.
 apply (Pocklington_refl (Pock_certif 271 6 ((2,1)::(3,3)::(5,1)::nil) 1)
        ((Proof_certif 2 prime2)::(Proof_certif 3 prime3)::(Proof_certif 5 prime_5)::nil)).
 vm_cast_no_check (refl_equal true).
Qed.

Lemma prime_1627 : prime 1627.
Proof.
 apply (Pocklington_refl (Pock_certif 1627 3 ((2,1)::(3,1)::(271,1)::nil) 1)
        ((Proof_certif 2 prime2)::(Proof_certif 3 prime3)::(Proof_certif 271 prime_271)::nil)).
 vm_cast_no_check (refl_equal true).
Qed.

Lemma prime_41 : prime 41.
Proof.
 apply (Pocklington_refl (Pock_certif 41 6 ((2,3)::(5,1)::nil) 1)
        ((Proof_certif 2 prime2)::(Proof_certif 5 prime_5)::nil)).
 vm_cast_no_check (refl_equal true).
Qed.

Lemma prime_83 : prime 83.
Proof.
 apply (Pocklington_refl (Pock_certif 83 2 ((2,1)::(41,1)::nil) 1)
        ((Proof_certif 2 prime2)::(Proof_certif 41 prime_41)::nil)).
 vm_cast_no_check (refl_equal true).
Qed.

Lemma prime_2657 : prime 2657.
Proof.
 apply (Pocklington_refl (Pock_certif 2657 3 ((2,5)::(83,1)::nil) 1)
        ((Proof_certif 2 prime2)::(Proof_certif 83 prime_83)::nil)).
 vm_cast_no_check (refl_equal true).
Qed.

Lemma prime_67 : prime 67.
Proof.
 apply (Pocklington_refl (Pock_certif 67 2 ((2,1)::(3,1)::(11,1)::nil) 1)
        ((Proof_certif 2 prime2)::(Proof_certif 3 prime3)::(Proof_certif 11 prime_11)::nil)).
 vm_cast_no_check (refl_equal true).
Qed.

Lemma prime_4423 : prime 4423.
Proof.
 apply (Pocklington_refl (Pock_certif 4423 3 ((2,1)::(3,1)::(11,1)::(67,1)::nil) 1)
        ((Proof_certif 2 prime2)::(Proof_certif 3 prime3)::(Proof_certif 11 prime_11)::(Proof_certif 67 prime_67)::nil)).
 vm_cast_no_check (refl_equal true).
Qed.

Lemma prime_103 : prime 103.
Proof.
 apply (Pocklington_refl (Pock_certif 103 5 ((2,1)::(3,1)::(17,1)::nil) 1)
        ((Proof_certif 2 prime2)::(Proof_certif 3 prime3)::(Proof_certif 17 prime_17)::nil)).
 vm_cast_no_check (refl_equal true).
Qed.

Lemma prime_41201 : prime 41201.
Proof.
 apply (Pocklington_refl (Pock_certif 41201 3 ((2,4)::(5,2)::(103,1)::nil) 1)
        ((Proof_certif 2 prime2)::(Proof_certif 5 prime_5)::(Proof_certif 103 prime_103)::nil)).
 vm_cast_no_check (refl_equal true).
Qed.

Lemma prime_101 : prime 101.
Proof.
 apply (Pocklington_refl (Pock_certif 101 2 ((2,2)::(5,2)::nil) 1)
        ((Proof_certif 2 prime2)::(Proof_certif 5 prime_5)::nil)).
 vm_cast_no_check (refl_equal true).
Qed.

Lemma prime_239 : prime 239.
Proof.
 apply (Pocklington_refl (Pock_certif 239 7 ((2,1)::(7,1)::(17,1)::nil) 1)
        ((Proof_certif 2 prime2)::(Proof_certif 7 prime_7)::(Proof_certif 17 prime_17)::nil)).
 vm_cast_no_check (refl_equal true).
Qed.

Lemma prime_96557 : prime 96557.
Proof.
 apply (Pocklington_refl (Pock_certif 96557 2 ((2,2)::(101,1)::(239,1)::nil) 1)
        ((Proof_certif 2 prime2)::(Proof_certif 101 prime_101)::(Proof_certif 239 prime_239)::nil)).
 vm_cast_no_check (refl_equal true).
Qed.

Lemma prime_19 : prime 19.
Proof.
 apply (Pocklington_refl (Pock_certif 19 2 ((2,1)::(3,2)::nil) 1)
        ((Proof_certif 2 prime2)::(Proof_certif 3 prime3)::nil)).
 vm_cast_no_check (refl_equal true).
Qed.

Lemma prime_419 : prime 419.
Proof.
 apply (Pocklington_refl (Pock_certif 419 2 ((2,1)::(11,1)::(19,1)::nil) 1)
        ((Proof_certif 2 prime2)::(Proof_certif 11 prime_11)::(Proof_certif 19 prime_19)::nil)).
 vm_cast_no_check (refl_equal true).
Qed.

Lemma prime_20113 : prime 20113.
Proof.
 apply (Pocklington_refl (Pock_certif 20113 10 ((2,4)::(3,1)::(419,1)::nil) 1)
        ((Proof_certif 2 prime2)::(Proof_certif 3 prime3)::(Proof_certif 419 prime_419)::nil)).
 vm_cast_no_check (refl_equal true).
Qed.

Lemma prime_1206781 : prime 1206781.
Proof.
 apply (Pocklington_refl (Pock_certif 1206781 10 ((2,2)::(3,1)::(5,1)::(20113,1)::nil) 1)
        ((Proof_certif 2 prime2)::(Proof_certif 3 prime3)::(Proof_certif 5 prime_5)::(Proof_certif 20113 prime_20113)::nil)).
 vm_cast_no_check (refl_equal true).
Qed.

Lemma prime_7240687 : prime 7240687.
Proof.
 apply (Pocklington_refl (Pock_certif 7240687 3 ((2,1)::(3,1)::(1206781,1)::nil) 1)
        ((Proof_certif 2 prime2)::(Proof_certif 3 prime3)::(Proof_certif 1206781 prime_1206781)::nil)).
 vm_cast_no_check (refl_equal true).
Qed.

Lemma prime_53 : prime 53.
Proof.
 apply (Pocklington_refl (Pock_certif 53 2 ((2,2)::(13,1)::nil) 1)
        ((Proof_certif 2 prime2)::(Proof_certif 13 prime_13)::nil)).
 vm_cast_no_check (refl_equal true).
Qed.

Lemma prime_107590001 : prime 107590001.
Proof.
 apply (Pocklington_refl (Pock_certif 107590001 3 ((2,4)::(5,4)::(7,1)::(29,1)::(53,1)::nil) 1)
        ((Proof_certif 2 prime2)::(Proof_certif 5 prime_5)::(Proof_certif 7 prime_7)::(Proof_certif 29 prime_29)::(Proof_certif 53 prime_53)::nil)).
 vm_cast_no_check (refl_equal true).
Qed.

Lemma prime_255515944373312847190720520512484175977 : prime 255515944373312847190720520512484175977.
Proof.
 apply (Pocklington_refl (Pock_certif 255515944373312847190720520512484175977 3 ((2,3)::(7,2)::(11,1)::(1627,1)::(2657,1)::(4423,1)::(41201,1)::(96557,1)::(7240687,1)::(107590001,1)::nil) 1)
        ((Proof_certif 2 prime2)::(Proof_certif 7 prime_7)::(Proof_certif 11 prime_11)::(Proof_certif 1627 prime_1627)::(Proof_certif 2657 prime_2657)::(Proof_certif 4423 prime_4423)::(Proof_certif 41201 prime_41201)::(Proof_certif 96557 prime_96557)::(Proof_certif 7240687 prime_7240687)::(Proof_certif 107590001 prime_107590001)::nil)).
 vm_cast_no_check (refl_equal true).
Qed.

Lemma prime_205115282021455665897114700593932402728804164701536103180137503955397371 : prime 205115282021455665897114700593932402728804164701536103180137503955397371.
Proof.
 apply (Pocklington_refl (Pock_certif 205115282021455665897114700593932402728804164701536103180137503955397371 10 ((2,1)::(3,1)::(5,1)::(29,2)::(31,1)::(7723,1)::(132896956044521568488119,1)::(255515944373312847190720520512484175977,1)::nil) 1)
        ((Proof_certif 2 prime2)::(Proof_certif 3 prime3)::(Proof_certif 5 prime_5)::(Proof_certif 29 prime_29)::(Proof_certif 31 prime_31)::(Proof_certif 7723 prime_7723)::(Proof_certif 132896956044521568488119 prime_132896956044521568488119)::(Proof_certif 255515944373312847190720520512484175977 prime_255515944373312847190720520512484175977)::nil)).
 vm_cast_no_check (refl_equal true).
Qed.

Lemma secp256k1_P_prime_cert : prime 115792089237316195423570985008687907853269984665640564039457584007908834671663.
Proof.
 apply (Pocklington_refl (Pock_certif 115792089237316195423570985008687907853269984665640564039457584007908834671663 3 ((2,1)::(3,1)::(7,1)::(13441,1)::(205115282021455665897114700593932402728804164701536103180137503955397371,1)::nil) 1)
        ((Proof_certif 2 prime2)::(Proof_certif 3 prime3)::(Proof_certif 7 prime_7)::(Proof_certif 13441 prime_13441)::(Proof_certif 205115282021455665897114700593932402728804164701536103180137503955397371 prime_205115282021455665897114700593932402728804164701536103180137503955397371)::nil)).
 vm_cast_no_check (refl_equal true).
Qed.

