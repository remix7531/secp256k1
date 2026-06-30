#!/usr/bin/env python3
"""theory/primality/gencert.py -- regenerate the Pocklington certificate body
of theory/primality/n.v (the proof that the secp256k1 group order N is
prime), using only the Python 3 standard library.

WHAT THIS PRODUCES
-------------------
A chain of Rocq `Lemma prime_<p> : prime p.` declarations, each closed by
coqprime's `Pocklington_refl` (from `PocklingtonRefl`), in dependency order
(leaves first), ending in the top-level `secp256k1_N_prime_cert` lemma for
N itself. `Pocklington_refl` reduces `prime p` to a `vm_compute`-checked
boolean once `p - 1` is fully factored and every distinct prime factor of
`p - 1` is itself already proved prime -- so the whole certificate is one
recursive factor-then-prove chain, bottoming out at coqprime's own base
certificates (`prime2` / `prime3` / `prime149` / `prime631`).

HOW TO REGENERATE
-----------------
    python3 theory/primality/gencert.py > /tmp/n_body.v

then copy the output below the doc comment in `theory/primality/n.v`
(replacing everything from the `From Coqprime Require Import ...` line
onward), and recompile:

    cd proof && rocq compile -Q . secp256k1 theory/primality/n.v

This only needs re-running if the literal N changes. `build_certificate()`
below hard-codes the three "hard" cofactors of `N - 1` (`p1`, `p2`, `p3`)
and the one residual (`EXTRA`) that plain trial division cannot crack --
found once, offline, via `pollard_rho_parallel` below (the `factor2.py`
Pollard's-rho driver this script also carries). If N ever changes, redo the
factorization by hand: trial-divide `N - 1` (see `factor_counts`), and for
any residual cofactor trial division cannot crack, either it is itself
prime (`is_probable_prime`) or find a nontrivial factor with

    python3 theory/primality/gencert.py factor <cofactor> [budget_s] [nproc]

then add the split to `EXTRA` (or `factor_counts`'s search bound) and
re-run `build_certificate`.

This is exactly the merge of three exploratory scripts from the feasibility
study (`factor.py`'s Miller-Rabin test, `factor2.py`'s parallel Pollard's
rho, and the original `gencert.py`'s Pocklington-chain emitter plus
`build_full.py`'s N-specific driver) into one self-contained file, with one
bug fixed on the merge: the emitted body now includes the
`Local Open Scope positive_scope.` line the certificate actually needs to
compile (the original `build_full.py` omitted it; it was patched in by
hand when `n_prime.v` was first assembled).
"""

import random
import sys
import time
from math import gcd

# ===================================================================
# The pinned target: the secp256k1 group order N, and the three "hard"
# cofactors of N - 1 that trial division alone cannot factor (found once,
# offline, by Pollard's rho below).
# ===================================================================

N = 115792089237316195423570985008687907852837564279074904382605163141518161494337

P1 = 107361793816595537
P2 = 174723607534414371449
P3 = 341948486974166000522343609283189

# Residual cofactor inside P3 - 1's chain that trial division (to the
# default 10**6 bound) cannot crack; its split was found by
# `pollard_rho_parallel(162058447585428954701)`.
EXTRA = {
    162058447585428954701: [545358713, 297159362677],
}

# Primes coqprime already provides base certificates for
# (`prime2` / `prime3` / `prime149` / `prime631`, re-exported by
# `PocklingtonRefl`) -- these never get their own `prime_<p>` lemma.
BASE_AVAILABLE = {2, 3, 149, 631}

# ===================================================================
# Primality testing -- Miller-Rabin (deterministic below 3.3 * 10**24;
# probabilistic with `rounds` random bases above that).
# ===================================================================

_SMALL_PRIMES = [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37]


def is_probable_prime(n, rounds=40):
    if n < 2:
        return False
    for p in _SMALL_PRIMES:
        if n % p == 0:
            return n == p
    d = n - 1
    r = 0
    while d % 2 == 0:
        d //= 2
        r += 1
    if n < 3317044064679887385961981:
        bases = _SMALL_PRIMES
    else:
        bases = [random.randrange(2, n - 1) for _ in range(rounds)]
    for a in bases:
        if a % n == 0:
            continue
        x = pow(a, d, n)
        if x == 1 or x == n - 1:
            continue
        for _ in range(r - 1):
            x = pow(x, 2, n)
            if x == n - 1:
                break
        else:
            return False
    return True


# ===================================================================
# Pollard's rho (Brent's improvement), for cracking a cofactor trial
# division cannot reach.  Only needed offline, to extend EXTRA if the
# pinned N above ever changes; `build_certificate` does not call this.
# ===================================================================

def brent(n, c, batch=128):
    """One attempt at a nontrivial factor of n, with parameter c."""
    if n % 2 == 0:
        return 2
    y = random.randrange(1, n)
    x = y
    r, q, g = 1, 1, 1
    while g == 1:
        x = y
        for _ in range(r):
            y = (y * y + c) % n
        k = 0
        while k < r and g == 1:
            ys = y
            step = min(batch, r - k)
            for _ in range(step):
                y = (y * y + c) % n
                q = (q * abs(x - y)) % n
                if q == 0:
                    break
            g = gcd(q, n)
            k += step
        r *= 2
        if r > 4_000_000:
            return None
    if g == n:
        while True:
            ys = (ys * ys + c) % n
            g = gcd(abs(x - ys), n)
            if g > 1:
                break
        if g == n:
            return None
    return g


def _rho_worker(args):
    n, seed, deadline = args
    random.seed(seed)
    while time.time() < deadline:
        c = random.randrange(1, n)
        try:
            d = brent(n, c)
        except Exception:
            continue
        if d and d != n and d != 1:
            return d
    return None


def pollard_rho_parallel(n, budget=120.0, nproc=16):
    """Search for one nontrivial factor of n across nproc worker processes
    for up to budget seconds; returns (factor, cofactor) or None."""
    import multiprocessing as mp

    deadline = time.time() + budget
    with mp.Pool(nproc) as pool:
        args = [(n, random.randrange(1, 2**62), deadline) for _ in range(nproc)]
        result = None
        for r in pool.imap_unordered(_rho_worker, args):
            if r is not None:
                result = r
                pool.terminate()
                break
    if result is None:
        return None
    return result, n // result


# ===================================================================
# The Pocklington-chain emitter: fully factor p - 1 (trial division plus
# any pre-supplied EXTRA split for a hard residual), find a witness base,
# and recursively emit a `prime_<p>` lemma for p and every prime factor of
# p - 1 it depends on.
# ===================================================================

def name_for(p):
    return f"prime_{p}"


def trial_division(n, bound=10**6):
    factors = []
    d = 2
    while d <= bound and d * d <= n:
        while n % d == 0:
            factors.append(d)
            n //= d
        d += 1 if d == 2 else 2
    return factors, n


def factor_counts(n, extra_factorizations=None, bound=10**6):
    """Fully factor n using trial division to `bound`, consulting
    extra_factorizations (dict: residual -> [prime,...] full factor list)
    for any residual cofactor trial division could not crack."""
    tf, rest = trial_division(n, bound)
    full = list(tf)
    if rest > 1:
        if is_probable_prime(rest):
            full.append(rest)
        elif extra_factorizations is not None and rest in extra_factorizations:
            full.extend(extra_factorizations[rest])
        else:
            raise RuntimeError(
                f"cannot factor residual {rest} (bits={rest.bit_length()}) of {n}; "
                "supply extra_factorizations (see pollard_rho_parallel)")
    full.sort()
    counts = {}
    for f in full:
        counts[f] = counts.get(f, 0) + 1
    return counts  # dict prime -> exponent


def find_witness(p, factor_list):
    """factor_list: the distinct prime factors of p - 1."""
    for a in range(2, 200):
        if pow(a, p - 1, p) != 1:
            continue
        ok = True
        for q in factor_list:
            e = (p - 1) // q
            if gcd(pow(a, e, p) - 1, p) != 1:
                ok = False
                break
        if ok:
            return a
    raise RuntimeError(f"no witness found for {p} in range")


def emit_chain(p, extra_factorizations=None, bound=10**6, memo=None, order=None):
    """Recursively emit Rocq lemma texts for p and all its dependencies.
    memo: dict prime -> True (already emitted or base-available).
    order: list accumulating (prime, text) in dependency order."""
    if memo is None:
        memo = {}
    if order is None:
        order = []
    if p in memo or p in BASE_AVAILABLE:
        return memo, order
    counts = factor_counts(p - 1, extra_factorizations, bound)
    distinct = sorted(counts.keys())
    for q in distinct:
        emit_chain(q, extra_factorizations, bound, memo, order)
    a = find_witness(p, distinct)
    dec_str = "(" + "::".join(f"({q},{e})" for q, e in sorted(counts.items())) + "::nil)"
    leaf_names = [f"prime{q}" if q in BASE_AVAILABLE else name_for(q) for q in distinct]
    proof_certifs = "::".join(
        f"(Proof_certif {q} {nm})" for q, nm in zip(distinct, leaf_names))
    proof_certifs = f"{proof_certifs}::nil" if proof_certifs else "nil"
    text = f"""Lemma {name_for(p)} : prime {p}.
Proof.
 apply (Pocklington_refl (Pock_certif {p} {a} {dec_str} 1)
        ({proof_certifs})).
 vm_cast_no_check (refl_equal true).
Qed.
"""
    memo[p] = True
    order.append((p, text))
    return memo, order


# ===================================================================
# The N-specific driver: chain the three hard cofactors, then assemble
# the top-level `secp256k1_N_prime_cert` lemma for N itself.
# ===================================================================

def build_certificate():
    memo, order = {}, []
    for p in (P1, P2, P3):
        emit_chain(p, extra_factorizations=EXTRA, memo=memo, order=order)

    distinct_n = [2, 3, 149, 631, P1, P2, P3]
    a_n = find_witness(N, distinct_n)
    counts_n = {2: 6, 3: 1, 149: 1, 631: 1, P1: 1, P2: 1, P3: 1}
    dec_str = "(" + "::".join(f"({q},{e})" for q, e in sorted(counts_n.items())) + "::nil)"
    leafname = lambda q: f"prime{q}" if q in BASE_AVAILABLE else f"prime_{q}"
    proof_certifs = "::".join(
        f"(Proof_certif {q} {leafname(q)})" for q in sorted(distinct_n)) + "::nil"

    top_text = f"""Lemma secp256k1_N_prime_cert : prime {N}.
Proof.
 apply (Pocklington_refl (Pock_certif {N} {a_n} {dec_str} 1)
        ({proof_certifs})).
 vm_cast_no_check (refl_equal true).
Qed.
"""

    parts = ["From Coqprime Require Import PocklingtonRefl.",
             "Local Open Scope positive_scope.",
             ""]
    for _, text in order:
        parts.append(text)
    parts.append(top_text)
    return "\n".join(parts)


# ===================================================================
# CLI: no args regenerates the certificate body on stdout; `factor <n>
# [budget] [nproc]` runs the parallel Pollard's-rho search (the old
# factor2.py entry point), for extending EXTRA if N ever changes.
# ===================================================================

if __name__ == "__main__":
    if len(sys.argv) > 1 and sys.argv[1] == "factor":
        n = int(sys.argv[2])
        budget = float(sys.argv[3]) if len(sys.argv) > 3 else 120.0
        nproc = int(sys.argv[4]) if len(sys.argv) > 4 else 16
        print(f"factoring n (bits={n.bit_length()}) with {nproc} workers, "
              f"budget {budget}s", flush=True)
        found = pollard_rho_parallel(n, budget, nproc)
        if found is None:
            print("NOT FOUND", flush=True)
            sys.exit(1)
        factor, cofactor = found
        print(f"FACTOR {factor} COFACTOR {cofactor}", flush=True)
        print("factor prime?", is_probable_prime(factor), flush=True)
        print("cofactor prime?", is_probable_prime(cofactor), flush=True)
    else:
        print(build_certificate(), end="")
