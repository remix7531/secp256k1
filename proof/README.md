# secp256k1 proofs

[![proof](https://github.com/remix7531/secp256k1/actions/workflows/proof.yml/badge.svg)](https://github.com/remix7531/secp256k1/actions/workflows/proof.yml)

Rocq specifications and VST proofs for libsecp256k1.

CompCert's `clightgen` extracts the production C functions and precomputed
tables through `extraction.c`.

## Build

From the repository root:

```sh
nix develop
cd proof
make proof             # build the project
make specification     # build only the specification and its dependencies
make html              # render the specification
make axioms            # report project assumptions
make vectors           # run SHA256 and BIP340 known-answer tests
```

These targets build serially unless you ask for parallelism, with either
`make -j8 proof` or `NPROC=8 make proof`, which an explicit `-j` overrides.
Size it by memory rather than by cores: a VST body proof peaks at about
1.4 GB resident and the heaviest at 4 GB, so allow roughly 2 GB of free
memory per job. Count memory that is free rather than available.

`make axioms` reports assumptions from every module in `_RocqProject` and
its imports without rechecking compiled proofs. Review the reported axioms
and admitted proofs.

`make verif-scalar` builds one C proof subsystem and its dependencies.
The other subsystem targets are `verif-int128`, `verif-util`, `verif-field`,
and `verif-modinv`. Vector tests are separate because scalar multiplication
makes them slow. `make clean` removes proof artifacts and HTML, preserving
`clight/` and the arithmetic tactic caches. `make purge` also removes
those retained files.

Every build prints one timing line per file and writes per-command times
to `<file>.v.timing`. Pass `TIMED=` or `TIMING=` to disable either.
`python3 doc/critical_path.py` combines those times with the dependency
graph and prints the chain of files that bounds parallel build time.

## Read the proof

Start with `specification.v`, or its rendered version at
`html/secp256k1.specification.html`. The HTML hides supporting proof details
and includes a source download for use in a Rocq editor.

- `specification.v` contains the mathematics and public C API contracts.
- `theory/` contains integer lemmas and models of C algorithms.
- `vst/` contains C contracts and individual body proofs. The Schnorr VSU
  target is in `specification.v`.
- `vectors/` contains known-answer tests.
- `doc/` contains the HTML renderer, templates, and stylesheet.
- `STYLE.md` describes proof conventions.

## Scope

Consult the theorem statements and the output of `make axioms` for the
guarantees and assumptions of the development.

The proofs establish functional correctness and memory safety under CompCert
semantics. They say nothing about execution time, side channels, or the
constant-time properties the library's masking and `volatile` hardening are
written to provide. Descriptions of a function as constant-time in this tree
name the upstream design intent, not a proved property.

The proofs apply to the extraction configuration in `Makefile` and
`extraction.c`: the struct-based 128-bit backend, libc-free code, software
bit counting, disabled `VERIFY` checks, and removed `volatile` qualifiers.
Callers must satisfy each function's contract.

The library source itself was changed to make it tractable for verification:
the scalar accumulator macros became `static inline` functions, a few helpers
were lifted out of inline code, and the library routes memory operations
through internal wrappers. `git diff <merge-base>...HEAD -- src/ include/`
shows the whole production diff. Those changes are not yet upstream.

The proof relies on Rocq, VST, CompCert semantics, and the reported
assumptions. Whether the specification states the intended BIP340 rules
remains a matter for review.

## License

MIT, under the repository's `COPYING`.

Files adapted from [sipa/safegcd-bounds](https://github.com/sipa/safegcd-bounds)
at commit `06abb7f` and from
[BlockstreamResearch/simplicity](https://github.com/BlockstreamResearch/simplicity)
at commit `c1dddedd` name their upstream in the file header. Both upstreams are
MIT and their notices are reproduced below.

```
MIT License

Copyright (c) 2021 Blockstream

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all
copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
SOFTWARE.
```

```
MIT License

Copyright (c) 2018 Blockstream

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all
copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
SOFTWARE.
```

The specification imports Coqprime as an external dependency. Coqprime is
licensed under the GNU Lesser General Public License version 2.1 in its
entirety; the modules used here are `List.UList`, `PrimalityTest.Euler`,
`PrimalityTest.Zp`, `elliptic.GZnZ`, `elliptic.SMain`, `elliptic.ZEll`, and
`examples.PocklingtonRefl`. It is not vendored and no build artifacts are
distributed, so the proof tree remains a source-only MIT distribution.
