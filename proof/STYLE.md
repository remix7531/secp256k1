# Proof Style Guide

## Tactics

- **One tactic per line.** Never chain independent tactics with `;` on one line.
- Semicolons are allowed inside `by (...)` or `ltac:(...)` for short inline proofs:
  ```coq
  assert (H : 0 <= x) by (apply Z.div_pos; lia).
  ```
- A trailing `; solver` is allowed when the solver (e.g. `lia`, `nia`, `reflexivity`)
  closes all remaining subgoals in one shot:
  ```coq
  apply limb_add_0; lia.
  apply limb_add_2_u64; lia.
  ```
- A `; ` chain is allowed when all generated subgoals use the same tactic sequence:
  ```coq
  apply Zbits.eqmod_add;
      apply Zbits.eqmod_sym;
      apply Zbits.eqmod_mod;
      lia.
  ```
- `by (...)` is for proofs that fit on one line (1-3 tactics). Use `{ }` blocks for anything longer.
- `do N tactic` is allowed for repeated identical tactics (e.g. `do 3 f_equal.`), but not for VST tactics like `forward` -- each `forward` should be on its own line with a comment.
- `ltac:(...)` is for very short proof obligations passed as arguments (1-2 tactics). If longer than ~60 characters, assert separately first.
- Break multi-line arguments at the opening parenthesis, align continuations:
  ```coq
  forward_call (v_acc, acc_s1_1a,
                mkUInt64 n1 Hn1, mkUInt64 N_C_0 N_C_0_range, Tsh).
  ```

## Assertions

- Short proof: `assert (H : statement) by (tactic1; tactic2).`
- Long proof:
  ```coq
  assert (H : statement).
  { tactic1.
    tactic2.
    tactic3. }
  ```
- Group similar assertions together without blank lines between them:
  ```coq
  assert (Hm0 : 0 <= m0 < B) by (subst m0; apply Z.mod_pos_bound; lia).
  assert (Hm1 : 0 <= m1 < B) by (subst m1; apply Z.mod_pos_bound; lia).
  assert (Hm2 : 0 <= m2 < B) by (subst m2; apply Z.mod_pos_bound; lia).
  ```

## Branching

- Use `{ }` blocks with bullets (up to 3 nesting levels): `-` (level 1), `+` (level 2), `*` (level 3).
- `[ | ]` syntax is allowed in short single-line proofs (e.g. inside `by (...)`).
  For multi-line branching, use `{ }` with bullets instead.
- Each branch gets its own line:
  ```coq
  assert (0 <= t0).
  { subst t0. apply Z.add_nonneg_nonneg.
    - lia.
    - apply Z.mul_nonneg_nonneg; lia. }
  ```
- Closing `}` goes on the last line of the block when short, or on its own line when the block is long.
- Add a short comment on each major branch or conjunct explaining what it proves:
  ```coq
  repeat split.
  - (* conjunct 0: (sum / B^0) mod B = a0 *)
    rewrite Z.pow_0_r, Z.div_1_r.
    ...
  - (* conjunct 1: (sum / B^1) mod B = a1 *)
    rewrite Z.pow_1_r.
    ...
  ```

## Formatting

- 2-space indentation throughout.
- Contents of `{ }` blocks are indented by 2 relative to the `assert` or tactic that opened them.
- Bullet points (`-`, `+`, `*`) are indented to the block level, with their body indented by 2 more.
- For complex proofs, document the proof strategy in the lemma's doc comment before `Proof.`
- ASCII only. No Unicode characters (use `->` not the arrow glyph, `x` not
  the multiplication sign, `--` not an em dash).
- Prefer repetition over premature abstraction.
- Do not compress whitespace or join lines for compactness.

## Whitespace

Blank lines mark logical boundaries only -- minimal but meaningful. Do not pad, and do
not compress (the per-phase rhythm is required, not optional).

- One blank line **after** each `(* ===== phase ===== *)` banner, and one **between**
  phases (before the next banner).
- One blank line **after** `start_function`.
- A `forward` / `forward_call` cluster -- its C-op comment, the call, its `{ }`
  side-condition proof, and the following `Intros` / `rename H` -- is **tight (no
  internal blank lines)**; one blank line separates one cluster from the next.
- **No** blank lines within a run of related `set` / `assert` (they form one unit);
  one blank line between distinct groups.
- One blank line before and after a multi-line `assert (...). { ... }`.
- **No** blank line between a comment and the tactic it annotates.
- One blank line between top-level `Lemma` / `Definition`s; none before `Qed`.

Target rhythm: the mul-pipeline files (`verif/scalar/impl/scalar_muladd.v`,
`verif/scalar/impl/scalar_mul_512.v`) -- roughly one blank line per logical
step, about 20% of lines blank. Files compressed well below that read as dense
and must be re-spaced.

## Comments

### File header (top of every file; no banner)

```coq
(** * <Module>: <one-line description>. *)
(** Copyright (C) 2026 remix7531
    SPDX-License-Identifier: MIT *)
```
Continuation lines of the copyright block are indented 4 spaces to align under the text.
The `<Module>` is the file's logical name (e.g. `Verif_muladd`, `model.scalar`).

### Section banner: ONE line ABOVE the heading (never a sandwich)

```coq
(* ================================================================= *)
(** ** Section name -- [refs] / elaboration. *)

<one blank line, then content>
```
- The banner is exactly **65 `=`** signs: `(* ` + 65x`=` + ` *)` (71 chars). It goes **above** the `(** ** ... *)` heading only -- do NOT add a banner below it, and do NOT stack `=`/`-` banners.
- Headings are descriptive: a name, then ` -- ` separating it from elaboration, `[brackets]` around code/identifier references, ending with `.`
  (e.g. `(** ** Lengths -- [SHA256] / [chain]. *)`). One blank line follows the heading.
- Subsections use `(** *** Name *)`, optionally preceded by a 65-`-` divider:
  ```coq
  (* ----------------------------------------------------------------- *)
  (** *** Subsection name. *)
  ```

### Three comment levels

1. **Section** -- the 65-`=` banner + `(** ** *)` heading above (file structure), as above.

2. **Proof phase** -- inside `Proof. ... Qed.`, open each major phase with
   ```coq
   (* ===== Phase name: detail ===== *)
   ```
   exactly 5 `=` on each side. Use `=====` for phases (never `-----`). Number stages/rounds
   consistently (`Stage 0`, `Round 1`, ...). Put one at: after `start_function`, each
   round/stage boundary, the postcondition, and the pure-Z arithmetic tail.

3. **Inline** -- **every `forward` / `forward_call` gets a comment**, on the line
   immediately above it (no blank line between), mirroring the C statement being verified:
   ```coq
   (* secp256k1_u128_mul(&t, a, b) *)
   forward_call (...).
   ```
   For tight low-level load/store pairs a trailing same-line comment is allowed:
   `forward. (* _t'7 = acc->c0 *)`. Append clarifications with ` -- `
   (e.g. `(* extract_fast(&acc, &l8[0]) -- needs acc < 2^128 *)`).

- `(** ... *)` doc comments are used ONLY outside proofs (on `Lemma` / `Definition`),
  describing intent -- the C op, the math, or the postcondition -- in 1-3 lines, with
  `[name]` for code references. Inside proofs use only `(* ... *)`.
- Branches / conjuncts get a short **tag**, not prose:
  `(* branch: j = 0 -- post reduces to a *)`, `(* conjunct 1: (sum / B) mod B = a1 *)`.
- For a multi-step math proof, stage it with `(* Setup: ... *)` / `(* Main: ... *)` /
  `(* Closeout: ... *)`.

## Context & Naming

### Identifiers and casing

Follow standard Rocq naming, but **never CamelCase**.

- **snake_case for everything value-level**: `Definition`s, `Fixpoint`s, functions,
  `Lemma` / `Theorem` / `Corollary` names, `Ltac` tactics, section variables, and
  hypotheses. Lowercase words separated by `_`. Never camelCase -- write
  `process_divstep` and `add_upper_point`, not `processDivstep` / `addUpperPoint`.
- Prefix native identifiers by subsystem to match the surrounding file
  (`secp256k1_scalar_mul`, `fe_mul`, `round_bit_eq`).
- **Leading-capital for type-level / namespace identifiers**, per Rocq: `Inductive`
  type names, constructors, `Module`s, `Section`s, and `Class` / `Instance`s start
  with a capital. Single-word capitals are the norm (`Some`, `Lt`, `State`); for
  multi-word names use `Capital_snake_case` (e.g. `On_path`, `On_path_between`), not
  PascalCase -- the no-interior-capitals rule keeps CamelCase out everywhere.
- **Lemma names read `subject_property`** (subject on the left), reusing the standard
  Rocq suffixes so the statement is guessable from the name:
  - semantics: `_correct`, `_spec`, `_sound`, `_complete`, `_eq`, `_iff`.
  - algebra: `_comm`, `_assoc`, `_distr`, `_id`, `_inv`, `_0` / `_1`, `_l` / `_r`.
  - relations: `_refl`, `_sym`, `_trans`, `_antisym`, `_inj`, `_surj`, `_mono`, `_morph`.
  - order / bounds: `_lt`, `_le`, `_gt`, `_ge`, `_pos`, `_neg`, `_bound`, `_range`.
  - lists / structure: `_nil`, `_cons`, `_app`, `_map`, `_in`, `_rev`.

  Compose and stack them left-to-right: `add_comm`, `mul_le_mono_r`,
  `process_divstep_correct` (not `correct_process_divstep`).

### Context hygiene

- Hypothesis names: `H` prefix + descriptive (`Hd0`, `Hchain`, `Hr_z_bnd`).
- Intermediate values: `set (name := expr).` with short descriptive names.
- `clear` intermediates as soon as they are no longer needed. Large VST contexts slow down tactics significantly.
- Use `clear -` (keep only listed hypotheses) at stage boundaries to reset the context.
- `rename H into Hname` immediately after `Intros` to give hypotheses meaningful names.

## Imports

- Standard library: `From Stdlib Require Import ZArith.`
- Group imports by origin (stdlib, project, external) with a blank line between groups.

## Funspecs

Funspecs follow one canonical shape: spaced delimiters (`PROP (...)`, `SEP (...)`,
`RETURN ()`), the POST existential on its own line, named `*_at` spatial predicates
in `SEP` (not raw `data_at`), and **one `PROP`/`SEP` conjunct per line**, aligned
under the opening paren.

```coq
Definition spec_secp256k1_foo : ident * funspec :=
  DECLARE _secp256k1_foo
  WITH x : Z, m : Z, ptrx : val, modinfo : val,
       shx : share, sh_modinfo : share, gv : globals
  PRE [ tptr t_secp256k1_modinv64_signed62, tptr t_secp256k1_modinv64_modinfo ]
    PROP (Z.Odd m;
          0 <= x < m;
          writable_share shx;
          readable_share sh_modinfo)
    PARAMS (ptrx; modinfo)
    GLOBALS (gv)
    SEP (signed62_at shx ptrx x;
         modinfo_at sh_modinfo modinfo m)
  POST [ tvoid ]
    EX rv : Z,
    PROP (0 <= rv < m;
          rel_prime x m -> Z.modulo (Z.mul x rv) m = 1)
    RETURN ()
    SEP (signed62_at shx ptrx rv;
         modinfo_at sh_modinfo modinfo m).
```

- `PRE [ ... ]` keeps the C argument types on one line when they fit; otherwise one
  type per line, trailing comma, aligned under the first.
- `WITH` binders wrap at a sensible width with the continuation aligned.
- Spatial resources use the `*_at` notations (`u128_at`, `scalar_at`, `fe_at`,
  `signed62_at`, `modinfo_at`, ...) from `contract/helper/notations.v` (and
  `contract/helper/signed62.v` for the modinv structs), never raw `data_at` --
  except where no notation fits the value shape (e.g. the `pad`-based and
  `trans2x2` resources, or uninitialised `data_at_`).
- Empty clauses are `PROP ()` / `RETURN ()`.

## VST proof style

- Comment before each `forward_call` explaining the C operation.
- Side condition proofs in `{ }` blocks.
- `Intros` / `rename H` / `assert` / `clear` each on their own line:
  ```coq
  (* secp256k1_u128_from_u64(&t, d0) *)
  forward_call (v_t, mkUInt64 d0 Hd0, Tsh).
  Intros t_init.
  rename H into Ht_init.
  ```

## Proof automation

The automation layer lives under `tactics/`. Prefer it over hand-rolled
patterns:

- **`rep_lia` over `lia`** for goals involving `UInt64` / `UInt128` / `Acc`
  values. The `rep_lia_setup2` hook (in `tactics/core.v`) auto-poses the
  carried range fact for every `u64_val ?x`, `u128_val ?x`, `acc_val ?x`,
  `u256_val ?x` in the goal, eliminating manual
  `pose proof (u64_range x)` calls. There is exactly ONE `rep_lia_setup2 ::=`
  override in the project; extend it there, never re-override elsewhere.
- **`forward_call_*` wrappers**, declared per subsystem (`tactics/int128.v`,
  `tactics/scalar.v`, ...), bundle each `forward_call` with `Intros`,
  `rename H`, optional `destruct`, and `deadvars!`. They auto-discharge the
  parameter-matching obligation via `solve_param_match` (which rewrites with
  the `to_val_limb` Hint database) and the linear PROP via
  `try (simpl; rep_lia)`. Use them in preference to raw
  `forward_call (...) ; Intros ...`.
- **Constants**: use `N_C_0_u64`, `N_C_1_u64`, `N_C_2_u64` (declared in
  `tactics/scalar.v`), not the verbose `mkUInt64 N_C_i N_C_i_range`. They
  are registered with `Hint Rewrite` in the `rep_lia` database so
  `u64_val N_C_i_u64` reduces automatically.
- **Limbs**: use the generic `limb (2^64) v i` from `theory/arithmetic.v`.
  The C-representation definitions (`uint128_to_val`, `acc_to_val`,
  `uint256_to_val`, `uint512_to_val` in `contract/helper/repr.v`) use
  **inline splits** `(v / 2^k) mod 2^64` in their bodies, matching the spec
  style. Bridge lemmas `uint128/acc/uint256/uint512_to_val_limb` (registered
  with `Hint Rewrite ... : to_val_limb`) equate the inline form to
  `limb (2^64) v i`, so proofs can convert with `autorewrite with to_val_limb`.
- **`limb_at_0` lemma** (`theory/bits.v`): rewrites `limb (2^64) v 0` back to
  `v mod 2^64`. Use `rewrite ?limb_at_0` in proofs that prefer the mod form.
- **`Hint Rewrite ... : rep_lia`** is the registry for any lemma that
  `rep_lia` should auto-apply (e.g. constant unfoldings, projector
  reductions, limb-of-known-value identities). The registrations live next
  to the definitions they unfold (e.g. `secp256k1_N_val` in
  `model/constants.v`); the database is string-keyed and merges at use site.
- **modinv (safegcd) proofs use the same layer as every other subsystem** --
  there is no subsystem-specific search automation. `rep_lia` and its
  `Hint Rewrite` registries close the linear side goals; the
  `forward_call_*` wrappers step the divstep / normalize / update helpers;
  the `vst/integers.v` word bridges come in via `autorewrite with int_to_z`
  plus an explicit `rewrite Int64.signed_repr by rep_lia` /
  `Int64.unsigned_repr by rep_lia` where a range side condition is needed;
  the `theory/modinv/bounds.v` interval lemmas (`umul_bounds_tight`,
  `smul64_bounds_tight`, `unadd_bounds_*`, ...) close with a direct
  `apply <lemma>; lia`. See "Banned in verif/" below for what replaced the
  old vendored search tactics.
- **Shift/pow-heavy proofs**: `Require Import secp256k1.tactics.hygiene`
  LAST sets `Arguments ... : simpl never` and `#[global] Opaque` for
  `Z.shiftl` / `Z.shiftr` / `Z.pow`, so `forward` does not diverge unfolding
  `Int64.Z_mod_modulus` under a shift. A bare `Opaque` does not survive a
  `Require` in Rocq 9 -- that is why the directive is `#[global]` -- and
  neither form blocks `vm_compute` / `native_compute`, so ground reflection
  proofs are unaffected.

### Banned in verif/

`tactics/` carries no search or macro automation for `verif/`. The Ltacs
below, familiar from other VST developments, are not available here; each
one expands to a short, explicit step written out at the call site:

| Banned | Use instead |
| - | - |
| `progressC` | a commented `forward` plus its `{ }` side-goal block |
| `convert_C_to_math` | `autorewrite with int_to_z` + an explicit `signed_repr` / `unsigned_repr` rewrite |
| `solve_bounds` / `solve_bounds_body` | a named `assert ... by (apply <lemma>; lia)` per obligation |
| `clear_mod` | `rewrite Z.mod_small by lia` at the site |
| `forward_verify_check` | nothing -- the VERIFY-off extraction has no check statements |
| `unfold_C` | nothing -- `rep_lia` already knows the word constants; `change` a shift count by hand if one is buried in an expression |
| `fastforward N` / `do N forward` | `N` commented `forward`s, one per C statement |
| `2:{ }` / `all:` / a multi-line `[ | ]` | `{ }` + bullets, or a hoisted named `assert` |
| `match goal with [H : ...] => rename ... end` | `rename H into ...`, after naming the PROP hypotheses up front from `Intros` |
| an inline `Opaque` / `Transparent` | `Require Import secp256k1.tactics.hygiene` last; ground a concrete identity with `vm_compute` instead of un-opacifying |
| `clearbody` / `set ... in *` / `rewrite ?... in *` as a speed crutch | allowed only with a one-line comment giving the measured with/without time |

## Vendored theory exception

`theory/modinv/divsteps/**` and `theory/modinv/construction/bezout.v` are
ports of the upstream sipa/safegcd-bounds and BlockstreamResearch/simplicity
developments and keep their upstream tactic idioms (`auto with *`,
`abstract`, `Defined` where upstream closes a proof that way) rather than
being reground into house style. Only the header (this project's MIT header
plus the upstream attribution line), doc comments, indentation, and bullets
are house-styled there; the tactic script itself stays as close to upstream
as it compiles. Do not "clean up" a proof in these files by replacing its
`auto with *` / `Defined` with a from-scratch `lia` / `Qed` rewrite -- that
is a resync-with-upstream decision, not a style fix.

## File and directory naming

- Every directory and file under `proof/` is `lower_snake_case`
  (`contract/helper/structs_modinv.v`,
  `verif/modinv/impl/modinv64_normalize_62.v`).
- `verif/` is one `semax_body` per file, named for the C function it proves
  with the `secp256k1_` prefix dropped when that leaves the name unambiguous
  (`verif/scalar/scalar_add.v` proves `secp256k1_scalar_add`;
  `verif/util/ctz64_var_debruijn.v` proves `secp256k1_ctz64_var_debruijn`).
  The lemma inside keeps the full C name: `body_secp256k1_scalar_add`.
- `impl/` under a subsystem directory holds the `static` (internal-linkage)
  helpers that module's C code calls but does not export
  (`verif/scalar/impl/`, `verif/modinv/impl/`, `verif/int128/impl/`),
  mirroring the split between a header's public API and its `.c`-local
  helpers.
- Subsystem directories (`field/`, `int128/`, `modinv/`, `scalar/`, `util/`)
  mirror the `src/` module they verify, and carry the same name across
  `theory/<sub>/`, `contract/gprog/<sub>.v`, `tactics/<sub>.v`, and
  `verif/<sub>/`.

## Lemma-name suffixes (project artifacts)

The generic Rocq suffixes above name what a lemma proves; this project also
has a small set of fixed names for what layer/role an artifact plays:

| Pattern | Meaning |
| - | - |
| `_eq` | a definitional / reflective equality |
| `_bound` / `_bnd` | a numeric interval fact (`0 <= x < 2^64`) |
| `_repr` | an `Int64.repr` / `Int.repr` representation bridge |
| `<name>_at` | a spatial (`SEP`) predicate notation, e.g. `u64_at`, `signed62_at`, `modinfo_at` (declared in `contract/helper/notations.v` or the subsystem's own contract file) |
| `body_secp256k1_<fn>` | the `semax_body` lemma proving `secp256k1_<fn>`'s contract |
| `spec_secp256k1_<fn>` | the `funspec` (`DECLARE`) for `secp256k1_<fn>` |
| `Gprog_<sub>` | the per-subsystem `Gprog` list bound in `contract/gprog/<sub>.v` |

## Where a lemma goes

- Pure `Z` fact with no VST/CompCert content -> `theory/` (generic core at
  the root; a per-subsystem fact goes in `theory/<sub>/`).
- A fact about the pure functional specification -> `model/` (purity-gated:
  no `VST.*` / `compcert.*` / `secp256k1.clight` / `secp256k1.vst` imports).
- A CompCert/VST word-level bridge with no funspec content (an `Int64.repr`
  identity, a mask/shift lemma) -> `vst/` (e.g. `vst/integers.v`).
- A representation predicate, a funspec, or a fact that exists only to
  discharge one -> `contract/` (`contract/<sub>.v` for the funspec + `_at`
  bridges, `contract/helper/` for the cross-subsystem plumbing frozen there,
  `contract/impl/` for a `static` helper's contract).
- Reusable Ltac -> `tactics/<sub>.v` (or `tactics/core.v` if it is
  subsystem-free).
- A `verif/` file holds ONLY its own body proof and the facts it uses
  exactly once. The moment a fact is needed by a second proof, hoist it to
  the layer above -- do not `Require` one verif file from another.

## Licence header

Every file under `proof/` (generated `clight/` excepted) opens:

```coq
(** * <Module>: <one-line description>. *)
(** Copyright (C) 2026 remix7531
    SPDX-License-Identifier: MIT *)
```

A ported file keeps its upstream provenance between the two lines instead of
dropping it on restyle:

```coq
(** * <Module>: <one-line description>. *)
(** Copyright (C) 2026 remix7531
    Ported from <upstream project> <upstream path>
    (commit <hash>), Copyright (c) <year> <upstream holder>, originally MIT.
    Upstream notice reproduced in proof/README.md.
    SPDX-License-Identifier: MIT *)
```

The whole tree is MIT under the repository root's `COPYING`; the SPDX line
says so even in a ported file. The attribution block names the upstream
copyright holder rather than the individual authors, because the holder is
who the upstream licence names. Never delete it when restyling a ported file
to house style. Continuation lines of the Copyright/attribution block are
indented 4 spaces to align under the text.

MIT requires the upstream copyright notice and permission notice to travel
with the code, so both are reproduced in full in the License section of
`proof/README.md` and every ported header points there. A link to the
upstream `LICENSE` is not a substitute. A project file that carries only a
few ported lemmas keeps one attribution block in the file header and names
the ported lemmas in it (`vst/integers.v`).

## Unported vendoring

A wholesale vendor drop that is NOT restyled to house style -- no header
rewrite, no comment-banner conversion, kept close to what upstream ships --
goes under `deps/<name>/` with its own `LICENSE` file, and is never edited
in place; a needed fix is a shim or a wrapper living outside `deps/`, not a
patch to the vendored source. This is stricter than the "Vendored theory
exception" above: a file that gets a house-style header and attribution
line but keeps its upstream tactic idioms is a restyled port, not unported
vendoring, and lives in its ordinary layer directory, not under `deps/`.
Nothing in the tree currently needs this tier; it is here so the next
wholesale drop has a home decided in advance.

## Gates

`audit/check.sh` is the mechanical honesty gate, seven checks:

0. Build freshness -- every file listed in `_RocqProject` has an up-to-date
   `.vo`. `model/tests_slow_*.v` are exempted from the "every layer `.v` is
   tracked in `_RocqProject`" half of this check, the same way
   `audit/assumptions.v` is: they are the slow curve KATs, deliberately kept
   out of `_RocqProject` because each one costs 10 to 50 minutes under
   `vm_compute` (built on request via `make model-tests`, never by `make
   proof` / `make audit`). The gate's OK/FAIL line reports how many files
   that exemption covered.
0b. AST fingerprint -- `clight/extraction.v` matches the pinned
    `audit/extraction.sha256`, so a silent re-extraction cannot swap the AST
    the proofs are checked against.
1. Proof gaps -- no `Admitted.` / `admit.` / `give_up.` anywhere under
   `proof/` except the register of scaffolded
   `model/` lemmas in `audit/scaffold.txt` (one `path:lemma` per line). The
   gate is a two-way match: every `Admitted.` site outside the sanctioned
   carve-out must have a `scaffold.txt` line naming its file and its nearest
   preceding `Lemma`/`Theorem`/`Corollary`, and every `scaffold.txt` line must
   name a real `Admitted.` site -- a stale entry (one whose lemma has since
   been proved or renamed) fails the gate exactly like an unregistered gap
   does. `scaffold.txt`'s first line may be a `# count: N` ratchet comment;
   when present it must equal the file's actual entry count. The gate prints
   the registered count per file.
2. Axiom confinement -- every top-level `Axiom`, `Parameter`, and section
   `Hypothesis` under `proof/` is confined to the files on the gate's
   explicit allowlist; today that is
   `theory/modinv/divsteps/{bound724,bound590}.v` (`example724` /
   `example590`) plus `model/tables.v` (the three precomputed-table
   `Parameter`s and their nine characterisation `Axiom`s) -- see
   `audit/AXIOM_WHITELIST`. (`model/constants.v`'s `secp256k1_N_prime` used
   to be a fourth allowed file; it is now a `Qed` lemma, discharged by a
   coqprime Pocklington certificate in `theory/primality/n.v`, so it no
   longer declares an `Axiom` at all.) Every name `model/tables.v` declares
   must also appear in `audit/scaffold.axioms` (one name per line, no
   comments needed); the gate prints `model/tables.v`'s Parameter/Axiom
   counts. `scaffold.axioms` is a source-side name-completeness ratchet only
   -- it is NOT consulted by gate 4, and its names are not whitelisted there
   until some body proof's assumption cone actually depends on one of them
   (a separate, reviewed `audit/AXIOM_WHITELIST` edit at that time).
3. Headline pin -- a statement file under `audit/` (`statement`, added with
   the reviewer-facing headline) probes the audited theorem(s) by name and
   pasted type, so a silent rename or a swap for a weaker namesake fails the
   build rather than passing quietly (reported as SKIP until that file exists).
4. Assumption cone vs whitelist -- `Print Assumptions` on
   `audit/assumptions.v`'s `verified_surface` must stay within
   `audit/AXIOM_WHITELIST`.
5. Style greps -- some of this document's mechanically-checkable rules
   (ASCII-only, the license header shape, the banned-tactic table above)
   enforced by grep, including sub-check 5h: `grep -rn 'contract\.gprog'
   tactics/` must be empty -- a tactics file may never import a proving
   context (see "Where a lemma goes").

`make audit` runs all seven. `make axioms` runs the model/theory purity check
plus gate 4 alone (the narrower check this project has always run before a
commit). `make style` runs gate 5 alone. `make model-tests` compiles the slow
`model/tests_slow_*.v` KATs one at a time (10 to 50 minutes each) -- it is
separate from both `proof` and `audit`.
