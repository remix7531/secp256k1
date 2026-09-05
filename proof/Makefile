# Formal verification build for secp256k1 (Rocq + VST + CompCert).
#
#   make extract      : clightgen extraction.c into clight/extraction.v.  One
#                        unit #includes the library's real headers (scalar,
#                        int128, modinv64, field) so the whole proof tree
#                        shares one AST.
#   make proof        : build the Rocq proofs against that AST.
#   make verif-<sub>  : build only verif/<sub>/ (and its dependencies) --
#                        int128, util, scalar, field, modinv.
#   make timing       : TIMED build + a slowest-files table; add BASELINE=1
#                        to (re)write audit/timing-baseline.txt.
#   make model-tests  : compile each model/tests_slow_*.v in sequence (10-50
#                        MINUTES EACH) -- the slow curve KATs excluded from
#                        _RocqProject; not part of `proof` or `audit`.
#
# Run inside the dev shell from the repo-root flake (`nix develop` or direnv).

NPROC := $(shell nproc)

# Extraction units: each <unit>.c clightgens to clight/<unit>.v via the pattern
# rule below.  One unit today; a second (tables.c -> clight/tables.v, for the
# precomputed ecmult tables under the extern-tables convention documented in
# extraction.c) is reserved for the ecmult phase -- add it here, nothing else
# changes.
EXTRACT_SRCS := extraction.c
SOURCES_V := $(patsubst %.c,clight/%.v,$(EXTRACT_SRCS))

# Re-extract when the unit OR any library header it #includes changes: clightgen
# inlines those headers, so a header edit must invalidate the AST.  The wildcard
# is a safe superset of the actually-included headers.
HEADER_DEPS := $(wildcard ../src/*.h ../include/*.h)

# Pure-C, struct-based 128-bit arithmetic (CompCert has no __int128), no asm.
FV_DEFINES      := -DUSE_FORCE_WIDEMUL_INT128_STRUCT=1

# modinv's ctz64_var uses __builtin_ctzll, which clightgen cannot translate;
# -U__has_builtin forces util.h to fall back to the De Bruijn software path.
# Compiled VERIFY-off (no -DVERIFY): the VERIFY_CHECK assertions and the
# verify-only helpers (abs/mul_62/mul_cmp_62/det_check_pow2) are absent from the
# AST, so the proofs reason about exactly the production (VERIFY-off) build.
CLIGHTGEN_FLAGS := -normalize -I../include -I../src -Wp,-w -U__has_builtin

# Verif subsystem directories (derive from _RocqProject, not hardcoded twice).
VERIF_V := $(shell grep -E '^verif/' _RocqProject)
SUBS    := int128 util scalar field modinv

# Indirection for the two new targets below ONLY (proof/clean keep using
# $(MAKE) directly, unchanged).  GNU Make treats a recipe LINE containing the
# literal text "$(MAKE)" or "${MAKE}" as a recursive-make invocation and runs
# that whole line for real even under -n/-q/-t -- the nested make then honors
# -n too (inherited via MAKEFLAGS) so it doesn't compile anything, but any
# other command chained on the same line (e.g. `tee` into a log file) is NOT
# dry-run-gated and executes for real.  Referencing $(SUBMAKE) instead avoids
# that literal-text trigger, so `make -n timing` / `make -n verif-<sub>` are
# genuine no-ops (verified: an earlier draft without this left a stray,
# harmless-but-real audit/timing.log from a `make -n timing` dry run).
SUBMAKE = $(MAKE)

# NOTE: verif-<sub> (from the verif-% pattern rule below) is deliberately NOT
# listed here, in any form -- neither spelled out (verif-int128 ... verif-
# modinv) nor via $(addprefix verif-,$(SUBS)).  GNU Make's .PHONY is a plain
# prerequisite list with no pattern support: mentioning a concrete name there
# registers it as an explicit (recipe-less) rule, and an explicit rule always
# wins over a matching %-pattern rule -- even an empty one.  The result is a
# *silent* "Nothing to be done for 'verif-modinv'" no-op instead of a build
# (verified empirically against GNU Make 4.4.1: both forms above defeat the
# pattern rule the same way). Leaving verif-<sub> off .PHONY does not weaken
# anything here: it never corresponds to a real file, so make always treats
# it as out of date and reruns the recipe -- the same practical behaviour
# .PHONY exists to give, just not spelled that way.
.PHONY: all extract proof clean axioms audit style timing model-tests

all: proof

# The safegcd-bounds divsteps convergence library (MIT-origin, pure Coq math)
# lives under theory/modinv/divsteps, listed in _RocqProject under the single `secp256k1`
# logical name, so `make proof` compiles it; it is NOT a separate Coq project.

extract: $(SOURCES_V)

clight/%.v: %.c $(HEADER_DEPS)
	@mkdir -p $(@D)
	clightgen $(CLIGHTGEN_FLAGS) $(FV_DEFINES) -o $@ $<

proof: Makefile.rocq $(SOURCES_V)
	@$(MAKE) -j $(NPROC) --no-print-directory -f Makefile.rocq
	@printf '\033[1;34m\xE2\x9C\x93 All verifications succeeded\033[0m\n'

Makefile.rocq: _RocqProject
	@rocq makefile -f _RocqProject -o Makefile.rocq

# ---- Per-subsystem verif targets -------------------------------------------
# `make verif-<sub>` builds only the .vo files under verif/<sub>/ (plus
# whatever Makefile.rocq's generated dependency rules pull in beneath them) --
# useful for iterating on one subsystem without a full `make proof`.
verif-%: Makefile.rocq $(SOURCES_V)
	@$(if $(strip $(filter verif/$*/%,$(VERIF_V))),,$(error verif-$*: no files under verif/$*/ in _RocqProject (known subsystems: $(SUBS))))
	@files="$(filter verif/$*/%,$(VERIF_V))"; \
	vo=""; for f in $$files; do vo="$$vo $${f%.v}.vo"; done; \
	$(SUBMAKE) -j $(NPROC) --no-print-directory -f Makefile.rocq $$vo

# ---- Timing / maintainability target ---------------------------------------
# `make timing` is only meaningful right after `make clean` (or a `touch` of
# the files you want timed): a warm tree recompiles nothing, so the table and
# baseline would come out empty.  Deliberately does NOT depend on `clean`.
# `make timing BASELINE=1` (re)writes audit/timing-baseline.txt from this run;
# plain `make timing` instead compares against an existing baseline (if any)
# and flags files running over 1.25x their recorded time.  Parsing lives in
# audit/timing.sh (bash/awk/sed only) so it can be run standalone on any log.
timing: Makefile.rocq $(SOURCES_V)
	@mkdir -p audit
	@bash -c 'set -o pipefail; $(SUBMAKE) -j $(NPROC) --no-print-directory -f Makefile.rocq TIMED=1 2>&1 | tee audit/timing.log'
	@bash audit/timing.sh table audit/timing.log 10
	@if [ "$(BASELINE)" = "1" ]; then \
	  bash audit/timing.sh baseline audit/timing.log audit/timing-baseline.txt; \
	  echo "wrote audit/timing-baseline.txt"; \
	elif [ -e audit/timing-baseline.txt ]; then \
	  bash audit/timing.sh compare audit/timing.log audit/timing-baseline.txt 1.25; \
	fi

# ---- Trust-base / axiom gate ----------------------------------------------
# Recompile the out-of-tree trust-base file (audit/assumptions.v), capturing
# its `Print Assumptions` output, then fail if any public body proof depends on an
# axiom not declared in audit/AXIOM_WHITELIST.  assumptions.v is deliberately NOT in
# _RocqProject (so a normal `make proof` is not flooded with assumption dumps); it
# is compiled here against the .vo built by the `proof` prerequisite.  Project
# load-path flags are derived from _RocqProject so they never drift.
ROCQ_FLAGS := $(shell grep -E '^(-Q|-R|-arg)' _RocqProject | sed -E 's/-arg +//g' | tr '\n' ' ')

axioms: proof
	@echo "Checking model/ + theory/ purity (no VST/CompCert/AST imports) ..."
	@! grep -rlE 'Require .*(VST\.|compcert\.|secp256k1\.(clight|vst))' model/ theory/ \
	  || { echo "PURITY: FAIL -- model/ or theory/ imports the VST/AST layer (files above)"; exit 1; }
	@echo "Auditing trust base (audit/assumptions.v) ..."
	@rocq compile $(ROCQ_FLAGS) audit/assumptions.v > audit/assumptions.log 2>&1 \
	  || { echo "AXIOMS: FAIL -- assumptions.v did not compile:"; tail -20 audit/assumptions.log; exit 1; }
	@bash audit/check.sh 4

# ---- Full audit gate -------------------------------------------------------
# Everything `axioms` checks, plus freshness, the AST pin, proof-gap scan,
# axiom-declaration confinement, the headline pin (once audit/statement.v
# exists), and the style greps.  Reuses the same trust-base compile as
# `axioms` above so the log is produced exactly the same way.
audit: proof
	@echo "Checking model/ + theory/ purity (no VST/CompCert/AST imports) ..."
	@! grep -rlE 'Require .*(VST\.|compcert\.|secp256k1\.(clight|vst))' model/ theory/ \
	  || { echo "PURITY: FAIL -- model/ or theory/ imports the VST/AST layer (files above)"; exit 1; }
	@echo "Auditing trust base (audit/assumptions.v) ..."
	@rocq compile $(ROCQ_FLAGS) audit/assumptions.v > audit/assumptions.log 2>&1 \
	  || { echo "AUDIT: FAIL -- assumptions.v did not compile:"; tail -20 audit/assumptions.log; exit 1; }
	@if [ -e audit/statement.v ]; then \
	  echo "Checking the headline pin (audit/statement.v) ..."; \
	  rocq compile $(ROCQ_FLAGS) audit/statement.v > audit/statement.log 2>&1 \
	    || { echo "AUDIT: FAIL -- statement.v did not compile:"; tail -20 audit/statement.log; exit 1; }; \
	fi
	@bash audit/check.sh all

# `make style` is a pure grep gate: no build prerequisite.
style:
	@bash audit/check.sh 5

# ---- Slow model KAT tests (opt-in, NOT part of `proof` or `audit`) ---------
# model/tests_slow_*.v run the same known-answer tests as their ordinary
# counterparts but at a scale (full ecmult/ecmult_gen table geometry) that
# costs 10 TO 50 MINUTES EACH under vm_compute -- far too slow to sit in
# `_RocqProject`, so they are excluded from it (audit/check.sh gate 0 exempts
# them the same way it exempts audit/assumptions.v) and only ever built here,
# one at a time, on request. Depends on `proof` so every dependency's .vo is
# current; reuses ROCQ_FLAGS so the load-path flags never drift from
# _RocqProject.
MODEL_SLOW_V := $(wildcard model/tests_slow_*.v)

model-tests: proof
	@for f in $(MODEL_SLOW_V); do \
	  echo "compiling $$f (10-50 min) ..."; \
	  rocq compile $(ROCQ_FLAGS) $$f || exit 1; \
	done

clean:
	@if [ -e Makefile.rocq ]; then $(MAKE) --no-print-directory -f Makefile.rocq cleanall 2>/dev/null; fi
	@rm -f Makefile.rocq Makefile.rocq.conf $(SOURCES_V)
