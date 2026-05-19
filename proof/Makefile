# Formal verification build for secp256k1 (Rocq + VST + CompCert).
#
#   make extract : clightgen extraction.c into clight/extraction.v.  One unit
#                  #includes the library's real headers (scalar, int128,
#                  modinv64) so the whole proof tree shares one AST.
#   make proof   : build the Rocq proofs against that AST.
#
# Run inside the dev shell from the repo-root flake (`nix develop` or direnv).

NPROC := $(shell nproc)

EXTRACT_SRC := extraction.c
# Re-extract when the unit OR any library header it #includes changes: clightgen
# inlines those headers, so a header edit must invalidate the AST.  The wildcard
# is a safe superset of the actually-included headers.
EXTRACT_DEPS := $(EXTRACT_SRC) $(wildcard ../src/*.h ../include/*.h)
SOURCE_V    := clight/extraction.v

SOURCES_V := $(SOURCE_V)

# Pure-C, struct-based 128-bit arithmetic (CompCert has no __int128), no asm.
FV_DEFINES      := -DUSE_FORCE_WIDEMUL_INT128_STRUCT=1

# modinv's ctz64_var uses __builtin_ctzll, which clightgen cannot translate;
# -U__has_builtin forces util.h to fall back to the De Bruijn software path.
# Compiled VERIFY-off (no -DVERIFY): the VERIFY_CHECK assertions and the
# verify-only helpers (abs/mul_62/mul_cmp_62/det_check_pow2) are absent from the
# AST, so the proofs reason about exactly the production (VERIFY-off) build.
CLIGHTGEN_FLAGS := -normalize -I../include -I../src -Wp,-w -U__has_builtin

.PHONY: all extract proof clean

all: proof

extract: $(SOURCES_V)

$(SOURCE_V): $(EXTRACT_DEPS)
	@mkdir -p $(@D)
	clightgen $(CLIGHTGEN_FLAGS) $(FV_DEFINES) -o $@ $(EXTRACT_SRC)

proof: Makefile.rocq $(SOURCES_V)
	@$(MAKE) -j $(NPROC) --no-print-directory -f Makefile.rocq
	@printf '\033[1;34m\xE2\x9C\x93 All verifications succeeded\033[0m\n'

Makefile.rocq: _RocqProject
	@rocq makefile -f _RocqProject -o Makefile.rocq

clean:
	@if [ -e Makefile.rocq ]; then $(MAKE) --no-print-directory -f Makefile.rocq cleanall 2>/dev/null; fi
	@rm -f Makefile.rocq Makefile.rocq.conf $(SOURCES_V)
