# Formal verification with Rocq, VST, and CompCert. See README.md for targets.

NPROC := $(shell nproc)

# Large Clight table initializers need a larger native stack.
ROCQ_STACK := ulimit -s 262144 &&

EXTRACT_SRCS := extraction.c
LIBRARY_SOURCES := ../src/secp256k1.c ../src/precomputed_ecmult.c ../src/precomputed_ecmult_gen.c
SOURCES_V := $(patsubst %.c,clight/%.v,$(EXTRACT_SRCS))

# clightgen inlines headers, so header changes must regenerate the AST.
HEADER_DEPS := $(wildcard ../src/*.h ../src/modules/*/*.h ../include/*.h)

# CompCert requires the struct-based 128-bit backend. VERIFY stays disabled.
FV_DEFINES := -DUSE_FORCE_WIDEMUL_INT128_STRUCT=1

# Disable the ctz builtin so util.h selects its software implementation.
CLIGHTGEN_FLAGS := -normalize -I../include -I../src -Wp,-w -U__has_builtin

PROOF_FILES := $(shell grep -E '^[^#[:space:]]+\.v$$' _RocqProject)
PROOF_MODULES := $(addprefix secp256k1.,$(subst /,.,$(PROOF_FILES:.v=)))

VERIF_V := $(shell grep -E '^vst/[a-z0-9_]+/verif/' _RocqProject)
SUBS    := int128 util scalar field modinv

# Indirection keeps these sub-builds from executing during make dry runs.
SUBMAKE = $(MAKE)

# Timing is on by default so every run leaves data behind: TIMED prints one
# real/user/sys/mem line per file, TIMING writes per-command times to
# <file>.v.timing. Pass TIMED= or TIMING= to switch either off.
TIMED ?= 1
TIMING ?= 1
ROCQ_TIMING := TIMED=$(TIMED) TIMING=$(TIMING)

# verif-% must remain a pattern rule. Explicit phony entries override it.
.DELETE_ON_ERROR:
.PHONY: all extract proof specification html clean purge axioms vectors

all: proof

extract: $(SOURCES_V)

clight/%.v: %.c $(LIBRARY_SOURCES) $(HEADER_DEPS) Makefile
	@mkdir -p $(@D)
	clightgen $(CLIGHTGEN_FLAGS) $(FV_DEFINES) -o $@ $<

proof: Makefile.rocq $(SOURCES_V)
	@$(ROCQ_STACK) $(MAKE) -j $(NPROC) --no-print-directory -f Makefile.rocq $(ROCQ_TIMING)

Makefile.rocq: _RocqProject
	@rocq makefile -f _RocqProject -o Makefile.rocq

specification: Makefile.rocq $(SOURCES_V)
	@$(ROCQ_STACK) $(SUBMAKE) -j $(NPROC) --no-print-directory -f Makefile.rocq $(ROCQ_TIMING) specification.vo

html: specification doc/render.sh doc/style.css doc/header.html doc/footer.html doc/presentation.sed
	bash doc/render.sh

verif-%: Makefile.rocq $(SOURCES_V)
	@$(if $(strip $(filter vst/$*/verif/%,$(VERIF_V))),,$(error verif-$*: no files under vst/$*/verif/ in _RocqProject (known subsystems: $(SUBS))))
	@$(ROCQ_STACK) $(SUBMAKE) -j $(NPROC) --no-print-directory -f Makefile.rocq $(ROCQ_TIMING) \
	  $(patsubst %.v,%.vo,$(filter vst/$*/verif/%,$(VERIF_V)))

axioms: proof
	mkdir -p .axioms
	@printf 'Require %s.\n' $(PROOF_MODULES) > .axioms/All.v
	$(ROCQ_STACK) rocq compile -Q . secp256k1 -Q .axioms AxiomReport .axioms/All.v
	$(ROCQ_STACK) rocqchk -silent -o -Q . secp256k1 -Q .axioms AxiomReport -norec AxiomReport.All
	rm -rf .axioms

# Scalar multiplication makes these known-answer tests too slow for the default build.
ROCQ_FLAGS := $(shell grep -E '^(-Q|-R|-arg)' _RocqProject | sed -E 's/-arg +//g' | tr '\n' ' ')
VECTOR_V  := $(wildcard vectors/*.v)
VECTOR_VO := $(VECTOR_V:.v=.vo)

# The vectors bypass Makefile.rocq, so they mirror its TIMED/TIMING behaviour here.
VECTOR_TIMER  = $(if $(TIMED),command time -f '$@ (real: %e, user: %U, sys: %S, mem: %M ko)')
VECTOR_TIMING = $(if $(TIMING),-time-file $<.timing)

vectors: specification
	@$(ROCQ_STACK) $(SUBMAKE) -j $(NPROC) --no-print-directory $(VECTOR_VO)

vectors/%.vo: vectors/%.v specification.vo
	$(ROCQ_STACK) $(VECTOR_TIMER) rocq compile $(ROCQ_FLAGS) $(VECTOR_TIMING) $<

clean: _RocqProject
	find theory vst vectors -type f -name "*.vo" -delete
	find theory vst vectors -type f -name "*.vos" -delete
	find theory vst vectors -type f -name "*.vok" -delete
	find theory vst vectors -type f -name "*.glob" -delete
	find theory vst vectors -type f -name ".*.aux" -delete
	find theory vst vectors -type f -name "*.vo.prof.json" -delete
	find theory vst vectors -type f -name "*.vo.prof.json.gz" -delete
	find theory vst vectors clight -type f -name "*.v.*timing*" -delete
	rm -f *.vo *.vos *.vok *.glob .*.aux
	rm -f *.vo.prof.json *.vo.prof.json.gz
	rm -f *.v.*timing* time-of-build*.log pretty-timed-success.ok
	rm -f Makefile.rocq Makefile.rocq.conf .Makefile.rocq.d
	rm -rf html
	rm -rf .axioms

purge: clean
	rm -rf clight
	rm -f .lia.cache .nia.cache
