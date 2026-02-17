# BRiCk verification of Daedalus RB tree (ddl/map.h).
#
# Targets:
#   make proofs      - Build all Coq proofs (requires AST to be compiled first)
#   make ast         - Compile the cpp2v-generated AST (~30-60 min, 96K lines)
#   make cpp2v       - Run cpp2v to generate Coq AST from C++
#   make status      - Check toolchain installation status
#   make clean       - Remove generated files
#   make all         - cpp2v + ast + proofs
#
# Prerequisites:
#   The BRiCk workspace must be built first:
#     cd .brick-workspace && make clone-public -j && make dev-setup
#     make update-opam-deps && dune build
#
#   Then activate before running this Makefile:
#     source .brick-workspace/dev/activate.sh

# ---- Workspace paths ----

WORKSPACE := .brick-workspace
WS_BUILD  := $(WORKSPACE)/_build/install/default

# coqc from the workspace dune build
COQC      := $(WS_BUILD)/bin/coqc
COQLIB    := $(WS_BUILD)/lib/coq
COQDEP    := $(WS_BUILD)/bin/coqdep

# cpp2v from the workspace dune build
CPP2V     := $(WS_BUILD)/bin/cpp2v

# ---- Project files ----

SRC       := src/map_int_int.cpp
COQ_DIR   := coq
GEN_AST   := $(COQ_DIR)/map_int_int_cpp.v
GEN_NAMES := $(COQ_DIR)/map_int_int_cpp_names.v

# Coq source files (order matters for dependency chain)
# Note: FindSpec_draft.v is a prototype with a hand-transcribed AST (not built).
# FindSpec.v extracts the function from source's symbol table (the correct way).
COQ_SRCS := $(COQ_DIR)/WpTactics.v \
            $(COQ_DIR)/RBTree.v \
            $(COQ_DIR)/TreeRep.v \
            $(COQ_DIR)/Tactics.v \
            $(COQ_DIR)/FindSpec.v \
            $(COQ_DIR)/InsertSpec.v \
            $(COQ_DIR)/RefCount.v \
            $(COQ_DIR)/Invariants.v

# Common flags: set COQLIB and the -R mapping for our project
COQFLAGS := -coqlib $(COQLIB) -R $(COQ_DIR) daedalus_rb

.PHONY: all proofs ast cpp2v clean status

all: cpp2v ast proofs

# ---- cpp2v translation ----

# Run cpp2v to generate the Coq deep embedding of the C++ AST.
cpp2v: $(GEN_AST)

$(GEN_AST): $(SRC) ddl/map.h ddl/boxed.h ddl/size.h ddl/maybe.h ddl/debug.h
	$(CPP2V) -v \
	  -names $(GEN_NAMES) \
	  -o $(GEN_AST) \
	  $(SRC) -- -std=c++17 -I.

# ---- Coq proofs ----

# Build all .vo files. Dependencies are listed explicitly so Make
# can parallelise correctly.

# Generated files have no inter-dependency (compiled independently).
$(COQ_DIR)/map_int_int_cpp_names.vo: $(COQ_DIR)/map_int_int_cpp_names.v
	$(COQC) $(COQFLAGS) $<

$(COQ_DIR)/map_int_int_cpp.vo: $(COQ_DIR)/map_int_int_cpp.v $(COQ_DIR)/map_int_int_cpp_names.vo
	$(COQC) $(COQFLAGS) $<

# Compile the generated AST separately (slow: ~30-60 min for 96K lines).
# This is a prerequisite for FindSpec.vo and later proof files that
# reference the C++ function definitions.
ast: $(COQ_DIR)/map_int_int_cpp.vo

# Generic wp tactics (no tree dependencies).
$(COQ_DIR)/WpTactics.vo: $(COQ_DIR)/WpTactics.v
	$(COQC) $(COQFLAGS) $<

# Hand-written proof files.
$(COQ_DIR)/RBTree.vo: $(COQ_DIR)/RBTree.v
	$(COQC) $(COQFLAGS) $<

$(COQ_DIR)/TreeRep.vo: $(COQ_DIR)/TreeRep.v $(COQ_DIR)/RBTree.vo
	$(COQC) $(COQFLAGS) $<

# Tree-specific tactics + lemmas (depends on generic WpTactics).
$(COQ_DIR)/Tactics.vo: $(COQ_DIR)/Tactics.v $(COQ_DIR)/RBTree.vo $(COQ_DIR)/TreeRep.vo $(COQ_DIR)/WpTactics.vo
	$(COQC) $(COQFLAGS) $<

# FindSpec extracts findNode from the generated AST's symbol table.
$(COQ_DIR)/FindSpec.vo: $(COQ_DIR)/FindSpec.v $(COQ_DIR)/RBTree.vo $(COQ_DIR)/TreeRep.vo $(COQ_DIR)/map_int_int_cpp.vo $(COQ_DIR)/Tactics.vo
	$(COQC) $(COQFLAGS) $<

$(COQ_DIR)/InsertSpec.vo: $(COQ_DIR)/InsertSpec.v $(COQ_DIR)/RBTree.vo $(COQ_DIR)/TreeRep.vo $(COQ_DIR)/Tactics.vo $(COQ_DIR)/map_int_int_cpp.vo
	$(COQC) $(COQFLAGS) $<

$(COQ_DIR)/RefCount.vo: $(COQ_DIR)/RefCount.v $(COQ_DIR)/RBTree.vo $(COQ_DIR)/TreeRep.vo $(COQ_DIR)/Tactics.vo
	$(COQC) $(COQFLAGS) $<

$(COQ_DIR)/Invariants.vo: $(COQ_DIR)/Invariants.v $(COQ_DIR)/RBTree.vo
	$(COQC) $(COQFLAGS) $<

proofs: $(COQ_DIR)/WpTactics.vo \
        $(COQ_DIR)/RBTree.vo $(COQ_DIR)/TreeRep.vo \
        $(COQ_DIR)/Tactics.vo $(COQ_DIR)/FindSpec.vo \
        $(COQ_DIR)/InsertSpec.vo \
        $(COQ_DIR)/RefCount.vo $(COQ_DIR)/Invariants.vo

# ---- Cleanup ----

clean:
	rm -f $(COQ_DIR)/*.vo $(COQ_DIR)/*.vok $(COQ_DIR)/*.vos $(COQ_DIR)/*.glob $(COQ_DIR)/.*.aux

# ---- Status ----

status:
	@echo "--- coqc ---"
	@if [ -x "$(COQC)" ]; then \
	  $(COQC) -coqlib $(COQLIB) --version; \
	else \
	  echo "NOT FOUND at $(COQC)"; \
	  echo "Build the workspace first: cd $(WORKSPACE) && dune build"; \
	fi
	@echo ""
	@echo "--- cpp2v ---"
	@if [ -x "$(CPP2V)" ]; then \
	  $(CPP2V) --version 2>&1 || echo "(version check not supported)"; \
	else \
	  echo "NOT FOUND at $(CPP2V)"; \
	fi
	@echo ""
	@echo "--- Generated AST ---"
	@if [ -f "$(GEN_AST)" ]; then \
	  echo "$(GEN_AST): $$(wc -l < $(GEN_AST)) lines"; \
	  echo "$(GEN_NAMES): $$(wc -l < $(GEN_NAMES)) lines"; \
	else \
	  echo "NOT GENERATED (run: make cpp2v)"; \
	fi
	@echo ""
	@echo "--- Proof status ---"
	@for f in $(COQ_SRCS); do \
	  vo=$${f%.v}.vo; \
	  if [ -f "$$vo" ]; then \
	    echo "  ✓ $$f"; \
	  else \
	    echo "  ✗ $$f (not compiled)"; \
	  fi; \
	done
