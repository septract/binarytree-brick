# BRiCk verification of Daedalus RB tree (cpp/ddl/map.h).
#
# Targets:
#   make proofs      - Build all Coq proofs (requires AST to be compiled first)
#   make ast         - Compile the cpp2v-generated AST (~30-60 min, 96K lines)
#   make cpp2v       - Run cpp2v to generate Coq AST from C++
#   make status      - Check toolchain installation status
#   make clean       - Remove generated files
#   make all         - cpp2v + ast + proofs
#   make setup       - Clone + build the pinned BRiCk workspace (~30-60 min)
#   make check       - Preflight host-tool version checks only
#
# Prerequisites (see BUILDING.md for the full guide):
#   The BRiCk toolchain (Rocq + cpp2v) must be built first. The easiest path:
#     make setup       # clones .brick-workspace/ at pinned commits and builds
#
#   Then activate before running the proof targets (in each new shell):
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

SRC       := cpp/src/map_int_int.cpp
DDL_DIR   := cpp/ddl
COQ_DIR   := coq
GEN_AST   := $(COQ_DIR)/map_int_int_cpp.v
GEN_NAMES := $(COQ_DIR)/map_int_int_cpp_names.v

# Coq source files (order matters for dependency chain).
# FindSpec.v extracts the function from the cpp2v symbol table (the correct way).
COQ_SRCS := $(COQ_DIR)/WpTactics.v \
            $(COQ_DIR)/RBTree.v \
            $(COQ_DIR)/TreeRep.v \
            $(COQ_DIR)/Tactics.v \
            $(COQ_DIR)/FindSpec.v \
            $(COQ_DIR)/InsertDefs.v \
            $(COQ_DIR)/InsertSpec.v \
            $(COQ_DIR)/RebalanceSpec.v \
            $(COQ_DIR)/InsSpec.v \
            $(COQ_DIR)/RefCount.v \
            $(COQ_DIR)/Invariants.v

# Common flags: set COQLIB and the -R mapping for our project
COQFLAGS := -coqlib $(COQLIB) -R $(COQ_DIR) daedalus_rb

.PHONY: all setup check proofs ast cpp2v clean status

all: cpp2v ast proofs

# ---- Toolchain setup ----

# Clone + build the pinned BRiCk workspace under .brick-workspace/.
# First run takes ~30-60 min (builds Rocq from source). See BUILDING.md.
setup:
	scripts/setup-brick-workspace.sh

# Preflight: check host tools without cloning or building anything.
check:
	scripts/setup-brick-workspace.sh --check

# ---- cpp2v translation ----

# Run cpp2v to generate the Coq deep embedding of the C++ AST.
cpp2v: $(GEN_AST)

$(GEN_AST): $(SRC) $(DDL_DIR)/map.h $(DDL_DIR)/boxed.h $(DDL_DIR)/size.h $(DDL_DIR)/maybe.h $(DDL_DIR)/debug.h
	$(CPP2V) -v \
	  -names $(GEN_NAMES) \
	  -o $(GEN_AST) \
	  $(SRC) -- -std=c++17 -Icpp

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

# InsertDefs pre-computes function extractions from the AST (one-time ~5-10 min).
# InsertSpec imports InsertDefs.vo (cached), avoiding per-rebuild AST traversal.
$(COQ_DIR)/InsertDefs.vo: $(COQ_DIR)/InsertDefs.v $(COQ_DIR)/RBTree.vo $(COQ_DIR)/TreeRep.vo $(COQ_DIR)/map_int_int_cpp.vo
	$(COQC) $(COQFLAGS) $<

$(COQ_DIR)/InsertSpec.vo: $(COQ_DIR)/InsertSpec.v $(COQ_DIR)/RBTree.vo $(COQ_DIR)/TreeRep.vo $(COQ_DIR)/Tactics.vo $(COQ_DIR)/InsertDefs.vo
	$(COQC) $(COQFLAGS) $<

# Phase 5B: setRebalanceLeft_ok + setRebalanceRight_ok
$(COQ_DIR)/RebalanceSpec.vo: $(COQ_DIR)/RebalanceSpec.v $(COQ_DIR)/InsertDefs.vo $(COQ_DIR)/Tactics.vo
	$(COQC) $(COQFLAGS) $<

# Phase 5B: ins_ok (Löb induction, depends on rebalance specs)
$(COQ_DIR)/InsSpec.vo: $(COQ_DIR)/InsSpec.v $(COQ_DIR)/InsertDefs.vo $(COQ_DIR)/Tactics.vo
	$(COQC) $(COQFLAGS) $<

$(COQ_DIR)/RefCount.vo: $(COQ_DIR)/RefCount.v $(COQ_DIR)/RBTree.vo $(COQ_DIR)/TreeRep.vo $(COQ_DIR)/Tactics.vo
	$(COQC) $(COQFLAGS) $<

$(COQ_DIR)/Invariants.vo: $(COQ_DIR)/Invariants.v $(COQ_DIR)/RBTree.vo
	$(COQC) $(COQFLAGS) $<

proofs: $(COQ_DIR)/WpTactics.vo \
        $(COQ_DIR)/RBTree.vo $(COQ_DIR)/TreeRep.vo \
        $(COQ_DIR)/Tactics.vo $(COQ_DIR)/FindSpec.vo \
        $(COQ_DIR)/InsertDefs.vo $(COQ_DIR)/InsertSpec.vo \
        $(COQ_DIR)/RebalanceSpec.vo $(COQ_DIR)/InsSpec.vo \
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
	  echo "Build the toolchain first: make setup   (see BUILDING.md)"; \
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
