# BRiCk verification of Daedalus RB tree (ddl/map.h).
#
# Targets:
#   make setup       - Install Coq + Iris (opam) and build cpp2v from source
#   make setup-coq   - Just the opam switch (Coq + Iris + BRiCk theories)
#   make setup-cpp2v - Just the cpp2v binary (cmake + LLVM)
#   make cpp2v       - Run cpp2v to generate Coq AST from C++
#   make proofs      - Build all Coq proofs (requires generated .v files)
#   make clean       - Remove generated files
#   make all         - cpp2v + proofs
#
# Prerequisites:
#   opam (>= 2.1), Homebrew llvm (for cpp2v build), cmake
#
# First-time setup:
#   make setup    # ~20 min total

# Homebrew LLVM (cpp2v links against libclang)
LLVM_PREFIX := $(shell brew --prefix llvm 2>/dev/null)

# cpp2v source (cloned during setup)
CPP2V_REPO  := https://github.com/bedrocksystems/BRiCk.git
CPP2V_SRC   := .brick-src
CPP2V_BIN   := $(CPP2V_SRC)/rocq-skylabs-cpp2v/build/cpp2v

SRC       := src/map_int_int.cpp
COQ_DIR   := coq
GEN_AST   := $(COQ_DIR)/map_int_int_cpp.v
GEN_NAMES := $(COQ_DIR)/map_int_int_cpp_names.v

# Coq source files (hand-written)
COQ_SRCS := $(COQ_DIR)/RBTree.v \
            $(COQ_DIR)/TreeRep.v \
            $(COQ_DIR)/FindSpec.v \
            $(COQ_DIR)/InsertSpec.v \
            $(COQ_DIR)/RefCount.v \
            $(COQ_DIR)/Invariants.v

.PHONY: all setup setup-coq setup-cpp2v cpp2v proofs clean check-env

all: cpp2v proofs

# ---- Environment check ----

check-env:
	@command -v opam >/dev/null 2>&1 || (echo "ERROR: opam not found. Install with: brew install opam" && exit 1)
	@test -n "$(LLVM_PREFIX)" || (echo "ERROR: Homebrew llvm not found. Install with: brew install llvm" && exit 1)
	@command -v cmake >/dev/null 2>&1 || (echo "ERROR: cmake not found. Install with: brew install cmake" && exit 1)
	@echo "opam:  $$(opam --version)"
	@echo "llvm:  $(LLVM_PREFIX)"
	@echo "cmake: $$(cmake --version | head -1)"

# ---- Setup ----

setup: setup-cpp2v setup-coq
	@echo ""
	@echo "=== Setup complete ==="
	@echo "cpp2v: $(CPP2V_BIN)"
	@echo "Coq:   eval \$$(opam env --switch=brick) && coqc --version"

# Step 1: Build cpp2v from source via cmake.
# cpp2v is a C++ binary that links against LLVM/Clang.
# We build it directly rather than going through opam/dune because
# the BRiCk monorepo's dune build has complex cross-package deps.
setup-cpp2v: check-env
	@if [ -x "$(CPP2V_BIN)" ]; then \
	  echo "cpp2v already built at $(CPP2V_BIN)"; \
	else \
	  echo "=== Cloning BRiCk repo ===" && \
	  git clone --depth 1 $(CPP2V_REPO) $(CPP2V_SRC) && \
	  echo "=== Building cpp2v ===" && \
	  cd $(CPP2V_SRC)/rocq-skylabs-cpp2v && \
	  cmake -B build \
	    -DCMAKE_BUILD_TYPE=Release \
	    -DCMAKE_PREFIX_PATH="$(LLVM_PREFIX)" \
	    -DClang_DIR="$(LLVM_PREFIX)/lib/cmake/clang" \
	    -DLLVM_DIR="$(LLVM_PREFIX)/lib/cmake/llvm" && \
	  make -C build -j$$(sysctl -n hw.ncpu) cpp2v && \
	  echo "cpp2v built: $$(pwd)/build/cpp2v"; \
	fi

# Step 2: Create opam switch with Coq, Iris, and BRiCk Coq theories.
# The 'brick' switch already exists from the failed attempt; reuse it.
setup-coq: check-env
	opam switch create brick 5.1.1 2>/dev/null || true
	eval $$(opam env --switch=brick) && \
	opam repo add --dont-select coq-released https://coq.inria.fr/opam/released 2>/dev/null || true && \
	opam repo add --dont-select iris-dev https://gitlab.mpi-sws.org/iris/opam.git 2>/dev/null || true && \
	opam repo add --this-switch coq-released 2>/dev/null || true && \
	opam repo add --this-switch iris-dev 2>/dev/null || true && \
	opam install coq coq-iris --yes
	@echo ""
	@echo "Coq switch ready. Activate with: eval \$$(opam env --switch=brick)"

# ---- cpp2v translation ----

# Run cpp2v to generate the Coq deep embedding of the C++ AST.
cpp2v: $(GEN_AST)

$(GEN_AST): $(SRC) ddl/map.h ddl/boxed.h ddl/size.h ddl/maybe.h ddl/debug.h
	$(CPP2V_BIN) -v \
	  -names $(GEN_NAMES) \
	  -o $(GEN_AST) \
	  $(SRC) -- -std=c++17 -I.

# ---- Coq proofs ----

# Build all Coq files using the _CoqProject file.
# Requires the generated AST files to exist first.
proofs: $(GEN_AST)
	eval $$(opam env --switch=brick) && \
	cd $(COQ_DIR) && coq_makefile -f _CoqProject -o Makefile.coq && \
	$(MAKE) -f Makefile.coq

# ---- Cleanup ----

clean:
	rm -f $(GEN_AST) $(GEN_NAMES)
	rm -f $(COQ_DIR)/Makefile.coq $(COQ_DIR)/Makefile.coq.conf $(COQ_DIR)/.Makefile.coq.d
	rm -f $(COQ_DIR)/*.vo $(COQ_DIR)/*.vok $(COQ_DIR)/*.vos $(COQ_DIR)/*.glob $(COQ_DIR)/.*.aux

clean-all: clean
	rm -rf $(CPP2V_SRC)
