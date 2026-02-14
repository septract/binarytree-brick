# BRiCk Verification of Daedalus Red-Black Tree

Formal verification of the Daedalus C++ red-black tree (`ddl/map.h`) using
[BRiCk](https://github.com/bedrocksystems/BRiCk) — a separation logic
framework for C++ built on the Iris framework in Coq.

## Why BRiCk?

CBMC (bounded model checker) cannot parse the Daedalus headers because its
hand-maintained C++ parser crashes on `std::numeric_limits<size_t>::max()` in
`ddl/size.h`. BRiCk avoids this entirely: it uses Clang's fully-elaborated AST,
so templates, `if constexpr`, and standard library types are all resolved before
translation to Coq.

## Prerequisites

Install via Homebrew:

```bash
brew install opam llvm cmake
```

- **opam** >= 2.1 — OCaml package manager (manages Coq and Iris)
- **llvm** — cpp2v links against libclang (Apple Clang doesn't ship the dev headers)
- **cmake** — builds cpp2v from source

## Setup

From this directory:

```bash
make setup       # ~20 min: builds cpp2v + installs Coq/Iris
```

This does two things (which can also be run independently):

1. **`make setup-cpp2v`** — Clones the BRiCk repo, builds the `cpp2v` binary
   via cmake, linking against Homebrew LLVM. The binary lands at
   `.brick-src/rocq-skylabs-cpp2v/build/cpp2v`.

2. **`make setup-coq`** — Creates an opam switch called `brick` with OCaml
   5.1.1, then installs the Rocq Prover (Coq) 9.1 and Iris.

Verify everything is working:

```bash
make status
```

## Usage

### Generate the Coq deep embedding

```bash
make cpp2v
```

Runs `cpp2v` on `src/map_int_int.cpp` (a monomorphized `Map<int,int>` driver)
and produces two files in `coq/`:

- `map_int_int_cpp.v` — Deep embedding of the C++ AST (~96K lines)
- `map_int_int_cpp_names.v` — Symbol table for mangled C++ names (~3K lines)

These are gitignored since they're generated.

### Build the Coq proofs

```bash
eval $(opam env --switch=brick)
make proofs
```

Compiles all `.v` files in `coq/` using `coq_makefile`. Requires the generated
AST files to exist (run `make cpp2v` first).

### Clean

```bash
make clean       # Remove generated .v files and Coq build artifacts
make clean-all   # Also remove the cloned BRiCk source tree
```

## Directory Structure

```
brick/
├── README.md
├── Makefile                  # setup, cpp2v, proofs, status, clean
├── 2026-02-13_brick_verification_plan.md   # Detailed approach + phase tracker
├── ddl/                      # Unmodified Daedalus headers (copied from cbmc/ddl/)
│   ├── map.h                 #   The C++ code under verification
│   ├── boxed.h               #   Reference counting (HasRefs, Boxed<T>)
│   ├── size.h                #   Contains std::numeric_limits (the CBMC blocker)
│   ├── maybe.h               #   Optional type
│   └── debug.h               #   Debug macros (no-op at DEBUG_LEVEL=0)
├── src/
│   └── map_int_int.cpp       # Monomorphized driver for cpp2v
├── coq/
│   ├── _CoqProject           # Coq project file
│   ├── RBTree.v              # Functional spec (ported from Lean)
│   ├── TreeRep.v             # Separation logic representation predicate
│   ├── FindSpec.v            # FindNode specification + proof scaffold
│   ├── InsertSpec.v          # Insert/ins/rebalance specs
│   ├── RefCount.v            # Reference counting correctness
│   └── Invariants.v          # End-to-end glue proofs
└── .brick-src/               # (gitignored) Cloned BRiCk repo with built cpp2v
```

## Proof Architecture

The verification follows a refinement strategy:

1. **Functional spec** (`RBTree.v`): Pure Coq definitions mirroring the Lean
   formalization in `Rbtree/Daedalus.lean`. Defines `ins`, `insert`, `findNode`,
   `IsBST`, `NoRedRed`, etc.

2. **Representation predicate** (`TreeRep.v`): Links the Coq `tree` type to
   the C++ `Node` heap layout using BRiCk's separation logic assertions.

3. **Refinement proofs** (`FindSpec.v`, `InsertSpec.v`, `RefCount.v`): Each C++
   function is shown to refine its functional spec counterpart via Hoare triples.

4. **Glue** (`Invariants.v`): Composes refinement proofs with functional
   invariant proofs for end-to-end correctness.

## Current Status

- **Phase 1 (Infrastructure)**: Complete. cpp2v generates correct Coq output;
  all target functions and struct fields present in the AST.
- **Phase 2 (Functional Spec)**: Complete. All 35 lemmas/theorems in
  `coq/RBTree.v` are machine-checked (zero `Admitted`). Covers BST preservation,
  NoRedRed preservation, findNode correctness, and fromList invariants.
- **Phase 3-7 (Separation Logic Proofs)**: Scaffolded with `Admitted` placeholders.

See `2026-02-13_brick_verification_plan.md` for the full phase breakdown.
