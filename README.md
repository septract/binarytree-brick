# binarytree-brick

Formal verification of a C++ red-black tree using
[BRiCk](https://github.com/SkyLabsAI/BRiCk) — a separation-logic
framework for C++ built on Iris in the Rocq Prover (Coq) — together with a
companion functional model and proofs in Lean 4.

The C++ under verification is the red-black tree map from
[Daedalus](https://github.com/GaloisInc/daedalus) (`rts-c/ddl/map.h`), a
reference-counted `Map<K,V>`. The goal is an end-to-end refinement proof: the
C++ implementation refines a pure functional specification that itself is
proved to preserve the red-black invariants.

> **Status: work in progress.** The functional specification and the `findNode`
> refinement proof are complete and machine-checked. The `insert` path is
> partially proved with remaining `admit`s. See
> [Proof status](#proof-status) below.

## Repository layout

```
.
├── README.md
├── LICENSE                     # BSD 3-Clause
├── NOTICE                      # third-party provenance (Daedalus, BRiCk)
├── Makefile                    # cpp2v + Rocq proof build
├── coq/                        # Rocq (Coq) separation-logic proofs
│   ├── _CoqProject
│   ├── RBTree.v                #   Functional spec (ported from lean/Rbtree/Daedalus.lean)
│   ├── TreeRep.v               #   Separation-logic representation predicate (treeR)
│   ├── WpTactics.v             #   Generic weakest-precondition tactic library
│   ├── Tactics.v               #   Tree-specific tactics + lemmas
│   ├── FindSpec.v              #   findNode refinement proof (complete)
│   ├── InsertDefs.v            #   AST function extractions + specs (cached layer)
│   ├── InsertSpec.v            #   insert refinement proof
│   ├── RebalanceSpec.v         #   setRebalanceLeft/Right proofs (WIP)
│   ├── InsSpec.v               #   ins proof via Löb induction (WIP)
│   ├── RefCount.v              #   reference-counting correctness (ghost state)
│   └── Invariants.v            #   end-to-end glue proofs
├── cpp/                        # The C++ under verification
│   ├── ddl/                    #   Unmodified Daedalus headers (see NOTICE)
│   │   ├── map.h               #     the code under verification
│   │   └── boxed.h  size.h  maybe.h  debug.h
│   └── src/
│       └── map_int_int.cpp     #   monomorphized Map<int,int> driver for cpp2v
├── lean/                       # Lean 4 functional model + invariant proofs
│   ├── lakefile.toml
│   └── Rbtree/                 #   Classic, DoubleBlack, and Daedalus variants + Equiv
├── docs/                       # design notes
│   ├── 2026-02-12_formal_verification_daedalus_rbt.md   # verification-approach survey
│   ├── brick-framework-gaps.v  #   two BRiCk framework gaps (not built)
│   └── notes/                  #   historical development notes
└── .claude/skills/brick/       # Claude Code skill for writing BRiCk wp proofs
```

## The two halves

### Lean model (`lean/`)

A standalone Lean 4 development of red-black trees, used to design and validate
the functional specification before porting it to Rocq. It contains three
insertion/deletion variants — `Classic`, `DoubleBlack`, and `Daedalus` (matching
the C++) — with BST and no-red-red invariant proofs, plus `Equiv.lean` proving
the variants agree. `Rbtree/Daedalus.lean` is the direct ancestor of `coq/RBTree.v`.

Build:

```bash
cd lean
lake build
```

### BRiCk / Rocq proofs (`coq/`)

The refinement proof proper. It follows a standard strategy:

1. **Functional spec** (`RBTree.v`) — pure Rocq definitions mirroring
   `lean/Rbtree/Daedalus.lean`: `ins`, `insert`, `findNode`, `IsBST`,
   `NoRedRed`, etc., with their invariant-preservation lemmas.
2. **Representation predicate** (`TreeRep.v`) — links the Rocq `tree` type to
   the C++ `Node` heap layout via BRiCk separation-logic assertions (`treeR`).
3. **Refinement proofs** (`FindSpec.v`, `InsertSpec.v`, `RebalanceSpec.v`,
   `InsSpec.v`, `RefCount.v`) — each C++ function is shown to refine its
   functional counterpart via a Hoare triple / weakest-precondition proof.
4. **Glue** (`Invariants.v`) — composes the refinement and functional-invariant
   proofs toward end-to-end correctness.

#### Why BRiCk (not CBMC)?

CBMC's hand-maintained C++ parser crashes on
`std::numeric_limits<size_t>::max()` in `cpp/ddl/size.h`. BRiCk instead consumes
Clang's fully-elaborated AST via `cpp2v`, so templates, `if constexpr`, and
standard-library types are all resolved before translation to Rocq.

## Building the Rocq proofs

> **Note.** A turnkey, reproducible build environment (pinned BRiCk + Rocq +
> Iris) is not yet checked in — this is the next planned step. The instructions
> below describe the current manual workflow against a locally built BRiCk
> workspace.

The proofs require a built [BRiCk](https://github.com/SkyLabsAI/BRiCk)
workspace providing `coqc` and the `cpp2v` binary. Only the *public*
components of BRiCk (`skylabs.lang.cpp`, `skylabs.iris.extra`) are used; no
proprietary packages are required. The `Makefile` expects the workspace under
`.brick-workspace/` (gitignored), built via the public
[SkyLabsAI/workspace](https://github.com/SkyLabsAI/workspace) meta-repo:

```bash
# 1. Build the BRiCk workspace (public repos only), then activate it.
#    See https://github.com/SkyLabsAI/workspace for current instructions.
source .brick-workspace/dev/activate.sh

# 2. Generate the Rocq deep embedding of the C++ AST from cpp2v (~96K lines).
make cpp2v

# 3. Compile the generated AST (slow: ~30–60 min).
make ast

# 4. Build the hand-written proofs.
make proofs

# Check toolchain + proof status at any point:
make status
```

The generated files (`coq/map_int_int_cpp.v`, `coq/map_int_int_cpp_names.v`)
are gitignored, as are all Rocq build artifacts.

## Proof status

| Component | File | Status |
|---|---|---|
| Functional RB-tree spec + invariants | `coq/RBTree.v` | ✅ Complete — 41 `Qed`, 0 `admit` |
| Representation predicate | `coq/TreeRep.v` | ✅ Complete |
| Generic wp tactic library | `coq/WpTactics.v` | ✅ Usable (some helper lemmas admitted) |
| `findNode` refinement | `coq/FindSpec.v` | ✅ Complete — 0 `admit` |
| `insert` top-level refinement | `coq/InsertSpec.v` | 🟡 `insert_ok` proved modulo admitted callees |
| `setRebalanceLeft/Right` | `coq/RebalanceSpec.v` | 🟠 WIP — contains `admit`s |
| `ins` (Löb induction) | `coq/InsSpec.v` | 🟠 WIP — contains `admit`s |
| Reference counting | `coq/RefCount.v` | 🔲 Scaffolded (ghost state, Phase 6) |
| End-to-end glue | `coq/Invariants.v` | 🔲 Scaffolded |

The Lean development (`lean/`) is fully proved and CI-checked.

See [`docs/notes/`](docs/notes/) for the detailed phase breakdown and the
historical development notes.

## License

BSD 3-Clause (see [LICENSE](LICENSE)). The `ddl/` headers are copied from
Daedalus (also BSD 3-Clause); see [NOTICE](NOTICE) for third-party provenance.
