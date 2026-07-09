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

> ⚠️ **Health warning — built with AI + human oversight.** This repository
> (proofs, tactics, models, and docs) was developed by a human working with AI
> coding assistants. Everything that is claimed complete is *machine-checked* by
> Rocq/Lean — that is the guarantee you should rely on, not the prose. But the
> specifications, the `Admitted`/trusted-base claims, and the surrounding
> documentation have had human review of varying depth and may contain mistakes
> or over-claims. Read the theorem statements and the trusted base yourself
> before depending on any result.

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
│   ├── IsBlackSpec.v           #   is_black / is_red leaf-callee proofs (complete)
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

Build (needs only [`elan`](https://github.com/leanprover/elan)):

```bash
cd lean && lake build
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

## Building

See **[BUILDING.md](BUILDING.md)** for the full guide. In short:

```bash
# Lean (fast, self-contained):
cd lean && lake build

# Rocq proofs (builds BRiCk from source; ~30-60 min first run):
make check      # preflight: check host tools
make setup      # clone + build the pinned BRiCk toolchain into .brick-workspace/
source .brick-workspace/dev/activate.sh
make cpp2v && make ast && make proofs
make status     # toolchain + per-file proof status
```

Only the *public* components of BRiCk (`skylabs.lang.cpp`, `skylabs.iris.extra`)
are used; no proprietary packages are required. The exact toolchain commits are
pinned in [`scripts/pins.env`](scripts/pins.env). The `cpp2v`-generated files
(`coq/map_int_int_cpp.v`, `coq/map_int_int_cpp_names.v`) and all build artifacts
are gitignored.

## Proof status

| Component | File | Status |
|---|---|---|
| Functional RB-tree spec + invariants | `coq/RBTree.v` | ✅ Complete — 41 `Qed`, 0 `admit` |
| Representation predicate | `coq/TreeRep.v` | ✅ Complete |
| Generic wp tactic library | `coq/WpTactics.v` | ✅ Complete (rests on the one `align_of_function` axiom; no admits) |
| `findNode` refinement (full: returns node holding the key/value) | `coq/FindSpec.v` | ✅ Complete — 0 `admit` |
| `insert` top-level refinement | `coq/InsertSpec.v` | 🟡 `insert_ok` proved modulo admitted callees |
| `is_black` / `is_red` refinement | `coq/IsBlackSpec.v` | ✅ Complete — both `Qed`, 0 `admit` |
| `setRebalanceLeft/Right` | `coq/RebalanceSpec.v` | 🟠 WIP — contains `admit`s |
| `ins` (Löb induction) | `coq/InsSpec.v` | 🟠 WIP — contains `admit`s |
| Reference counting | `coq/RefCount.v` | 🔲 Scaffolded (ghost state, Phase 6) |
| End-to-end glue | `coq/Invariants.v` | 🔲 Scaffolded |

The Lean development (`lean/`) is fully proved (no `sorry`/`admit`).

**Trusted base.** Beyond BRiCk's own axiom base, the write-path proofs now rest
on a single, documented, **proven-sound** axiom for the first BRiCk framework
gap:

- **Function-pointer alignment** — `align_of (Tfunction ft) = Some 1`
  (`coq/WpTactics.v`, `align_of_function`). C++ leaves function-type alignment
  undefined, so BRiCk has no axiom for it; this is BRiCk's own proposed fix and
  is sound (`size_of (Tfunction) = None` makes the size/alignment axiom vacuous;
  `aligned_ptr 1 p` holds for every `p`). With it, `wp_operand_cfun2ptr_global`
  — the direct-call callee step — is **fully proved** (was previously
  `Admitted`), which unblocks the `insert` write path.

The second gap — **static initialization** (BRiCk cannot yet model the value of
a statically-initialized global const, e.g. `Node::black`/`red`) — has been
**eliminated at the source** rather than trusted: those trivial constants are
inlined to `false`/`true` literals in `cpp/ddl/map.h` (a marked, reversible,
behaviour-preserving change; see [`NOTICE`](NOTICE)), so no global-const read is
generated and no axiom is needed. `findNode_ok` depends on neither gap.

So the entire trusted base beyond BRiCk itself is the one `align_of_function`
axiom above. Background:
[`docs/brick-framework-gaps.v`](docs/brick-framework-gaps.v) and
[`docs/2026-07-07_brick_gaps_upstream_review.md`](docs/2026-07-07_brick_gaps_upstream_review.md).

## What is actually connected to the C++

The proofs are about the **real compiled code**, not a re-transcription: every
function is extracted from the `cpp2v`-generated AST of `cpp/ddl/map.h` (via
`source.(symbols) !! …`), and the extraction is machine-checked by
`native_compute` (e.g. `findNode_lookup`). Each `func_ok source f spec` states
that the extracted body `f`, executed under BRiCk's C++ operational semantics,
satisfies `spec`. The `treeR` field layout matches the struct (`ref_count :
size_t → ulongR`, `color : bool → boolR`, `key/value : int → intR`,
`left/right → ptrR`). There are **no `Axiom`s** in the proof files.

One honest limit on that connection today:

- **Results are conditional on module well-formedness.** Every theorem is
  proved under a section hypothesis that the driver translation unit is
  well-formed (`map_int_int_cpp.source ⊧ σ`, and for the insert path
  `|-- denoteModule source`). These are standard, dischargeable BRiCk side
  conditions, but nothing in the repo discharges them yet — so the theorems
  currently read "*if* the module is well-formed, *then* the C++ refines its
  spec." Closing this is part of the Phase G capstone.

`findNode_spec` is now a *full* functional guarantee: on a hit it returns a
pointer to a node that genuinely holds the searched key and the computed value
(as a borrow with a restore-wand), and on a miss it returns `nullptr` — not
merely a non-null/null flag. (`ins_spec` / `insert_spec` likewise pin down the
entire resulting tree, values included.)

## Roadmap

The path to a complete proof of the C++ tree is tracked in [`TODO.md`](TODO.md),
with the full rationale, soundness review, and dependency graph in
[`docs/2026-07-07_technical_review_and_roadmap.md`](docs/2026-07-07_technical_review_and_roadmap.md).
See also [`docs/notes/`](docs/notes/) for historical development notes.

## License

BSD 3-Clause (see [LICENSE](LICENSE)). The `ddl/` headers are copied from
Daedalus (also BSD 3-Clause); see [NOTICE](NOTICE) for third-party provenance.
