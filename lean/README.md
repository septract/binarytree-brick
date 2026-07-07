# Lean 4 red-black tree formalization

A standalone Lean 4 development of red-black trees. Its purpose in this
repository is to design and validate the functional specification *before*
porting it to Rocq: [`Rbtree/Daedalus.lean`](Rbtree/Daedalus.lean) is the
direct ancestor of [`../coq/RBTree.v`](../coq/RBTree.v).

All proofs are complete — no `sorry`, `admit`, or `axiom` — and the library is
checked in CI (`.github/workflows/lean_action_ci.yml`).

## Build

```bash
cd lean
lake build          # build the library + `rbtree` executable
lake exe rbtree     # run the runtime test/demo harness (Main.lean)
```

No external dependencies (no Mathlib) — core Lean 4 / `Std` only.

## Module map

The **core** modules model the Daedalus C++ (`cpp/ddl/map.h`):

| Module | Role |
|---|---|
| `Rbtree/Daedalus.lean` | Key-value map mirroring the C++: split `setRebalanceLeft`/`setRebalanceRight`, `ins` with value-update, `findNode`, `valid`. **The model that maps to the C++.** |
| `Rbtree/Daedalus/Proofs.lean` | Main artifact: split-rebalance = unified `balance`, BST preservation, `NoRedRed` preservation, and key-set agreement with the Classic reference. |
| `Rbtree/Defs.lean` | Abstract `Impl` / `ImplWithDelete` typeclass interfaces. |
| `Rbtree/Classic.lean` + `Classic/Proofs.lean` | Okasaki 2-color set tree with unified `balance`. Used by the Daedalus proofs as the **reference implementation** for the key-set cross-check, so it is load-bearing. |

The remaining modules are **companion experiments**, not required to verify the
C++ (the Daedalus code has no deletion):

| Module | Role |
|---|---|
| `Rbtree/DoubleBlack.lean` + `DoubleBlack/Proofs.lean` | 4-color functional *deletion* (Matt Might's double-black scheme), with BST proofs through the delete path. |
| `Rbtree/Equiv.lean` | `embed`/`project` between Classic and DoubleBlack, proving they agree on `toList`/`contains`/`size`/`fromList`. |

`Main.lean` is a runtime test harness: it builds trees with each
implementation, pretty-prints them, and asserts membership, ordering, deletion,
and cross-implementation agreement.
