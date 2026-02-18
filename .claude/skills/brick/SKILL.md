---
name: brick
description: "BRiCk separation logic verification of C++ code using Coq/Rocq and Iris. Use when writing representation predicates (Rep), Hoare triple specs, wp proofs, or working with cpp2v-generated ASTs."
user-invokable: false
---

# BRiCk C++ Verification in Coq

[BRiCk](https://github.com/bedrocksystems/BRiCk) is a separation logic
framework for formally verifying C++ code. It uses **cpp2v** to translate
Clang's fully-elaborated AST into a Coq deep embedding, then proves
correctness via Hoare triples in the **Iris** framework.

**Sub-files:**
- [api-reference.md](api-reference.md) — Types, reps, specs, key lemmas, Iris tactics
- [wp-proof-guide.md](wp-proof-guide.md) — wp proof architecture, function extraction, call resolution, loops, local variables, ownership patterns

## Installation

BRiCk uses the [SkylabsAI/workspace](https://github.com/SkylabsAI/workspace)
meta-repo to manage all dependencies (Rocq, Iris, stdpp, cpp2v, etc.) with
correct version pinning. **Do not install dependencies manually via opam.**

```bash
git clone https://github.com/SkylabsAI/workspace.git .brick-workspace
cd .brick-workspace
make clone-public -j       # Clone BRiCk + public dependencies
make dev-setup             # Create opam switch with pinned versions
make update-opam-deps      # Install all dependencies
make -j$(nproc) stage1     # Build ASTs
dune build                 # Build everything (cpp2v + Coq theories)
```

To use cpp2v:
```bash
source .brick-workspace/dev/activate.sh
cpp2v -v -names output_names.v -o output_cpp.v input.cpp -- -std=c++17 -I.
```

## External Resources

- **BRiCk repo**: https://github.com/bedrocksystems/BRiCk
  - [`howto_sequential.v`](https://github.com/bedrocksystems/BRiCk/blob/master/rocq-skylabs-brick/theories/noimport/doc/cpp/howto_sequential.v) — best tutorial
  - [`theories/lang/cpp/`](https://github.com/bedrocksystems/BRiCk/tree/master/rocq-skylabs-brick/theories/lang/cpp) — core theory files
- **Workspace meta-repo**: https://github.com/SkylabsAI/workspace
- **Iris framework**: https://iris-project.org/
  - [Iris tutorial (POPL'21)](https://gitlab.mpi-sws.org/iris/tutorial-popl21)
  - [A beginner's guide to Iris](https://arxiv.org/pdf/2105.12077)

## Workflow

1. **cpp2v**: C++ source → Coq deep embedding (`_cpp.v` + `_cpp_names.v`)
2. **Functional spec**: Pure Coq model of the data structure / algorithm
3. **Representation predicate** (`Rep`): Links Coq model to C++ heap layout
4. **Refinement proofs**: Each C++ function refines its Coq spec via Hoare triples

## Quick Reference

### Imports

```coq
Require Import skylabs.lang.cpp.cpp.
Import cQp_compat.
From iris.proofmode Require Import proofmode.

Section with_Sigma.
Context `{Sigma : cpp_logic} {CU : genv}.
(* definitions and proofs *)
End with_Sigma.
```

### Key Types

| Type | Meaning |
|------|---------|
| `Rep` | Representation predicate (`ptr -> mpred`) |
| `ptr` | Abstract C++ pointer |
| `offset` | Field/array offset |
| `mpred` | Iris separation logic proposition |
| `Qp` | Fractional permission (0 < q <= 1) |

### Core Patterns

**Struct rep** — compose fields with `**`:
```coq
Definition PointR (q : Qp) (p : Point) : Rep :=
  _x |-> intR q p.(px) **
  _y |-> intR q p.(py).
```

**Recursive rep** — `as_Rep` + `Exists` for child pointers:
```coq
Fixpoint treeR (q : Qp) (t : tree A) : Rep :=
  as_Rep (fun this =>
    match t with
    | leaf => [| this = nullptr |]
    | node d l r =>
      Exists (lp rp : ptr),
      lp |-> treeR q l ** rp |-> treeR q r **
      this |-> (_data |-> R q d ** _left |-> ptrR<_T> q lp ** _right |-> ptrR<_T> q rp)
    end).
```

**Function spec**:
```coq
Definition insert_spec : function_spec :=
  SFunction (cc:=CC_C) (ar:=Ar_Definite) (Tptr _Node) (Tint :: Tptr _Node :: nil)
    (cpp_spec (ar:=Ar_Definite) (Tptr _Node) (Tint :: Tptr _Node :: nil)
      (\arg{x} "x" (Vint x)
       \arg{n} "n" (Vptr n)
       \pre{t} n |-> myRep 1 t
       \post{ret}[Vptr ret] ret |-> myRep 1 (insert x t))).
```

## Rocq 9.x Conventions

- `From Stdlib Require Import ...` (not `From Coq`)
- `intuition auto` (not bare `intuition`)
- Zero `Admitted` in final code

## Version Compatibility

BRiCk's dependency chain (Rocq, Iris, stdpp, elpi, equations, etc.) requires
precise version alignment. **Always use the workspace meta-repo** — manual
opam installs will hit version conflicts.
