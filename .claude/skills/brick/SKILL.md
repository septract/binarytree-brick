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

## External Resources

- **BRiCk repo**: https://github.com/bedrocksystems/BRiCk
  - [README](https://github.com/bedrocksystems/BRiCk/blob/master/README.md) — build instructions, repo layout
  - [`howto_sequential.v`](https://github.com/bedrocksystems/BRiCk/blob/master/rocq-skylabs-brick/theories/noimport/doc/cpp/howto_sequential.v) — best tutorial: Range, Tree, BST, linked list reps + specs
  - [`theories/lang/cpp/`](https://github.com/bedrocksystems/BRiCk/tree/master/rocq-skylabs-brick/theories/lang/cpp) — core theory files (rep, primitives, logic, semantics)
- **Paper**: [Towards an Axiomatic Basis for C++](https://gmalecha.github.io/publications/2020/towards-an-axiomatic-basis-for-c++) (Malecha, Anand, Stewart — Coq Workshop 2020)
- **Iris framework**: https://iris-project.org/
  - [Iris tutorial (POPL'21)](https://gitlab.mpi-sws.org/iris/tutorial-popl21) — learn IPM proof mode
  - [A beginner's guide to Iris](https://arxiv.org/pdf/2105.12077) — separation logic in Coq tutorial
  - [Iris Coq development](https://gitlab.mpi-sws.org/iris/iris) — source + IPM/MoSeL docs

## Workflow

1. **cpp2v**: C++ source -> Coq deep embedding (`_cpp.v` + `_cpp_names.v`)
2. **Functional spec**: Pure Coq model of the data structure / algorithm
3. **Representation predicate** (`Rep`): Links Coq model to C++ heap layout
4. **Refinement proofs**: Each C++ function refines its Coq spec via Hoare triples

## Quick Reference

### Imports

```coq
Require Import skylabs.lang.cpp.cpp.
Import cQp_compat.
Import primitives.
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

### Primitive Reps

```coq
boolR q v         (* bool *)       intR q v          (* signed int *)
uintR q v         (* unsigned int *)ulongR q v        (* unsigned long *)
ptrR<ty> q p      (* pointer to ty *)
```

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
      this |-> (_field _data  |-> R q d **
                _field _left  |-> ptrR<_T> q lp **
                _field _right |-> ptrR<_T> q rp)
    end).
```

**Function spec** — Hoare triple via `cpp_spec`:
```coq
Definition insert_spec (this : ptr) :=
  cpp_spec Tbool [Tint] $
  \with (t : tree Z)
  \arg{x} "x" (Vint x)
  \pre this |-> bstR 1 t
  \post this |-> bstR 1 (insert x t).
```

For the full API reference, see [api-reference.md](api-reference.md).

## Rocq 9.x Conventions

- `From Stdlib Require Import ...` (not `From Coq`)
- `intuition auto` (not bare `intuition`)
- Zero `Admitted` in final code

## Version Compatibility

BRiCk Coq theories require version alignment between `rocq-skylabs-prelude`
and `coq-stdpp` (Iris stdpp). When building from source, pin to matching
commits. The `elem_of_list_bind` API is a known breakage point between
stdpp versions.
