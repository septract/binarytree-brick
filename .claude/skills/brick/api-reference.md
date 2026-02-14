# BRiCk API Reference

Detailed reference for the BRiCk C++ verification framework types,
notations, and proof patterns. Source: `rocq-skylabs-brick/theories/lang/cpp/`.

## Type System

### Values (`val`)

C++ values are represented as:

```coq
Vint (n : Z)         (* integer value *)
Vbool (b : bool)     (* boolean value *)
Vptr (p : ptr)       (* pointer value *)
Vnullptr             (* null pointer value *)
```

### C++ Types (`type` / `Rtype`)

```coq
Tbool                (* bool *)
Tint                 (* signed int *)
Tuint                (* unsigned int *)
Tlong                (* signed long *)
Tulong               (* unsigned long *)
Tptr ty              (* pointer to ty *)
Tref ty              (* reference to ty *)
Tnamed name          (* named struct/class *)
```

### Pointers (`ptr`)

Abstract type with provenance tracking. Key values:

```coq
nullptr : ptr        (* null pointer *)
p ,, o  : ptr        (* pointer p offset by o *)
```

### Offsets (`offset`)

```coq
_field f             (* field offset — f is a field name string *)
.[ ty ! n ]          (* array subscript: p[n] when p points to ty *)
o1 ,, o2             (* compose two offsets *)
```

## Representation Predicates (`Rep`)

`Rep` is a monadic predicate: `ptr -> mpred`. Created via:

```coq
as_Rep (fun p => ...)    (* explicit construction from ptr -> mpred *)
```

### Points-to Operator `|->`

Overloaded on left operand:

```coq
(* ptr |-> Rep = mpred — evaluates Rep at the pointer *)
p |-> R

(* offset |-> Rep = Rep — creates Rep shifted by offset *)
o |-> R

(* Chaining: equivalent forms *)
p |-> (o |-> R)    ⊣⊢    p ,, o |-> R
```

### Primitive Type Reps

All are `Notation` wrappers around `primR`:

```coq
primR : Rtype -> cQp.t -> val -> Rep     (* core primitive *)

(* Convenience notations *)
boolR q v        := primR Tbool q (Vbool v)
intR q v         := primR Tint q (Vint v)       (* = sintR *)
sintR q v        := primR Tint q (Vint v)
uintR q v        := primR Tuint q (Vint v)
longR q v        := primR Tlong q (Vint v)      (* = slongR *)
slongR q v       := primR Tlong q (Vint v)
ulongR q v       := primR Tulong q (Vint v)
ptrR<ty> q p     := primR (Tptr ty) q (Vptr p)
refR<ty> q p     := primR (Tref ty) q (Vptr p)
```

### anyR — Existentially Quantified Value

```coq
anyR : Rtype -> cQp.t -> Rep
(* Asserts some value of the given type exists at the location *)
(* Useful in preconditions when value doesn't matter *)
```

### Pure Assertions

```coq
[| P |]              (* Prop P as Rep — no resources consumed *)
pureR (Q : mpred)    (* mpred Q as Rep, independent of location *)
```

### Separating Conjunction

```coq
R1 ** R2             (* separating conjunction of two Reps *)
emp                  (* empty Rep — no resources *)
```

## Field Access

### Defining Fields from cpp2v Names

cpp2v generates a `_names.v` file with `Notation` entries for mangled C++
names. Define field accessors using `_field`:

```coq
(* From the generated _names.v, find the field notation string *)
Definition _begin := _field "Range::_begin".
Definition _size  := _field "Range::_size".
```

For namespaced/templated classes, use the full mangled name:

```coq
Definition _key := _field "::MyNS::MyClass<int>::key".
```

### Using Fields in Reps

```coq
(* Field offset applied to a Rep *)
_begin |-> ulongR q val     (* offset-level: Rep *)

(* At a specific pointer *)
p |-> (_begin |-> ulongR q val)    (* pointer-level: mpred *)

(* Equivalent to *)
(p ,, _begin) |-> ulongR q val
```

## Struct Representation Patterns

### Flat Struct (No Pointer Fields)

```coq
Record Range := { rng_begin : Z; rng_size : Z }.

Definition _begin := _field "Range::_begin".
Definition _size  := _field "Range::_size".

Definition RangeR (q : Qp) (r : Range) : Rep :=
  _begin |-> ulongR q r.(rng_begin) **
  _size  |-> ulongR q r.(rng_size).
```

No `as_Rep` needed — field-level `|->` composition works directly.

### Struct with Pointer Fields

```coq
Record NodeModel := {
  nm_data  : Z;
  nm_left  : ptr;
  nm_right : ptr;
}.

Definition NodeR (q : Qp) (n : NodeModel) : Rep :=
  _field _data  |-> intR q n.(nm_data) **
  _field _left  |-> ptrR<_Tree> q n.(nm_left) **
  _field _right |-> ptrR<_Tree> q n.(nm_right).
```

### Recursive Data Structure (Tree)

Use `as_Rep` when you need the `this` pointer (null check, self-reference):

```coq
Section treeR.
Context {A : Type} (R : Qp -> A -> Rep).

Fixpoint treeR (q : Qp) (t : tree A) : Rep :=
  as_Rep (fun this =>
    match t with
    | leaf => [| this = nullptr |]
    | node d l r =>
      Exists (lp : ptr) (rp : ptr),
      lp |-> treeR q l **
      rp |-> treeR q r **
      this |-> (_field _data  |-> R q d **
                _field _left  |-> ptrR<_Tree> q lp **
                _field _right |-> ptrR<_Tree> q rp)
    end
  ).

End treeR.
```

**Key points:**
- `leaf` = `[| this = nullptr |]` (null pointer, no heap resources)
- `node` = `Exists` child pointers, separate assertions for:
  - child subtrees (`lp |-> treeR q l`)
  - current node fields (`this |-> (... ** ... ** ...)`)

### Combining with Pure Invariants

```coq
(* Attach a sortedness/well-formedness invariant *)
Definition bstR (q : Qp) (t : tree Z) : Rep :=
  treeR (fun q z => intR q z) q t ** [| sorted Z.lt t |].
```

## Function Specifications

### cpp_spec Structure

```coq
Definition func_spec (this : ptr) :=
  cpp_spec ReturnType [ArgType1; ArgType2] $
  \with (ghost_var1 : Type1) (ghost_var2 : Type2)
  \arg{x} "param_name" (Vint x)
  \pre  (* precondition: mpred *)
    this |-> SomeR 1 ghost_var1
  \post (* postcondition: mpred *)
    this |-> SomeR 1 (modified ghost_var1).
```

### Spec Patterns

**Read-only** — use fractional permission `q`, `\prepost` for frame:
```coq
Definition count_spec (this : ptr) :=
  cpp_spec Tint [] $
  \with (q : Qp) (t : tree Z)
  \prepost this |-> treeR (fun q z => uintR q z) q t
  \post[Vint (count t)] emp.
```

**Mutating** — take full permission `1`:
```coq
Definition insert_spec (this : ptr) :=
  cpp_spec Tbool [Tint] $
  \with (t : tree Z)
  \arg{x} "x" (Vint x)
  \pre this |-> bstR 1 t
  \post this |-> bstR 1 (insert x t).
```

**With existential postcondition:**
```coq
Definition insert_spec' (this : ptr) :=
  cpp_spec Tbool [Tint] $
  \with (t : tree Z)
  \arg{x} "x" (Vint x)
  \pre this |-> bstR 1 t
  \post Exists t',
    this |-> bstR 1 t' **
    [| forall y, in_tree y t' <-> (y = x \/ in_tree y t) |].
```

## Fractional Permissions (`Qp` / `cQp.t`)

```coq
1                    (* exclusive / full ownership — can read and write *)
(1/2)                (* half — read-only, can be split/joined *)
q1 + q2              (* combine two fractional permissions *)
```

Rules:
- `1` = exclusive write access
- Any `q < 1` = read-only shared access
- Two halves can be joined: `(1/2) + (1/2) = 1`
- `primR` with matching type and permission agrees on value:

```coq
Instance primR_observe_agree ty q1 q2 v1 v2 :
  Observe2 [| v1 = v2 |] (primR ty q1 v1) (primR ty q2 v2).
```

## Key Lemmas

### Rep Composition

```coq
(* Separating conjunction distributes over |-> *)
Lemma _at_sep p (P Q : Rep) :
  p |-> (P ** Q) -|- p |-> P ** p |-> Q.

(* Offset composition *)
Lemma _offsetR_offsetR (o1 o2 : offset) R :
  o1 |-> (o2 |-> R) -|- o1 ,, o2 |-> R.

(* as_Rep evaluation *)
Lemma _at_as_Rep p (Q : ptr -> mpred) :
  p |-> (as_Rep Q) ⊣⊢ Q p.

(* Offset distributes over sep *)
Lemma _offsetR_sep o r1 r2 :
  o |-> (r1 ** r2) -|- o |-> r1 ** o |-> r2.

(* Exists distributes over offset *)
Lemma _offsetR_exists o {T} (P : T -> Rep) :
  o |-> (Exists v : T, P v) -|- Exists v, o |-> (P v).

(* Empty offset *)
Lemma _offsetR_emp o :
  o |-> emp ⊣⊢ emp.
```

## Proof Tactics

### Iris Proof Mode (IPM)

```coq
iIntros "H".                   (* introduce hypothesis named "H" *)
iIntros (x y).                 (* introduce universally quantified vars *)
iDestruct "H" as "[H1 H2]".   (* split separating conjunction *)
iDestruct "H" as (x) "H".     (* eliminate existential *)
iExists v1, v2.               (* provide existential witnesses *)
iFrame.                        (* frame matching resources *)
iFrame "H1".                   (* frame specific hypothesis *)
iSplit.                        (* split persistent/pure conjunction *)
iPureIntro.                    (* switch to pure Coq goal *)
iApply "H".                    (* apply hypothesis *)
done.                          (* close trivial goal *)
```

### wp Tactics (Weakest Precondition)

```coq
wp_call.                       (* step through function call *)
wp_if.                         (* step through if/else branch *)
wp_while inv.                  (* while loop with loop invariant *)
wp_field.                      (* field access *)
wp_alloc p as "Hp".            (* allocate, bind pointer to p *)
wp_free.                       (* free allocation *)
wp_load.                       (* load from memory *)
wp_store.                      (* store to memory *)
```

### Observe Pattern (Extract Pure Facts)

```coq
(* Extract agreement from two fractional resources *)
iDestruct (observe_2 [| v1 = v2 |] with "R1 R2") as %Heq.
```

## cpp2v Integration

### Running cpp2v

```bash
cpp2v -v -names output_names.v -o output_cpp.v input.cpp -- -std=c++17 -I.
```

### Monomorphization

cpp2v operates on Clang's elaborated AST. Templates must be instantiated:

```cpp
// Force template instantiation for cpp2v
template class MyContainer<int>;

void driver() {
    MyContainer<int> c;
    c.insert(42);
    c.find(42);
}
```

### Reading Generated Files

- `_cpp.v` — Deep embedding of the C++ AST (~thousands of lines)
- `_cpp_names.v` — Symbol table mapping mangled C++ names to Coq terms

Look for:
- Struct definitions: search for `Gstruct` in the AST file
- Field names: search for your class name in the names file
- Function bodies: search for function names in the AST file
- Type aliases: `Tnamed`, `Tptr`, field type annotations
