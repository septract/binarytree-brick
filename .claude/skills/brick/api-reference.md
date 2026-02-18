# BRiCk API Reference

Detailed reference for the BRiCk C++ verification framework types,
notations, and proof patterns. Source: `rocq-skylabs-brick/theories/lang/cpp/`.

## Type System

### Values (`val`)

C++ values are represented as:

```coq
Vint (n : Z)         (* integer value *)
Vbool (b : bool)     (* = Vint (if b then 1 else 0), NOT a separate constructor *)
Vptr (p : ptr)       (* pointer value *)
Vnullptr             (* null pointer value *)
```

**Gotcha**: `Vbool b` is notation for `Vint (if b then 1 else 0)`.
`is_true (Vint i) = Some (bool_decide (i ≠ 0))` reduces automatically.

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
(* Useful in postconditions when old value doesn't matter *)
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

### Validity / Non-nullness

```coq
structR cls q        (* struct identity — implies nonnullR, validR, type_ptrR *)
nonnullR             (* pointer is non-null *)
validR               (* pointer is valid (strict) *)
svalidR              (* pointer is strictly valid *)
type_ptrR ty         (* pointer has type ty *)
```

**Design rule**: always include `structR cls q` in the Node case of
recursive rep predicates. It provides `nonnullR` (for null contradictions),
`validR` (for pointer comparisons), and `reference_to` (for field access).

### Intermediate Storage Predicates

These appear during wp proofs for local variables:

```coq
tptsto_fuzzyR ty q v    (* fuzzy typed points-to — standard local var form *)
tptstoR ty q v          (* typed points-to — produced by assignment *)
initializedR ty q v     (* combines has_type + tptsto — for reading *)
```

Conversion chain:
```
tptstoR  →  tptsto_fuzzyR  →  anyR       (weakening direction)
primR    ↔  has_type ** tptsto_fuzzyR     (decomposition)
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
Fixpoint treeR (q : Qp) (t : tree A) : Rep :=
  as_Rep (fun this =>
    match t with
    | leaf => [| this = nullptr |]
    | node d l r =>
      Exists (lp : ptr) (rp : ptr),
      lp |-> treeR q l **
      rp |-> treeR q r **
      this |-> (_data  |-> R q d **
                _left  |-> ptrR<_Tree> q lp **
                _right |-> ptrR<_Tree> q rp **
                structR _Tree_name q)   (* <-- required for nonnullR/validR *)
    end).
```

**Key points:**
- `leaf` = `[| this = nullptr |]` (null pointer, no heap resources)
- `node` = `Exists` child pointers, separate assertions for:
  - child subtrees (`lp |-> treeR q l`)
  - current node fields (`this |-> (... ** ... ** structR)`)
- Always include `structR` — see "Validity / Non-nullness" above

**Characterization lemmas** (always define these):
```coq
Lemma treeR_leaf q : treeR q Leaf = as_Rep (fun p => [| p = nullptr |]).
Proof. reflexivity. Qed.

Lemma treeR_node q c l k v r : treeR q (Node c l k v r) = as_Rep (fun this => ...).
Proof. reflexivity. Qed.
```
Use these instead of `simpl`/`unfold` — direct unfolding interacts badly
with Iris's proof mode.

### Combining with Pure Invariants

```coq
(* Attach a sortedness/well-formedness invariant *)
Definition bstR (q : Qp) (t : tree Z) : Rep :=
  treeR (fun q z => intR q z) q t ** [| sorted Z.lt t |].
```

## Function Specifications

### cpp_spec Structure

```coq
Definition func_spec : function_spec :=
  SFunction (cc:=CC_C) (ar:=Ar_Definite) RetType [ArgType1; ArgType2]
    (cpp_spec (ar:=Ar_Definite) RetType [ArgType1; ArgType2]
      (\arg{x} "param_name" (Vint x)
       \arg{n} "param_name2" (Vptr n)
       \pre (* precondition: mpred *)
         ...
       \post (* postcondition: mpred *)
         ...)).
```

### Spec Patterns

**Read-only** — use fractional permission `q`, `\prepost` for frame:
```coq
\prepost{q t} p |-> myRep q t
\post{ret}[Vptr ret] [| pure_result |]
```

**Mutating / ownership transfer** — take full permission `1`, `\pre` + `\post`:
```coq
\pre{t} p |-> myRep (cQp.m 1) t
\post{ret}[Vptr ret] ret |-> myRep (cQp.m 1) (transform t)
```

Use ownership transfer when the function may free/reallocate the input.

**With existential postcondition:**
```coq
\post Exists t',
  this |-> myRep 1 t' **
  [| some_relation t t' |]
```

## Fractional Permissions (`Qp` / `cQp.t`)

```coq
1                    (* exclusive / full ownership — can read and write *)
(1/2)                (* half — read-only, can be split/joined *)
q1 + q2              (* combine two fractional permissions *)
(cQp.m 1)            (* monomorphic form of 1, used in specs *)
```

Rules:
- `1` = exclusive write access
- Any `q < 1` = read-only shared access
- Two halves can be joined: `(1/2) + (1/2) = 1`

## Key Lemmas

### Rep Composition

```coq
(* Separating conjunction distributes over |-> *)
Lemma _at_sep p (P Q : Rep) :
  p |-> (P ** Q) -|- p |-> P ** p |-> Q.

(* Offset composition *)
Lemma _offsetR_offsetR (o1 o2 : offset) R :
  o1 |-> (o2 |-> R) -|- o1 ,, o2 |-> R.

(* as_Rep evaluation — critical for unfold/fold *)
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

### Storage Predicate Conversions

```coq
(* Weaken tptstoR to tptsto_fuzzyR (after assignment) *)
tptsto_fuzzyR_intro : p |-> tptstoR ty q v |-- p |-> tptsto_fuzzyR ty q v

(* Convert tptsto_fuzzyR to anyR (for cleanup) *)
anyR_tptsto_fuzzyR_val_2 : tptsto_fuzzyR ty q v -|- anyR ty q

(* Decompose primR into components *)
_at_primR : p |-> primR ty q v ⊣⊢
  [| ~~ is_raw v |] ** has_type v ty ** p |-> tptsto_fuzzyR ty q v
```

### Observe Instances

```coq
(* reference_to from structR — for field access *)
structR_reference_to cls q p :
  Observe (reference_to (Tnamed cls) p) (p |-> structR cls q)

(* nonnullR from structR — for null contradictions *)
structR_nonnullR : Observe (p |-> nonnullR) (p |-> structR cls q)

(* validR from structR — for pointer comparisons *)
structR_validR : Observe (p |-> validR) (p |-> structR cls q)

(* has_type from primR — for eval_binop *)
primR_observe_has_type_prop :
  Observe [| has_type_prop v ty |] (p |-> primR ty q v)

(* has_type_or_undef from tptsto_fuzzyR — for reading locals *)
(* available via observe instance *)
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
iSplitL "H1 H2".              (* split sep conj, left gets named hyps *)
iSplitR "H3".                 (* split sep conj, right gets named hyps *)
iPureIntro.                    (* switch to pure Coq goal *)
iApply "H".                    (* apply hypothesis *)
iRevert "H".                   (* move hypothesis back to goal *)
iClear "H".                    (* discard hypothesis *)
iModIntro.                     (* strip fancy update modality *)
iNext.                         (* strip later modality *)
done.                          (* close trivial goal *)
```

### Observe Pattern (Non-destructive Fact Extraction)

```coq
(* Extract persistent fact without consuming resource *)
iDestruct (observe (reference_to _ _) with "H") as "#Href".
iDestruct (observe (has_type_or_undef v ty) with "H") as "#Hty".
iDestruct (observe (p |-> nonnullR) with "Hstruct") as "#Hnn".
iDestruct (observe (p |-> validR) with "Hstruct") as "#Hv".
iDestruct (observe ([| has_type_prop (Vint x) Tint |]) with "H") as "%Htp".
```

`#` prefix = persistent (survives iSplitL/iSplitR).
`%` prefix = pure Coq fact (moves to Coq context).

### wp Tactics (Weakest Precondition)

See [wp-proof-guide.md](wp-proof-guide.md) for the full proof architecture.

```coq
(* Statement-level *)
iApply wp_seq.                 (* step through sequence *)
iApply wp_break.               (* break from loop *)
iApply wp_return.              (* return statement *)
iApply wp_expr.                (* expression statement *)
iApply (wp_if tu).             (* if/else branch *)
iApply (wp_while_inv tu Inv).  (* while loop with invariant *)

(* Expression-level *)
iApply wp_operand_call.        (* function call *)
iApply (wp_operand_binop tu).  (* binary operator *)
iApply wp_operand_cast_l2r.    (* lvalue-to-rvalue cast *)
iApply wp_operand_cast_null.   (* nullptr literal *)
iApply wp_null.                (* null value *)
iApply wp_lval_var.            (* variable lookup *)
iApply wp_lval_member.         (* field member access *)
iApply wp_lval_assign.         (* assignment *)
iApply wp_func_intro.          (* enter function body *)
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
