# Phase 5B Plan: Prove Callee Functions (setRebalanceLeft/Right, ins)

*Created: 2026-02-22*

## Goal

Discharge the Admitted callee proofs that `insert_ok` depends on:
`setRebalanceLeft_ok`, `setRebalanceRight_ok`, and `ins_ok`.

`makeCopy_ok` stays Admitted — it requires ref-count ghost state (Phase 6).

## Current State

| Lemma | Status | File |
|-------|--------|------|
| `insert_ok` | **Qed** | InsertSpec.v |
| `ins_ok` | Admitted | InsertDefs.v |
| `setRebalanceLeft_ok` | Admitted | InsertDefs.v |
| `setRebalanceRight_ok` | Admitted | InsertDefs.v |
| `makeCopy_ok` | Admitted | InsertDefs.v (Phase 6) |

## Critical Finding: Specs Need Revision

The current `setRebalanceLeft_spec` and `setRebalanceRight_spec` in
InsertDefs.v are **wrong** for actual usage.

### The Problem

Current spec (InsertDefs.v:209-219):
```coq
Definition setRebalanceLeft_spec : function_spec :=
  ... (\arg{n_ptr} "n" (Vptr n_ptr)
       \arg{nl_ptr} "newLeft" (Vptr nl_ptr)
       \pre{c k v l r} n_ptr |-> treeR (cQp.m 1) (Node c l k v r)
       \pre nl_ptr |-> treeR (cQp.m 1) Leaf      (* <-- WRONG *)
       \post{ret}[Vptr ret]
         ret |-> treeR (cQp.m 1) (setRebalanceLeft c Leaf k v r)).
```

This requires `newLeft` to be `Leaf`, but in actual usage from `ins`:

```cpp
return setRebalanceLeft(n, ins(k, v, n->left));
```

`newLeft` is the result of `ins(k, v, n->left)` — an arbitrary tree.

Worse, the caller cannot provide `n_ptr |-> treeR (Node c l k v r)` because
the left subtree's ownership has already been consumed by the recursive
`ins` call. At the call site we have:

- `n`'s struct fields (color, key, value, left-ptr, right-ptr, ref_count, struct)
- `rp |-> treeR r` (right subtree, untouched)
- `result |-> treeR (ins k v l)` (from the recursive call)
- The left-pointer field in `n` is *stale* — it still stores `lp` but `lp`'s
  tree ownership was consumed by `ins`

### The Fix: Field-Level Node Predicate

Introduce `nodeFieldsR` — the struct fields of a Node without subtree
ownership:

```coq
Definition nodeFieldsR (q : Qp) (c : Color) (k v : Z)
    (lp rp : ptr) (rc : Z) : Rep :=
  as_Rep (fun this =>
    this |-> (_ref_count |-> ulongR q rc **
              _color     |-> boolR q (color_to_bool c) **
              _key       |-> intR q k **
              _value     |-> intR q v **
              _left      |-> ptrR<_Node> q lp **
              _right     |-> ptrR<_Node> q rp **
              structR _Node_name q)).
```

Then `treeR (Node c l k v r)` decomposes as:
```
Exists lp rp rc,
  nodeFieldsR q c k v lp rp rc **
  lp |-> treeR q l **
  rp |-> treeR q r
```

### Corrected Specs

```coq
(** setRebalanceLeft receives n's fields + right subtree + new left tree.
    The old left subtree has been consumed by the caller (recursive ins). *)
Definition setRebalanceLeft_spec : function_spec :=
  SFunction (cc:=CC_C) (ar:=Ar_Definite) (Tptr _Node)
    (Tptr _Node :: Tptr _Node :: nil)
    (cpp_spec (ar:=Ar_Definite) (Tptr _Node)
      (Tptr _Node :: Tptr _Node :: nil)
      (\arg{n_ptr} "n" (Vptr n_ptr)
       \arg{nl_ptr} "newLeft" (Vptr nl_ptr)
       \pre{c k v lp rp rc r newL}
         n_ptr |-> nodeFieldsR (cQp.m 1) c k v lp rp rc **
         rp |-> treeR (cQp.m 1) r
       \pre nl_ptr |-> treeR (cQp.m 1) newL
       \post{ret}[Vptr ret]
         ret |-> treeR (cQp.m 1) (setRebalanceLeft c newL k v r))).

(** Mirror for right. Left subtree preserved, right consumed by caller. *)
Definition setRebalanceRight_spec : function_spec :=
  SFunction (cc:=CC_C) (ar:=Ar_Definite) (Tptr _Node)
    (Tptr _Node :: Tptr _Node :: nil)
    (cpp_spec (ar:=Ar_Definite) (Tptr _Node)
      (Tptr _Node :: Tptr _Node :: nil)
      (\arg{n_ptr} "n" (Vptr n_ptr)
       \arg{nr_ptr} "newRight" (Vptr nr_ptr)
       \pre{c k v lp rp rc l newR}
         n_ptr |-> nodeFieldsR (cQp.m 1) c k v lp rp rc **
         lp |-> treeR (cQp.m 1) l
       \pre nr_ptr |-> treeR (cQp.m 1) newR
       \post{ret}[Vptr ret]
         ret |-> treeR (cQp.m 1) (setRebalanceRight c l k v newR))).
```

Note the asymmetry: `setRebalanceLeft` preserves the *right* subtree
(left was consumed), `setRebalanceRight` preserves the *left* subtree.

**Why this works**: The C++ code never reads the consumed child pointer.
In `setRebalanceLeft`, `n->left` is always *overwritten* (default case:
`res->left = newLeft`; LL: `r->left = newLeft->right`; LR:
`r->left = sub2->right`). It is never read.

## Additional Function Specs Needed

### is_black / is_red

```cpp
static bool is_black(Node const* n) { return n == nullptr || n->color == black; }
static bool is_red(Node const* n) { return !is_black(n); }
```

Called by `setRebalanceLeft`/`Right` to check color conditions. Need specs:

```coq
(** Borrows the tree read-only (fractional permission). *)
Definition is_black_spec : function_spec :=
  SFunction (cc:=CC_C) (ar:=Ar_Definite) Tbool
    (Tptr (Tconst _Node) :: nil)
    (cpp_spec ...
      (\arg{n_ptr} "n" (Vptr n_ptr)
       \prepost{t} n_ptr |-> treeR q t
       \post{ret}[Vbool (is_black t)])).
```

**Complication**: `is_black` takes `Node const*`. BRiCk may require
handling the `T*` → `T const*` implicit conversion. If this is too
cumbersome, **Alternative**: inline `is_black`/`is_red` in the proofs
(step through the null check + field read directly). This avoids
needing a separate spec at the cost of longer proofs.

### Node 5-arg Constructor

```cpp
Node(Color color, Node *left, Key key, Value value, Node *right)
  : ref_count(1), color(color), key(key), value(value),
    left(left), right(right) { }
```

Used in `ins` base case: `new Node(red, nullptr, k, v, nullptr)`.

This constructor does NOT call `copy()` on children (unlike the copy
constructor `Node(Node*)`), so it should be provable without Phase 6
ghost state. The constructor sets `ref_count=1`, which satisfies the
existential `rc` in `treeR`.

**Note**: `new Node(...)` involves both memory allocation (`operator new`)
and constructor call. BRiCk should have wp rules for `Enew` expressions.
Research needed on exact proof pattern.

### makeCopy (stays Admitted)

The existing spec is correct:
```coq
\pre{t} p |-> treeR (cQp.m 1) t
\post{ret} ret |-> treeR (cQp.m 1) t
```

But `makeCopy` checks `ref_count` internally:
- If `ref_count == 1`: return p (trivial)
- If `ref_count > 1`: call copy constructor `Node(Node*)` + `free(p)`

The copy constructor calls `copy(left)` and `copy(right)` (incrementing
ref counts). Proving this requires ghost state linking `ref_count` to
ownership — Phase 6.

## Proof Strategies

### setRebalanceLeft_ok / setRebalanceRight_ok

Standard wp proof with 3-way case split:

```
1. Extract args (n, newLeft)
2. Step through outer if: is_black(n) && is_red(newLeft)
   - Read n->color (from nodeFieldsR)
   - Unfold newLeft's treeR, read color, refold or keep unfolded
3. Case split:
   a. LL case (is_black(n) ∧ is_red(newLeft) ∧ is_red(newLeft->left)):
      - Read newLeft->left (sub2)
      - Call makeCopy(sub2) [Admitted spec]
      - Set l->color = black
      - Set r->color = black, r->left = newLeft->right
      - Set newLeft->left = l, newLeft->right = r
      - Fold result into treeR (setRebalanceLeft ...)
   b. LR case (is_black(n) ∧ is_red(newLeft) ∧ is_red(newLeft->right)):
      - Similar rotation with different pointer rewiring
      - Call makeCopy(sub2) [Admitted spec]
   c. Default case (everything else):
      - Set n->left = newLeft
      - Fold result into treeR (Node c newLeft k v r)
      - Show this equals setRebalanceLeft c newLeft k v r
4. Return + postcondition
```

**Estimated complexity**: ~150-250 lines per function (3 cases × ~50-80
lines each). The rotation cases are mechanical but tedious.

### ins_ok

Recursive function — requires **Löb induction** in Iris:

```
1. iLöb as "IH"  (* ▷ func_ok source ins_func ins_spec *)
2. Extract args (k, v, n)
3. Unfold ins_func body
4. Case: n == nullptr (base case)
   - new Node(red, nullptr, k, v, nullptr)
   - Needs Node constructor spec
   - Result: treeR (Node Red Leaf k v Leaf)
   - Show this = ins k v Leaf ✓
5. Case: n != nullptr
   - Call makeCopy(n) [Admitted]
   - Unfold treeR at n to get field access
   - Read n->key for comparison
   a. k < n->key:
      - Read n->left to get lp
      - Recursive call ins(k, v, lp) via ▷IH
        - Consumes lp |-> treeR l
        - Produces result |-> treeR (ins k v l)
      - Call setRebalanceLeft(n, result)
        - Uses nodeFieldsR at n + rp |-> treeR r + result tree
        - Produces ret |-> treeR (setRebalanceLeft c (ins k v l) k v r)
      - Show this = ins k v (Node c l k v r) ✓
   b. n->key < k:
      - Mirror of (a) with setRebalanceRight
   c. k == n->key:
      - Write n->value = v
      - Fold treeR back with updated value
      - Show result = ins k v (Node c l k v r) = Node c l k v r ✓
      - (hasRefs<int>() is false, so k.free()/n->value.free() compiled away)
6. Return + postcondition
```

**Estimated complexity**: ~200-300 lines. The Löb induction + recursive
call pattern is the novel part; the rest follows established patterns.

## File Structure

### Build time analysis (current)

| File | Build time | Dependencies |
|------|-----------|--------------|
| map_int_int_cpp.vo | 30-60 min | (generated AST) |
| InsertDefs.vo | 5-10 min | map_int_int_cpp.vo |
| InsertSpec.vo | 10-12 min | InsertDefs.vo, Tactics.vo |

**Key constraint**: Any change to InsertDefs.v triggers a 15-22 min
rebuild (InsertDefs.vo + InsertSpec.vo).

### New file layout

```
coq/
  TreeRep.v         ← add nodeFieldsR + fold/unfold lemmas (*)
  InsertDefs.v      ← fix setRebalanceLeft/Right specs (one-time)
  CalleeDefs.v      ← NEW: is_black, is_red, Node ctor extraction + specs
  RebalanceSpec.v   ← NEW: setRebalanceLeft_ok, setRebalanceRight_ok
  InsSpec.v         ← NEW: ins_ok (Löb induction)
```

(*) Adding `nodeFieldsR` to TreeRep.v triggers a rebuild of downstream
files (Tactics, FindSpec, InsertDefs, etc.). **Alternative**: define it
in a new `NodeFields.v` or in `CalleeDefs.v` to isolate the change.
Decision: put it in **Tactics.v** (already imports TreeRep, already
imported by proof files). This triggers rebuilds of FindSpec.vo and
InsertSpec.vo but not InsertDefs.vo or map_int_int_cpp.vo.

### Dependency graph (new files in bold)

```
map_int_int_cpp.vo (30-60 min, never rebuilds)
  ├── InsertDefs.vo (5-10 min, one-time fix)
  │     └── InsertSpec.vo (10-12 min, one-time rebuild)
  ├── CalleeDefs.vo (5-10 min, new)
  │     ├── RebalanceSpec.vo (new, fast iteration)
  │     └── InsSpec.vo (new, fast iteration)
  └── FindSpec.vo (existing, unaffected)

Tactics.vo ──► RebalanceSpec.vo, InsSpec.vo
InsertDefs.vo ──► RebalanceSpec.vo, InsSpec.vo
```

### Makefile additions

```makefile
$(COQ_DIR)/CalleeDefs.vo: $(COQ_DIR)/CalleeDefs.v \
    $(COQ_DIR)/RBTree.vo $(COQ_DIR)/TreeRep.vo $(COQ_DIR)/map_int_int_cpp.vo
	$(COQC) $(COQFLAGS) $<

$(COQ_DIR)/RebalanceSpec.vo: $(COQ_DIR)/RebalanceSpec.v \
    $(COQ_DIR)/CalleeDefs.vo $(COQ_DIR)/InsertDefs.vo $(COQ_DIR)/Tactics.vo
	$(COQC) $(COQFLAGS) $<

$(COQ_DIR)/InsSpec.vo: $(COQ_DIR)/InsSpec.v \
    $(COQ_DIR)/RebalanceSpec.vo $(COQ_DIR)/InsertDefs.vo $(COQ_DIR)/Tactics.vo
	$(COQC) $(COQFLAGS) $<
```

Fast iteration on RebalanceSpec.v and InsSpec.v won't trigger any
upstream rebuilds. Only the initial InsertDefs.v spec fix triggers
a one-time rebuild.

## Implementation Order

### Step 1: Foundation (one-time rebuilds)

1. Add `nodeFieldsR` + lemmas to Tactics.v (or new NodeFields.v)
   - `nodeFieldsR` definition
   - `treeR_node_to_fields`: split `treeR (Node ...)` into `nodeFieldsR ** subtrees`
   - `treeR_node_of_fields`: fold `nodeFieldsR ** subtrees` back into `treeR (Node ...)`

2. Fix specs in InsertDefs.v
   - Replace `setRebalanceLeft_spec` with field-level version
   - Replace `setRebalanceRight_spec` (mirror)
   - Keep Admitted proofs (unchanged in statement)

3. `make proofs` — verify insert_ok still compiles with new specs.
   (It should: insert_ok only uses `ins_ok`, whose spec `ins_spec` is unchanged.)

### Step 2: CalleeDefs.v

1. Extract function names for `is_black`, `is_red`, Node 5-arg constructor
2. `Eval vm_compute` for concrete Func records
3. `native_compute` lookup proofs
4. Formal specs for `is_black`, `is_red`, Node constructor
5. Admitted proofs for each (filled in Step 3/4)

### Step 3: RebalanceSpec.v — setRebalanceLeft_ok + setRebalanceRight_ok

1. Start with `setRebalanceLeft_ok` (default case first — simplest)
2. Add LL rotation case
3. Add LR rotation case
4. Mirror everything for `setRebalanceRight_ok`
5. Also prove `is_black_ok`, `is_red_ok` here (or in CalleeDefs.v)

### Step 4: InsSpec.v — ins_ok

1. Set up Löb induction
2. Base case (n == nullptr, new Node)
3. Recursive case k < n->key (with setRebalanceLeft)
4. Recursive case n->key < k (with setRebalanceRight)
5. Equal case (value update)

### Step 5: Cleanup

1. Remove Admitted from InsertDefs.v (replace with imports from new files)
2. Or: re-export proved lemmas so downstream files see them
3. Final `make proofs` — all green

## Risk Assessment

| Risk | Impact | Mitigation |
|------|--------|------------|
| `Node const*` type in is_black/is_red | Medium | Inline the functions instead of calling spec |
| `new Node(...)` wp handling unknown | Medium | Research BRiCk's Enew rules; worst case: Admit constructor and prove in Phase 6 |
| Löb induction for ins_ok unfamiliar | High | Study BRiCk examples (e.g., linked-list traversal proofs) |
| setRebalanceLeft rotation proofs tedious | Low | Mechanical; follow insert_ok's field-access pattern |
| Spec changes break insert_ok | Low | insert_ok only uses ins_spec (unchanged) |

## Open Questions

1. **nodeFieldsR location**: Tactics.v vs new file? Tactics.v is natural
   but triggers downstream rebuilds. A new NodeFields.v isolates changes
   but adds a file.

2. **is_black/is_red approach**: Spec + separate proof, or inline in
   setRebalanceLeft/Right proofs? Separate is cleaner; inline avoids
   `const` type issues.

3. **Node constructor**: Can we handle `new Node(...)` in BRiCk's wp
   framework for Phase 5B, or does it need to be Admitted?

4. **makeCopy inside setRebalanceLeft**: The LL and LR cases call
   `makeCopy(sub2)`. Since makeCopy_ok is Admitted, we can USE it as
   a callee spec. But the spec says input/output is a full treeR. Need
   to verify that sub2 (a subtree node) indeed has full treeR ownership
   when we reach the makeCopy call.

## Success Criteria

- `setRebalanceLeft_ok` : Qed
- `setRebalanceRight_ok` : Qed
- `ins_ok` : Qed
- `insert_ok` : Qed (still works)
- `make proofs` : exits 0
- Remaining Admitted: `makeCopy_ok` + framework gaps (Phase 6)
