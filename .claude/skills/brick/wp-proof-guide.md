# BRiCk wp Proof Guide

Patterns and techniques for writing weakest-precondition proofs against
cpp2v-generated C++ ASTs using BRiCk's core library (`skylabs.lang.cpp.*`).

## Proof Structure

A `func_ok` proof has this skeleton:

```coq
Lemma myFunc_ok :
  |-- func_ok source myFunc_func myFunc_spec.
Proof.
  rewrite /func_ok. iSplit.
  - iPureIntro. reflexivity.          (* type agreement *)
  - iIntros "!>" (Q vals) "Hspec".
    iApply wp_func_intro.
    rewrite /myFunc_func /=.          (* unfold function body *)
    (* 1. extract arguments from Hspec *)
    iDestruct "Hspec" as (pv v ...) "(%Hvals & Harg1 & ... & Hspec)".
    subst vals. simpl.
    iDestruct "Hspec" as (ghost_vars ...) "(%Hargs & Hresource & Hcont)".
    injection Hargs as -> ->. subst.
    (* 2. step through the function body *)
    wp_auto.
    ...
Qed.
```

The proof then walks through the C++ AST step by step. Each C++ construct
has a corresponding wp rule.

## Two Kinds of Steps

### Mechanical Steps (automatable)

These are purely syntactic — match the AST constructor, apply the wp rule:

| C++ Construct | Tactic |
|---------------|--------|
| `{ s1; s2; }` (sequence) | `iApply wp_seq` |
| `break` | `iApply wp_break` |
| `return expr` | `iApply wp_return` |
| Expression statement | `iApply wp_expr` |
| Block entry | `rewrite wp_block_eq /wp_block_def` |
| Variable declaration | `rewrite wp_decls_eq /wp_decls_def /=` |
| Variable init | `rewrite /wp_initialize /qual_norm /=` then `rewrite wp_initialize_unqualified.unlock /=` |
| Discard expr result | `rewrite /wp_discard /=` |
| Temporary destruction | `rewrite interp_unfold /=` |
| While unroll | `rewrite /while_unroll` |
| Loop structure | `rewrite /Kloop /Kloop_inner /=` |
| Return cleanup | `rewrite /Kfree /Kat_exit /Kcleanup /Kreturn /Kreturn_inner /=` |
| Modality stripping | `iModIntro` or `iNext` |

`wp_step` tries these in priority order; `wp_auto` repeats until stuck.

**Priority order**: Statement wp rules → block/decl unfolding → expression
rules → interp unfolding → continuation unfolding → modality stripping.
Modalities are last because they appear between every step — trying them
first would mask the actual wp rule.

### Semantic Steps (require user input)

| Task | Approach |
|------|----------|
| Loop invariant | `iApply (wp_while_inv tu Inv)` |
| If/else | `iApply (wp_if tu)` |
| Binary operator | `iApply (wp_operand_binop tu)` + nd_seq |
| Read local variable | l2r cast → var lookup → reference_to → value provision |
| Field access (p->f) | l2r → member → arrow → reference_to → offset → value |
| Assignment | Evaluate RHS → lval target → reference_to → anyR for old |
| Function call | call → Cfun2ptr → nd_seqs args → wp_fptr resolution |
| eval_binop | Case-specific (see Pointer/Integer Comparisons below) |
| Resource framing | `iFrame`, `iSplitL`, `iSplitR`, `iExists` |
| Case splitting | `destruct` on abstract model to match C++ branches |

## Modality Dance

Between every pair of wp steps, BRiCk inserts modalities (`|={⊤}=>`, `▷`,
`|={⊤}▷=>`). Strip them before the next rule can fire:

```coq
wp_auto.           (* handles sequences of iModIntro/iNext *)
(* or manually: *)
iModIntro. iNext. iModIntro.
```

## Function Extraction from cpp2v AST

**Never hand-transcribe AST fragments.** A proof about a hand-copied AST
proves nothing about the actual C++ code.

### Pattern

```coq
(* 1. Symbol table key *)
#[local] Open Scope pstring_scope.
Definition myFunc_name : obj_name :=
  Nscoped _MyClass_name
    (Nfunction function_qualifiers.N "myFunc"
      (Tint :: Tptr _MyClass :: nil)).
#[local] Close Scope pstring_scope.

(* 2. Extract function via computation *)
Definition myFunc_func : Func :=
  match source.(symbols) !! myFunc_name with
  | Some (Ofunction f) => f
  | _ => {| f_return := Tvoid; f_params := nil; f_cc := CC_C;
            f_arity := Ar_Definite; f_exception := exception_spec.NoThrow;
            f_body := None |}
  end.

(* 3. Machine-check the lookup *)
Lemma myFunc_lookup :
  source.(symbols) !! myFunc_name = Some (Ofunction myFunc_func).
Proof. native_compute. reflexivity. Qed.

(* 4. Prove body exists (needed for code_at) *)
Lemma myFunc_has_body : exists body, myFunc_func.(f_body) = Some body.
Proof. vm_compute. eexists. reflexivity. Qed.
```

If `native_compute; reflexivity` compiles, the name correctly identifies
the function. If wrong, Coq reports a type error.

### Finding the Name

Search the cpp2v-generated `_names.v` for the function name. Static methods
are stored as `Ofunction (static_method m)`. Names are typically
`Nscoped class_name (Nfunction qualifiers "name" param_type_list)`.

## Function Call Resolution

When a wp proof reaches `f(args)`, resolution needs three persistent facts:

1. **`denoteModule tu`** → `code_at tu f p` (via symbol table lookup)
2. **`code_at tu f p`** → `wp_func tu f ls Q -* wp_fptr ... ls Q` (via `code_at_ok`)
3. **`func_ok tu f spec`** → `spec.(fs_spec) vals Q -* wp_func tu f vals Q` (callee proof)

### One-Liner

```coq
wp_call_direct "HMOD" myFunc_lookup myFunc_has_body myFunc_ok myFunc_func.
```

After this, the goal is `fs_spec myFunc_spec vs Q` — provide the
function's precondition from spatial resources.

### Setup

The proof section needs `denoteModule` as a persistent hypothesis:

```coq
Section with_Sigma.
Context `{Sigma : cpp_logic} `{MOD: my_cpp.source ⊧ σ}.
Hypothesis MODULE : |-- denoteModule source.
(* ... *)
iPoseProof MODULE as "#HMOD".
```

### Cfun2ptr for Function Expressions

Before `wp_call_direct`, the proof must resolve `Ecast Cfun2ptr (Eglobal name ty)`.
This hits a known BRiCk gap (no `align_of` axiom for `Tfunction`). Use:

```coq
iApply (wp_operand_cfun2ptr_global _ _ _ _ _ _ myFunc_lookup myFunc_has_body).
iSplitL "HMOD"; [iExact "HMOD" |].
```

This lemma is Admitted due to the upstream gap — semantically valid but
formally blocked on BRiCk's alignment axiom for functions.

### Full Call Sequence

```coq
(* 1. Enter call *)
iApply wp_operand_call.
rewrite /wp_call /=.
iIntros "%_".  (* discharge source ⊧ σ *)
rewrite /wp.WPE.Mbind /wp.WPE.Mmap /=.

(* 2. Resolve function expression *)
iApply (wp_operand_cfun2ptr_global _ _ _ _ _ _ lookup has_body).
iSplitL "HMOD"; [iExact "HMOD" |].
iExists (_global func_name).
iSplit; [iPureIntro; reflexivity |].

(* 3. Evaluate arguments (all orderings) *)
wp_nd_args ltac:(first [
  wp_read_local "Harg1" (Vint x) |
  wp_read_local "Harg2" (Vptr p)
]).

(* 4. Resolve wp_fptr → spec precondition *)
all: wp_call_direct "HMOD" lookup has_body callee_ok callee_func.

(* 5. Provide spec precondition *)
all: rewrite /callee_spec. all: simpl.
all: iExists ...; iSplit; [iPureIntro; reflexivity |]; iFrame.
```

## Argument Evaluation (nd_seqs)

C++ has unspecified argument evaluation order. BRiCk's `nd_seqs` requires
proving correctness for ALL orderings (N! branches for N arguments).

```coq
wp_nd_args ltac:(first [
  wp_read_local "Harg1" (Vint x) |
  wp_read_local "Harg2" (Vptr p) |
  wp_read_local "Harg3" (Vint y)
]).
```

`first [...]` tries each argument's evaluation tactic at each position.
For 3 args, generates 6 branches — all solved by the same dispatch.

After `wp_nd_args`, use `all:` to apply the same tactic across all branches.

For binary operators, `nd_seq` has just 2 orderings:
```coq
iApply (wp_operand_binop tu).
rewrite /nd_seq.
iSplit; [ eval_a; eval_b; kont | eval_b; eval_a; kont ].
```

## Loop Proofs (wp_while_inv)

### Invariant Structure

```coq
iApply (wp_while_inv tu (
  Exists (x : T) ...,
    local_p |-> tptsto_fuzzyR ty (cQp.m 1) (Vptr x) **  (* local vars *)
    param_p |-> tptsto_fuzzyR ty (cQp.m 1) (Vint k) **  (* parameters *)
    x |-> myRep q current_data **                         (* current data *)
    [| f(original) = f(current_data) |] **                (* correspondence *)
    (x |-> myRep q current_data -* root |-> myRep q t) ** (* magic wand *)
    postcondition_handler)%I).
```

### What Must Be in the Invariant

Iris linear logic requires **every spatial resource** to be accounted for.
Include:

1. **All local variables** (`tptsto_fuzzyR`)
2. **All parameters** (`tptsto_fuzzyR`)
3. **Current data resource** (rep predicate at current position)
4. **Pure correspondence** linking current to original
5. **Magic wand** for reconstruction (see below)
6. **Postcondition handler** if any exit path (break, return) needs it

### Magic Wand Zipper

For traversal (search/walk), the magic wand captures "how to plug the
current subtree back into the full structure":

```coq
(* Initial: identity wand *)
iIntros "H". iExact "H".

(* After descending left: wand captures parent + right sibling *)
iIntros "Hleft_back".
iApply "Hwand".       (* compose with outer wand *)
iExists lp, rp, rc.
iFrame "Hleft_back Hright_sibling Hfield1 Hfield2 ...".
```

Each iteration extends the wand by one level.

### Two Proof Obligations

1. **Inductive step**: `I ⊢ while_unroll ...` — given invariant, process
   one iteration (evaluate condition, execute body or break).
2. **Initial establishment**: provide invariant from current context
   (typically current pointer = original, identity wand).

## Local Variable Lifecycle

### 1. Declaration

```coq
rewrite wp_block_eq /wp_block_def.
rewrite wp_decls_eq /wp_decls_def /=.
iModIntro. iNext.
iIntros (addr).    (* fresh address *)
rewrite /wp_initialize /qual_norm /=.
rewrite wp_initialize_unqualified.unlock /=.
(* evaluate initializer → produces tptsto_fuzzyR *)
```

### 2. Reading (`wp_read_local`)

```coq
(* Pattern: Ecast Cl2r (Evar "name" ty) *)
iApply wp_operand_cast_l2r.
rewrite /wp_glval /=.
iApply wp_lval_var.
rewrite /read_decl /_local /=.
(* observe reference_to from tptsto_fuzzyR *)
iDestruct (observe (reference_to _ _) with "H") as "#_ref".
iFrame "_ref". iClear "_ref".
iExists v.
iSplit.
- iExists (cQp.m 1).
  rewrite _at_initializedR.
  iDestruct (observe (has_type_or_undef _ _) with "H") as "#_hty".
  iRevert "_hty". rewrite has_type_or_undef_unfold.
  iIntros "[_htmp | %_habs]"; [iFrame "H"; iExact "_htmp" | discriminate].
- (* continuation *)
```

Or use the composite tactic: `wp_read_local "H" (Vint x)`.

### 3. Assignment

```coq
iApply wp_lval_assign.
(* evaluate RHS first *)
...
(* then resolve LHS: *)
iApply wp_lval_var.
rewrite /read_decl /_local /=.
wp_observe_ref "H_local".                  (* reference_to *)
iSplitL "H_local"; [wp_finish_anyR |].    (* old value → anyR *)
iIntros "H_new".                           (* new tptstoR *)
(* convert: *)
iDestruct (tptstoR_to_fuzzyR with "H_new") as "H_new".
```

### 4. Destruction (scope exit)

```coq
destroy_val_unfold.
rewrite wp_destroy_prim.unlock /=.
iModIntro.
iSplitL "H".
- iRevert "H". rewrite _at_tptsto_fuzzyR.
  iIntros "Htmp".
  iDestruct "Htmp" as (v) "[% Htpsto]".
  iExists v. rewrite _at_tptstoR. iExact "Htpsto".
- (* continuation *)
```

For arg temporaries with `anyR`: `iApply anyR_wp_destroy_prim_val; [done |]`.

## Field Access (ptr->field)

### Read Pattern

```coq
(* p->field where p is read from a local variable *)
(* 1. l2r cast + member + arrow *)
wp_member_access.

(* 2. Read the pointer from local *)
wp_read_local "Hlocal" (Vptr p).

(* 3. Observe reference_to from struct identity *)
wp_observe_ref "Hstruct".

(* 4. Navigate to field *)
rewrite /read_decl /=.
wp_offset "Hfield".           (* p |-> (f |-> R) → (p,,f) |-> R *)

(* 5. Observe reference_to from field, provide value *)
wp_observe_ref "Hfield".
wp_provide_value "Hfield" (Vint x).
```

Or use the composite: `wp_struct_field "Hstruct" "Hfield" (Vint x)`.

### Offset Conversion

```coq
(* Nest: p |-> (f |-> R) → (p,,f) |-> R *)
wp_offset "H".
(* equivalent to: *)
iDestruct (at_offsetR_intro with "H") as "H".

(* Unnest: (p,,f) |-> R → p |-> (f |-> R) *)
wp_revert_offset "H".
(* equivalent to: *)
iRevert "H". rewrite -_at_offsetR. iIntros "H".
```

You often need `wp_revert_offset` before folding a rep predicate back
together (the rep expects the nested-offset form).

## Pointer Comparisons

### Null self-comparison (`nullptr != nullptr` → false)

```coq
iPoseProof valid_ptr_nullptr as "_pvn".
iPoseProof (eval_ptr_self_eq tu cls nullptr with "_pvn") as "_peq".
iPoseProof (eval_ptr_neq tu cls nullptr nullptr true with "_peq")
  as "[_pimp _ptrue]".
rewrite /eval_binop.
iFrame "_ptrue". iRight. iExact "_pimp".
```

Or: `wp_eval_ptr_neq_null tu _MyClass`.

### Non-null comparison (`p != nullptr` → true)

Requires: `p <> nullptr` (pure), `valid_ptr p` (persistent).

```coq
match goal with Hne : ?p <> nullptr |- _ =>
  iPoseProof (eval_ptr_nullptr_eq_l tu
    (fun _ => bool_decide_eq_false_2 (p = nullptr) Hne)
    with "Hvalid") as "_peq"
end.
iPoseProof (eval_ptr_neq tu cls p nullptr false with "_peq")
  as "[_pimp _ptrue]".
rewrite /eval_binop.
iFrame "_ptrue". iRight. iExact "_pimp".
```

Or: `wp_eval_ptr_neq_nonnull tu _MyClass "Hvalid"`.

### Integer less-than (`x < y`)

Requires: `has_type_or_undef (Vint x) Tint` (persistent, via observe).

```coq
iExists (Vbool (bool_decide (x < y)%Z)).
iSplit.
- iSplitR; [| done].
  rewrite /eval_binop. iLeft.
  iRevert "Hty". rewrite has_type_or_undef_unfold.
  iIntros "[H | %Habs]"; [| discriminate].
  iDestruct (has_type_has_type_prop with "H") as "%Htp".
  iPureIntro.
  eapply eval_lt; [solve [typeclasses eauto] | done | assumption | assumption].
- destruct (bool_decide (x < y)%Z) eqn:Hcmp; ...
```

Or: `wp_eval_int_lt "Hty"`. For other ops: `wp_eval_int_binop "Hty" eval_le`.

## Bottom-Up Proof Strategy

When verifying a call chain (e.g., `insert` → `ins` → `makeCopy`):

1. **State specs** for all functions.
2. **Admit leaf functions** (`makeCopy_ok : Admitted`).
3. **Prove the top-level function** using admitted specs as axioms.
4. **Fill in admitted proofs** incrementally, deepest first.

This validates the overall structure before investing in the hardest
sub-proofs. Each `Admitted` is a clear TODO.

**Critical**: Never use `Axiom`, `Parameter`, or `Conjecture`. Only
`admit`/`Admitted` for work-in-progress proofs.

## Rep Predicate Unfold/Fold

### Unfolding a Node

```coq
(* Convert p |-> treeR q (Node ...) to field hypotheses *)
iRevert "H". rewrite _at_as_Rep. iIntros "H".
iDestruct "H" as (child_ptrs rc) "(Hchild1 & Hchild2 & Hfields)".
iDestruct "Hfields" as "(Hf1 & Hf2 & ... & Hstruct)".
```

### Folding Back

```coq
(* Reassemble from field hypotheses *)
iExists child_ptrs, rc.
iFrame "Hchild1 Hchild2 Hf1 Hf2 ... Hstruct".
```

Before folding, use `wp_revert_offset` on any field hypothesis that was
flattened by `wp_offset` during the proof body.

### Extracting Pure/Persistent Facts from Nodes

Without consuming the resource:

```coq
(* p <> nullptr *)
iDestruct (myRep_node_nonnull with "H") as "[H %Hne]".

(* valid_ptr p *)
iDestruct (myRep_node_valid with "H") as "[H #Hvalid]".
```

These pattern lemmas (proved once per rep predicate) avoid repeatedly
unfolding/refolding just to extract a single fact.

## Debugging Tips

1. **Goal too opaque**: `rewrite /= /myFunc_func` or `vm_compute` to
   force reduction of AST terms extracted from the symbol table.

2. **`iApply` fails with unification error**: The goal's function type
   may not match. Use `change ft with (type_of_value (Ofunction func_def))`
   before `iApply` to help Coq's unifier.

3. **Modality stuck**: If a wp rule won't fire, there's likely an
   unstripped `|={⊤}=>` or `▷`. Try `iModIntro` or `iNext`.

4. **`wp_auto` loops**: It shouldn't (each step makes progress), but if
   it does, switch to manual `wp_step` to identify the stuck point.

5. **nd_seqs branches differ**: After `wp_nd_args`, the N! branches have
   different temporary pointer orderings. Use `all:` to apply uniform
   tactics, and `lazymatch goal` when pointer order matters.

6. **`native_compute; reflexivity` fails for lookup**: The function name
   is wrong. Double-check the mangled name in `_names.v`.

7. **Scoping**: Use `#[local] Open/Close Scope pstring_scope` around AST
   name definitions to avoid conflicts with Iris's `%I` notation scope.
