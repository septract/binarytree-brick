# BRiCk framework gaps — upstream check & workaround analysis

**Date:** 2026-07-07
**Author:** review pass (read-only; no proofs or builds were run)
**Scope:** the two BRiCk framework gaps that form this project's trusted base,
documented as `Admitted` lemmas in `coq/WpTactics.v` and
`docs/brick-framework-gaps.v`.

This note answers two questions:

1. Is there progress on these gaps in the current BRiCk `main` (upstream)?
2. Are these *true* framework gaps, or could the proof have worked around them?

TL;DR: **Both gaps are still open on today's upstream `main`, and neither is a
self-inflicted wound — they sit on the only code path BRiCk offers for the
constructs involved.** Gap 1 (function alignment) has a clean, sound workaround
that BRiCk itself proposes but has not landed; Gap 2 (static initialization) has
no in-framework workaround and is a genuine missing feature.

---

## The two gaps (recap)

Both are stated as `Admitted` lemmas (deliberately **not** `Axiom`) in
`coq/WpTactics.v`:

- **Gap 1 — `wp_operand_cfun2ptr_global`** (WpTactics.v:829). Calling a global
  function `f(args)` forces the callee expression `Ecast Cfun2ptr (Eglobal f ty)`
  through `read_decl`, which demands
  `reference_to (Tfunction …) (_global f)`. `reference_to` needs
  `aligned_ptr_ty (Tfunction …)`, which needs `align_of (Tfunction …) = Some _`.
  BRiCk declares `align_of` as a bare `Parameter` with **no axiom for
  `Tfunction`**, so the chain cannot be discharged.
  *Used by:* `InsertSpec.v:77,83` (`insert` → `ins` call) and, transitively, the
  whole write path (Phases B–E in `TODO.md`).

- **Gap 2 — `wp_operand_read_global_const`** (WpTactics.v:872). Reading a global
  `const` (e.g. `Node::black = false`) forces
  `Ecast Cl2r (Eglobal name qty)`, which needs `initializedR` at the global's
  address to extract the stored value. `denoteModule` only provides `svalidR`
  (location validity); the value comes from `initSymbol`, which returns `emp`.
  *Used by:* `InsertSpec.v:108` (`wp_read_global_const … black_lookup …`).

---

## 1. Upstream status (checked against BRiCk `main`)

- Local pinned checkout: `fmdeps/BRiCk` @ `e2f29ae` (2026-02-13), recorded in
  `scripts/pins.env`. Both gaps are present verbatim in the pin.
- Upstream `SkyLabsAI/BRiCk` default branch `main` HEAD at review time:
  **`4a8ce6c`, pushed 2026-07-07** — roughly five months of commits past the pin.
  (Repo is public; verified via `gh api repos/SkyLabsAI/BRiCk`.)

### Gap 1 — function alignment: **still open**

`rocq-skylabs-brick/theories/lang/cpp/logic/wp.v` on `main` still carries the
identical design note (now at lines ~742–745), unchanged in substance:

```
(this rule has a problem with function references because there is no alignment for functions)
Two options:
1. functions have 1 alignment
2. there is a special rule for [has_type (Vref r) (Tref (Tfunction ..))] that ignores this
```

`semantics/types.v` on `main` still has **no** `align_of` axiom mentioning
`Tfunction` (it has axioms for `Tnamed`, `Tarray`, `Tnum`, `Tchar`, `Tptr`, …
but not functions). Neither of the two proposed fixes has landed. The file did
see later commits (through 2026-06-17) but none add function alignment.

### Gap 2 — static initialization: **still open, and explicitly tracked**

`logic/translation_unit.v` on `main` still defines `initSymbol` returning `emp`
for the `Ovar t (global_init.Init e)` case, with the same
`todo(gmm): static initialization is not yet supported` and a commented-out
`wp_init`-based sketch. The `translation_unit.v` file has only been touched by
repo-wide renames (`bluerock`→`skylabs`) since the pin — no semantic change.

This gap is **acknowledged upstream** in issue
[#154 "List of blockers for using BRiCk on BRiCk"](https://github.com/SkyLabsAI/BRiCk/issues/154)
(open, updated 2026-05-20), which lists under "Class 3: BRiCk logic / semantics
gaps":

> **Translation-unit / global initialization** — BRiCk docs list translation-unit
> initialization as roadmap-only, and the current TU semantics file still says
> static initialization is not yet supported.
> *(evidence: `translation_unit.v:96-106`)*

No open PR was found addressing either gap.

**Conclusion for (1):** the pins are not stale on these points — upgrading to
current `main` would not close either gap.

---

## 2. Are these true gaps, or could we have worked around them?

### Gap 1 — true gap, but with a sound, framework-side fix (not a user workaround)

The project's approach is *not* the problem. The standard call rule
`wp_call` (`logic/expr.v` on `main`, def. ~line 1167) evaluates the callee with

```
let eval_f Q := wp_operand f (fun v fr => Exists fp, [| v = Vptr fp |] ** Q fp fr) in
```

For a global function, `f` is `Ecast Cfun2ptr (Eglobal …)`, and
`wp_operand_cast_fun2ptr_cpp` (expr.v ~773) reduces it to `wp_lval` on the
`Eglobal`, i.e. `wp_lval_global` → `read_decl` → `reference_to (Tfunction …)`.
**This is the only path BRiCk provides for evaluating a named-function callee**,
and it unavoidably hits the missing `align_of (Tfunction …)`. There is no
alternate lemma the project could have used instead — hence a genuine framework
gap, not a modeling mistake.

Could a *user* work around it inside this repo? Only by adding an axiom about
`align_of (Tfunction …)`, which is exactly what the `Admitted` lemma already
encapsulates (and doing it as a local `Axiom` would be strictly worse — the
current `Admitted` at least keeps it visible to `Print Assumptions` as an
incomplete proof rather than a trusted axiom).

Is the eventual fix sound? Yes. BRiCk's own option 1 — "functions have 1
alignment" — is sound: `aligned_ptr_ty ty p` unfolds to
`∃ a, align_of ty = Some a ∧ aligned_ptr a p`, and with `a = 1` every pointer is
1-aligned (`1 | va` always). Nothing else constrains `align_of (Tfunction …)`
(`size_of (Tfunction _) = None`, so the `align_of_size_of'` axiom that ties
alignment to size is vacuous for functions). So an `align_of_function : align_of
(Tfunction …) = Some 1` axiom would make `wp_operand_cfun2ptr_global` provable
with no unsoundness. The lemma is therefore a faithful placeholder for a fix
that is known-sound and merely unimplemented upstream.

**Verdict:** true framework gap; unavoidable on BRiCk's only call path; the
`Admitted` lemma is semantically valid and will discharge once upstream adds the
(sound) 1-alignment axiom.

### Gap 2 — true gap, no in-framework workaround

Reading an lvalue global of primitive type must go through `wp_operand_cast_l2r`,
which requires `initializedR` (the stored value) at the location. The only
source of a global's contents is `initSymbol`, which returns `emp` for
initialized globals. There is **no** lemma in BRiCk that yields `initializedR`
for a statically-initialized global from `denoteModule` — the value simply is
not modeled yet. So there is no path, standard or otherwise, and no sound
user-level workaround: the value literally cannot be recovered from what
`denoteModule` provides.

Note the placeholder lemma is **weaker/looser than the eventual real rule**: it
quantifies `v` universally and unconstrained by `init` (see the caveat in
`docs/brick-framework-gaps.v` and WpTactics.v:872). This is only safe because
the project always instantiates `v` with the concrete initializer value
(`Vbool false` for `black`); a real `initSymbol` would *tie* `v` to the
initializer. This is the one place where the trusted base is genuinely
"trust me" rather than "provable-once-upstream-lands-a-known-sound-axiom", so it
deserves the most scrutiny when the fix arrives.

Is the specific use sound in practice? Yes for this codebase: `Node::black` /
`Node::red` are `static const bool` with literal initializers, so the concrete
`v` the proof supplies matches what any correct static-init model would produce.
But that soundness rests on manual instantiation, not on the framework.

**Verdict:** true framework gap (a missing feature, roadmap-tracked in #154);
no workaround exists; the placeholder is sound *for the way this project uses
it* but is looser than the real rule will be.

---

## Practical implications for this repo

- Neither gap will be closed by bumping the BRiCk pin to current `main`; the
  `TODO.md` Phase A "real fix" (A1c) remains blocked on upstream.
- The **highest-leverage upstream ask** is Gap 1's 1-alignment axiom: it is
  known-sound, tiny, and unblocks the entire write path (Phases B–E). It is a
  reasonable candidate to propose upstream (or to carry as a clearly-labeled
  local axiom with this soundness argument attached) rather than waiting.
- Gap 2 is a larger upstream feature (static-init semantics) with no shortcut.
  Its blast radius here is small and well-contained (two boolean constants), so
  the pragmatic path is to keep the `Admitted` placeholder but tighten it to
  constrain `v` to the initializer as soon as `initSymbol` gains any content —
  and to keep it out of `findNode_ok`'s dependency set (it already is; see the
  proof-state note).
- Recommend wiring the `TODO.md` `Print Assumptions` audit (A1b / H2) so these
  two `Admitted`s remain the *entire* trusted base and cannot silently grow.

## Addendum — can these be closed locally, and *why* do they remain?

### Gap 1: closeable locally with a one-line axiom; remains open for a semantic reason

The full dependency chain for a global-function call is:

```
reference_to (Tfunction …) p                                    -- what read_decl needs
  ⇐ reference_to_intro : strict_valid_ptr p                     -- ✓ code_at_strict_valid gives this
                       ** has_type (Vptr p) (Tptr (Tfunction …)) -- = valid_ptr p ** aligned_ptr_ty (Tfunction …) p
  ⇐ aligned_ptr_ty (Tfunction …) p                              -- = ∃a, align_of (Tfunction …) = Some a ∧ aligned_ptr a p
```

Everything except `align_of (Tfunction …) = Some _` is already provable —
`code_at` (which `denoteModule` yields for a defined function) gives
`strict_valid_ptr`, and from `strict_valid_ptr` + the alignment fact
`reference_to_intro` closes the goal. **The sole missing ingredient is one
alignment fact.** So Gap 1 *can* be closed inside this repo (or upstream) by
adding a single axiom:

```coq
Axiom align_of_function : ∀ cc ar ret args,
  align_of (Tfunction (FunctionType (ft_cc:=cc) (ft_arity:=ar) ret args)) = Some 1%N.
```

and then proving `wp_operand_cfun2ptr_global` for real (no `Admitted`). This is
sound: `aligned_ptr 1 p` holds for every `p` (`1 | va` always), and no other
axiom constrains `align_of` of a function (`size_of (Tfunction) = None`, so the
`align_of_size_of'` axiom that normally ties alignment to size is vacuous here).

**Why it remains open upstream is a genuine (mild) semantic question, exactly as
suspected.** In C++, a function type is *not an object type*: `alignof` applied
to a function type is ill-formed ([expr.alignof]), and `sizeof` of a function is
likewise ill-formed ([expr.sizeof]) — which is why BRiCk faithfully sets
`size_of (Tfunction) = None`. So there is **no standard-sanctioned value** for
"the alignment of a function type"; picking `1` is inventing a number the
language does not define. That is precisely why the BRiCk authors left it as an
open comment with two options rather than just adding the axiom:

- **Option 1 ("functions have 1 alignment")** — the one-line axiom above. Cheap,
  sound, but slightly abuses `align_of` by giving a function type an alignment
  the standard doesn't define. Harmless because function *pointers* are only ever
  compared/called, never used for object-alignment reasoning.
- **Option 2 ("special-case `has_type (Vref r) (Tref (Tfunction ..))`")** — the
  cleaner fix: make function-designator lvalues bypass the alignment machinery
  entirely. But `reference_to` is defined (and its `reference_to_elim` axiom
  states) to *always* carry `aligned_ptr_ty ty p`; teaching it to skip that for
  function types means forking the definition and revisiting every consumer.
  That is a design change with ripples, not a local patch.

So: it lingers not because it's hard, but because the tidy fix touches a core
invariant and the cheap fix asserts something the C++ standard leaves undefined —
neither is a slam-dunk, so it sits as a documented TODO. For *this* project the
cheap axiom is entirely adequate and is the recommended way to close the gap
without waiting on upstream.

### Gap 2: not closeable as a local patch; remains open because it is unbuilt semantics

Gap 2 is a different animal. There is no "one missing fact" — the value of a
statically-initialized global is simply *not represented*. `initSymbol` would
have to actually run the initializer (`wp_init … e Q`) at module-denotation time
and hand back `Q`'s resource, i.e. produce `initializedR`/`primR` at the
global's location. The commented-out sketch in `translation_unit.v` shows the
authors know the intended shape, but filling it in drags in real design work:

- **static vs. dynamic initialization** and initialization *order* (including
  across translation units) — which initializers are constant-expressions
  evaluated at "compile time" vs. run as dynamic init;
- **`constinit`/`constexpr`** guarantees vs. ordinary dynamic init;
- **function-local `static`** guard variables (thread-safe one-time init);
- threading a `wp_init` (a spatial, stateful evaluation) through
  `denoteModule`, which is currently *persistent* — mixing those layers is the
  crux of why the sketch is commented out rather than finished.

None of this can be faked locally without essentially asserting the value out of
thin air (which is what the current placeholder does, and why its `v` is
unconstrained). It is roadmap-tracked upstream (issue #154, "translation-unit /
global initialization"). For this repo the blast radius is tiny — two
`static const bool` constants — so the pragmatic stance is to keep the
placeholder but tighten it to pin `v` to the initializer the moment `initSymbol`
gains any content.

### Gap 2, target-side workaround: eliminate the const read by minor C++ surgery

There is a *fourth* option for Gap 2 that avoids both BRiCk changes and the
`Admitted` placeholder: **change the target so the global-const read never
occurs.** The gap only fires because `Node::black` / `Node::red` are
`static const Color` members that are *read* as globals — in the generated AST
this is `Ecast Cl2r (Eglobal Node::black (Qconst Tbool))`
(`coq/map_int_int_cpp.v:32785,32792`). But the constants are trivial
(`map.h:32-33`):

```cpp
using Color = bool;
static const Color red   = true;
static const Color black = false;
```

and every use is either a comparison (`n->color == black`, map.h:90) or an
rvalue in an assignment (`curr->color = black`, map.h:100,164,…). Replacing the
named constants with their literals at the use sites (`black`→`false`,
`red`→`true`), or making them `constexpr`/an `enum` that folds to a literal,
removes every `Eglobal` const read from the tree code. The AST then contains
only `Ebool false` / `Ebool true`, which `wp` evaluates natively — and **Gap 2
disappears for this target with no trusted axiom at all.**

Why this is sound and cheap:

- Behaviour-preserving by construction: `Color` *is* `bool` and the constants
  are literally `false`/`true`; the compiled semantics are identical.
- Confined to `cpp/ddl/map.h` — no BRiCk fork, no local axiom.
- Cost is a small *fidelity* note (we verify a source that inlines two named
  constants rather than the verbatim upstream), which is a far smaller ask than
  the current unconstrained-`v` admit — arguably nil, since the substitution is
  mechanical and obviously equivalent.

Note this trick is **specific to Gap 2 and to constants this simple**. It does
*not* generalize to Gap 1: `ins` / `setRebalance*` / `makeCopy` are genuine
recursive calls that must be modeled, so the function-call gap still needs the
(sound) `align_of_function` axiom or an upstream fix — you cannot make those
calls "go away" by editing the source.

### One-line answers

- **Can they be closed locally?** Gap 1: **yes** — add the sound
  `align_of_function = Some 1` axiom and discharge the lemma (`code_at` already
  supplies the rest). Gap 2: **no** — it needs real static-initialization
  semantics in BRiCk, not a local lemma.
- **Why do they remain?** Gap 1: the standard doesn't define alignment for
  function types, so the clean fix touches a core `reference_to` invariant and
  the cheap fix asserts an undefined-by-C++ value — a real (if minor) design
  choice. Gap 2: static initialization is genuinely unimplemented framework
  semantics (order/constexpr/persistent-vs-spatial), tracked on the roadmap.

## Sources

- Local pin: `scripts/pins.env`, `fmdeps/BRiCk@e2f29ae`.
- Upstream `main@4a8ce6c` (2026-07-07): `logic/wp.v`, `semantics/types.v`,
  `semantics/ptrs.v`, `logic/expr.v`, `logic/translation_unit.v`.
- Issue [SkyLabsAI/BRiCk#154](https://github.com/SkyLabsAI/BRiCk/issues/154).
- This repo: `coq/WpTactics.v` (lines 829, 872), `docs/brick-framework-gaps.v`,
  `coq/InsertSpec.v` (77, 83, 108).
