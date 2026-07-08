# CLAUDE.md — working notes for this repo

Guidance for AI-assisted work on the BRiCk/Rocq proofs. See `README.md`,
`BUILDING.md`, and `TODO.md` for the project itself.

## Rocq proof iteration: diagnose, then fix (do NOT guess against full builds)

Building a proof file that `Require`s the cpp2v AST (`FindSpec.v`, `InsSpec.v`,
`InsertSpec.v`, `RebalanceSpec.v`) takes **~7 minutes** — it loads the 96K-line
`map_int_int_cpp.vo`. Guessing tactic fixes against that loop is fatally slow
and gives no clear signal at the failure point. Use this loop instead:

### 1. Get the exact goal at the failure point
Insert a proofmode goal dump right before the failing tactic:
```coq
match goal with |- ?g => idtac "PROOFMODE_GOAL:" g end;
```
(`Show` / `Show Proof` also work but only print when the file is processed.)
Build once, then read the `PROOFMODE_GOAL:` block from the log — it shows the
Iris context (hypotheses, incl. their exact `▷`/`_at`/fold state) and the goal.
This one build buys you the real signal; everything after is fast.

### 2. Reproduce in a *faithful* scratch (3-second loop)
Create `coq/ScratchH1.v` (or similar) that imports only
`RBTree`/`TreeRep`/`Tactics` — **NOT** the AST — so it compiles in ~3 s:
```
coqc -coqlib .brick-workspace/_build/install/default/lib/coq \
     -R coq daedalus_rb coq/ScratchH1.v
```
State a lemma whose goal, printed with the same `idtac`, is **character-identical**
to the real `PROOFMODE_GOAL:` dump. Getting the reduction/fold state to match is
the whole game — e.g. the goal may show `cv |-> as_Rep (λ this, …)` (the `_at`
not yet applied) while a hypothesis shows `∃ …, cv |-> (…)` (applied); they
differ by `_at_as_Rep`. If your scratch's goal doesn't match, adjust how you
build the hypotheses (`treeR_node_fold`, `iExists` with concrete vs evar
witnesses, `cbn [treeR]`, etc.) until it does.

### 3. Find the closing tactic in the scratch, then apply once to the real file.
Only rebuild the real (AST-loaded) file after the scratch closes.

### Gotchas learned the hard way
- **`treeR` is a `Fixpoint`.** `treeR q (Node c l k v r)` with *concrete*
  constructor args gets eagerly reduced to `as_Rep (…)` by Coq, so `rewrite
  treeR_node` may find "no subterm" (already reduced). With *evar* args it stays
  folded. Match the real state before choosing `rewrite treeR_node` vs
  `rewrite _at_as_Rep` vs nothing.
- **`iExact` is syntactic**, up to *definitional* but not up to `_at_as_Rep`
  application or `▷`-depth. `iApply` unifies a bit more but can't cross a `▷`
  (you cannot derive a bare `wand` from `▷ wand` without a `▷` in the goal).
- **Ltac scoping:** names bound by `destruct tc as [|c_tc …]` in one `Ltac`
  are NOT visible in a separate `Ltac` invoked via `ltac:(...)`. Thread them as
  parameters. Pure hyps introduced by `iDestruct (…) as "%H"` can't be named at
  parse time in a nested tactic — use `assumption`, not `exact H`.

## Build environment for iteration
The full pinned toolchain build is ~1 hr (`make setup`); it builds in-repo at
`./_opam` (opam switch) + `.brick-workspace/_build`. For a faster loop when
only the target file changes, keep the AST `.vo` + dependency `.vo`
(`map_int_int_cpp RBTree TreeRep WpTactics Tactics`) compiled in `coq/` so only
the target rebuilds. `.brick-workspace`, `_opam`, and all `.vo` are gitignored.
Each new shell: `eval $(opam env --switch=<repo-root> --set-switch)` and put
`.brick-workspace/_build/install/default/bin` + `/opt/homebrew/opt/llvm@19/bin`
on PATH.

### Fast goal inspection: preloaded coqtop (~1.4 s), NOT make (~7 min)
`coqtop` with the AST `.vo` preloaded gives instant goal dumps. Feed it a script
that `Require`s the AST once, starts the lemma, and prints goals with
`idtac "TAG:" g` / `Show` between tactics. This is the working fast loop.

> Note: an MCP-server route (LLM4Rocq/rocq-mcp) was trialled and dropped — its
> interactive `pet-server` path wouldn't pick up our `-R . daedalus_rb` load
> path in this dune-workspace layout. The preloaded-coqtop loop above is the
> workflow we use. (`pet`/coq-lsp finds its stdlib by locating a `rocq` binary
> on `PATH` — a useful fact if that route is ever revisited.)
