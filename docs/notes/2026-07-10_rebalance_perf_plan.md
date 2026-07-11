# RebalanceSpec build-performance plan (2026-07-10)

## Measured diagnosis (not guessed)

| What | Time |
|---|---|
| Load AST + deps (RBTree/TreeRep/Tactics/InsertDefs), trivial file | ~5 s |
| One `vm_compute` on a call's function type | ~0.004 s |
| `setRebalanceLeft_ok` prologue through `destruct c` (both cases admitted) | ~11.5 s |
| `IsBlackSpec.v` (2 small lemmas, 1 verified-callee call) | ~34 s (~5 load + ~29 proof) |
| `RebalanceSpec.v` (two ~1000-line lemmas, 35 call-resolvers) | ~70 min |

**Conclusion:** cost is ~entirely **Iris proof-term construction + Qed type-checking**,
scaling with proof volume. NOT fixed file overhead (5 s) and NOT `vm_compute`
(4 ms). The prologue is cheap; the *cases* are the entire cost.

## Why splitting is the right lever (and `abstract` is not enough)

- `abstract` (verified: works inside Iris proof mode) partitions one Qed into
  many opaque sub-terms — isolates errors, but runs in ONE process and Qed-checks
  the same total work, so it does not cut wall-time or give incremental rebuild.
- **Separate `.vo` files DO** give "smaller pieces replayed on demand":
  - editing one piece recompiles only that piece (coqc caches `.vo` per file);
  - `make -j` compiles independent pieces in parallel;
  - a per-case unit is ~30–90 s instead of the 70-min monolith.
- Nothing imports RebalanceSpec yet, so splitting is safe (no downstream breakage).
- The case-entry goal is fully determined by the (cheap) prologue and is
  capturable via an `idtac` goal-dump — so per-case lemma statements are feasible.

## Plan

### Step 1 — split by lemma into separate files (done first; low-risk, ~linear win)
- `coq/RebalanceDefs.v` — shared: the `setRebalanceLeft/Right_default` pure
  lemmas, the `wp_guard_isblack_true/false` Ltac (needs source/is_black_ok/MODULE,
  so lives in a Section here), and any shared notation. Imports InsertDefs +
  IsBlackSpec + Tactics. Small/fast.
- `coq/SetRebalanceLeft.v` — `setRebalanceLeft_ok` only.
- `coq/SetRebalanceRight.v` — `setRebalanceRight_ok` only.
Result: editing one rebalance fn no longer rebuilds the other; the two build in
parallel under `make -j`.

### Step 2 — per-case top-level lemmas (the real on-demand-replay fix)
Within each function's file, factor each default case into its own
`Lemma setRebalanceLeft_case_<name> : <case-entry goal> ` proved independently,
and make `setRebalanceLeft_ok` a thin driver: prologue → `destruct` →
`iApply`/`by` each case lemma. Statements captured via the goal-dump probe
(prologue is ~11 s, so capturing is cheap). Each case lemma compiles in isolation
(~30–90 s) and in parallel.

Design to keep statements short: define once
`Notation SRL_case c newL := (<the wp (Sif (Eseqand ..)) ..> goal)` or a
`Definition` of the case-entry proposition parameterised by
`(Q ρ n_ptr nl_ptr c k v lp rp rc r newL)`, so each `Lemma` statement is one line.

### Step 3 — proof-term-size reducers (compose with the above)
- Convert the big shared tails (`wp_srl_default`/`wp_srr_default`) and guard
  openers from Ltac (which INLINE a large term at each of 35 sites) into
  `Qed`-backed lemmas applied once — a lemma reference is O(1) in the caller's
  term vs. inlining ~30 steps. Likely the biggest per-proof shrink; measure it.
- Mark extraction defs (`*_func`) and helper lemmas `Opaque` where safe so Qed
  doesn't re-unfold them.

### Makefile / build hygiene
- Add the new files to `_CoqProject` + Makefile with correct deps; keep the
  `proofs` target. `make -jN` then parallelises.
- ALWAYS iterate new tactics in a ~3 s faithful scratch (RBTree/TreeRep/Tactics
  only), never against the full AST-loaded file.
