# Development notes (historical)

These are working notes captured during proof development. They are kept for
context on *why* the proof is structured the way it is, but they are **not**
maintained as current documentation — for the up-to-date picture see the
top-level [`README.md`](../../README.md).

Some notes predate the repository reorganization and refer to the old layout
(e.g. `daedalus-rb/brick/`, a `coq/` next to `ddl/`) or to intermediate plans
that were superseded (e.g. an `InsertStep10.v` scaffolding file that was never
created — the fast-iteration split landed as `coq/InsertDefs.v` instead).

| Note | Topic |
|---|---|
| `2026-02-13_brick_verification_plan.md` | Overall approach, phase breakdown, toolchain setup |
| `2026-02-20_fast_iteration_plan.md` | Splitting `InsertSpec.v` to cut rebuild time |
| `2026-02-22_phase5b_plan.md` | Proving the `insert` callees (`setRebalance*`, `ins`) |

See also [`../brick-framework-gaps.v`](../brick-framework-gaps.v): a
self-contained note (with `Admitted` lemma statements) describing two BRiCk
framework gaps encountered during the `insert` proof.
