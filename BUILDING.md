# Building

This repository has two independent build trees:

- **`lean/`** — a Lean 4 project (fast, self-contained, no external deps).
- **`coq/`** — Rocq (Coq) proofs against [BRiCk](https://github.com/SkyLabsAI/BRiCk),
  which must be built from source (the slow part).

You can build either half on its own.

---

## Lean (`lean/`)

The only prerequisite is [`elan`](https://github.com/leanprover/elan), the Lean
toolchain manager. It reads `lean/lean-toolchain` and fetches the exact Lean
version automatically (currently `leanprover/lean4:v4.27.0`).

```bash
cd lean
lake build          # build the library + proofs
lake exe rbtree     # run the runtime demo / sanity-test harness (Main.lean)
```

There are no external package dependencies (`lake-manifest.json` is empty), so
the build is hermetic once `elan` has the toolchain. A clean build takes well
under a minute.

---

## Rocq / BRiCk (`coq/`)

The proofs are checked with:

| Tool | Version |
|---|---|
| Rocq Prover (Coq) | **9.1.0** (built from vendored source) |
| OCaml | **5.4.0** (installed into a local opam switch) |
| dune | 3.21.0 |
| opam | ≥ 2.2.1 |
| Clang / LLVM | 18–21 (recommended 19) — `cpp2v` links against `libclang` |

BRiCk is **not** published on opam, and the prebuilt workspace container image
is not anonymously pullable, so the toolchain is built from source out of the
public [`SkyLabsAI/workspace`](https://github.com/SkyLabsAI/workspace) meta-repo.
The exact known-good commits are pinned in
[`scripts/pins.env`](scripts/pins.env).

### 1. Install host prerequisites

On macOS (Homebrew):

```bash
brew install opam cmake llvm gnu-sed bash
```

> Apple Clang will **not** work — `cpp2v` needs the `libclang` development
> headers that only the Homebrew/LLVM `clang` ships. Make sure the Homebrew
> `clang` is ahead of Apple's on your `PATH`.

On Debian/Ubuntu: install `opam cmake clang-19 libclang-19-dev` and ensure a
recent `bash` and GNU `sed` (both are default).

Check your host without cloning or building anything:

```bash
make check
```

### 2. Build the toolchain (~30–60 min, first run only)

```bash
make setup
```

This runs [`scripts/setup-brick-workspace.sh`](scripts/setup-brick-workspace.sh),
which:

1. Clones `SkyLabsAI/workspace` into `.brick-workspace/` (gitignored),
2. Clones its **public** sub-repos (`make clone-public`),
3. Checks out the pinned commits from `scripts/pins.env`
   (the workspace tracks moving branch heads, so pinning is what makes the
   build reproducible),
4. Creates the opam switch, installs dependencies, and builds Rocq + `cpp2v` +
   the BRiCk theories.

The script is idempotent — re-running it skips completed steps.

### 3. Activate the toolchain

The build produces binaries under `.brick-workspace/_build/install/default/`.
The top-level `Makefile` points at them directly, but you still need the opam
environment on your `PATH` in each new shell:

```bash
source .brick-workspace/dev/activate.sh
```

### 4. Generate the AST and build the proofs

```bash
make cpp2v      # run cpp2v on cpp/src/map_int_int.cpp -> coq/map_int_int_cpp*.v
make ast        # compile the ~96K-line generated AST (slow: ~30-60 min)
make proofs     # build the hand-written proofs
make status     # show toolchain + per-file proof status at any time
```

The generated files (`coq/map_int_int_cpp.v`, `coq/map_int_int_cpp_names.v`)
and all Rocq build artifacts are gitignored.

---

## Refreshing the pins

`scripts/pins.env` records the commits the proofs were last checked against.
If BRiCk moves forward and you want to update:

1. `cd .brick-workspace && make pull` (advance to current heads),
2. rebuild and re-run `make ast && make proofs`,
3. once the proofs still go through, capture the new commits:
   `git -C .brick-workspace/fmdeps/BRiCk rev-parse HEAD` (etc.) into
   `scripts/pins.env`.
