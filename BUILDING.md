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
brew install opam cmake llvm@19 gnu-sed bash
```

> **Use LLVM 19 specifically, and put it first on `PATH` for the build:**
> ```bash
> export PATH="/opt/homebrew/opt/llvm@19/bin:$PATH"
> ```
> Apple Clang will **not** work — `cpp2v` needs the `libclang` development
> headers that only the Homebrew/LLVM `clang` ships. The workspace also rejects
> **too-new** clang: it requires `18 ≤ version < 22`, so the current Homebrew
> `llvm` (22.x) fails the check — hence `llvm@19`.

On Debian/Ubuntu: install `opam cmake clang-19 libclang-19-dev` and ensure a
recent `bash` and GNU `sed` (both are default).

Check your host without cloning or building anything:

```bash
make check
```

### 2. Build the toolchain (~30–60 min, first run only)

```bash
export PATH="/opt/homebrew/opt/llvm@19/bin:$PATH"   # LLVM 19 must be first
make setup
```

This runs [`scripts/setup-brick-workspace.sh`](scripts/setup-brick-workspace.sh),
which:

1. Clones `SkyLabsAI/workspace` into `.brick-workspace/` (gitignored),
2. Clones its **public** sub-repos over anonymous **HTTPS**
   (`make clone-public GITHUB_URL=https://github.com/`) — no SSH keys or
   SkyLabsAI credentials required,
3. Checks out the pinned commits from `scripts/pins.env`
   (the workspace tracks moving branch heads, so pinning is what makes the
   build reproducible),
4. Creates the opam switch, installs dependencies, and builds Rocq + `cpp2v` +
   the BRiCk theories.

The script is idempotent — re-running it skips completed steps.

### 3. Activate the toolchain

The build produces binaries under `.brick-workspace/_build/install/default/`
and creates the opam switch at the **repo root** (`./_opam`). The top-level
`Makefile` points at the binaries directly, but for interactive use you need
the switch active in each new shell:

```bash
eval "$(opam env --switch="$PWD" --set-switch)"        # activate ./_opam
export PATH="/opt/homebrew/opt/llvm@19/bin:.brick-workspace/_build/install/default/bin:$PATH"
```

> Do **not** `source .brick-workspace/dev/activate.sh` — it runs a bare
> `eval $(opam env)` that resolves to your *default* opam switch, not this
> repo's `./_opam`, and the build/tools then fail to find libraries
> (e.g. `Library "camlzip" not found`) even though they are installed here.

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

---

## Interactive proof development (fast goal inspection)

Rebuilding a proof file that `Require`s the cpp2v AST costs ~7 minutes (loading
the 96K-line `map_int_int_cpp.vo`). For iteration, drive `coqtop` with the AST
`.vo` **preloaded** — it loads once (~6 s cold, ~1.4 s warm) and then reports
goals instantly:

```bash
eval "$(opam env --switch="$PWD" --set-switch)"
COQTOP=.brick-workspace/_build/install/default/bin/coqtop
COQLIB=.brick-workspace/_build/install/default/lib/coq
# Feed a script that Requires the AST once, starts the lemma, and prints the
# goal between tactics with `idtac "TAG:" g` or `Show`.
$COQTOP -coqlib "$COQLIB" -R coq daedalus_rb
```

See `CLAUDE.md` for the full diagnose-then-fix loop (preloaded coqtop + a
faithful 3-second scratch that imports only `RBTree`/`TreeRep`/`Tactics`).

> An MCP-server route (`LLM4Rocq/rocq-mcp`) was trialled and dropped: its
> interactive backend wouldn't pick up this repo's `-R . daedalus_rb` load path
> in the dune-workspace layout. The coqtop loop above is what we use.
