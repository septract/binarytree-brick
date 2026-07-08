#!/usr/bin/env bash
#
# Set up the BRiCk toolchain (Rocq + cpp2v) used to check the proofs in coq/.
#
# This clones the public SkyLabsAI/workspace meta-repo into .brick-workspace/,
# checks out the known-good commits from scripts/pins.env, installs the opam
# dependencies, and builds Rocq + cpp2v from source.
#
# It is idempotent: re-running skips work that is already done. The first run
# takes roughly 30-60 minutes (it builds the Rocq prover from source).
#
# Usage:
#   scripts/setup-brick-workspace.sh            # full setup
#   scripts/setup-brick-workspace.sh --check    # preflight version checks only
#
# Requirements (see scripts/pins.env for exact versions):
#   opam >= 2.2.1, OCaml 5.4.0 (installed into a local switch by this script),
#   Clang/LLVM 18-21 with dev headers (Apple Clang is NOT sufficient),
#   cmake, GNU sed, and a recent bash (>= 4).

set -euo pipefail

# --- Locate ourselves and the repo root ---
SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
REPO_ROOT="$(cd "$SCRIPT_DIR/.." && pwd)"
WORKSPACE_DIR="$REPO_ROOT/.brick-workspace"

# shellcheck source=pins.env
source "$SCRIPT_DIR/pins.env"

log()  { printf '\033[1;34m==>\033[0m %s\n' "$*"; }
warn() { printf '\033[1;33mWARN:\033[0m %s\n' "$*" >&2; }
die()  { printf '\033[1;31mERROR:\033[0m %s\n' "$*" >&2; exit 1; }

# --- Preflight: check host tools ---

# Compare dotted versions: ver_ge A B  ->  true if A >= B.
ver_ge() { [ "$(printf '%s\n%s\n' "$1" "$2" | sort -V | head -n1)" = "$2" ]; }

preflight() {
  local ok=1

  command -v git   >/dev/null || { warn "git not found";   ok=0; }
  command -v cmake >/dev/null || { warn "cmake not found (brew install cmake)"; ok=0; }

  if command -v opam >/dev/null; then
    local opamv; opamv="$(opam --version)"
    ver_ge "$opamv" "$REQ_OPAM_MIN" || { warn "opam $opamv < required $REQ_OPAM_MIN"; ok=0; }
  else
    warn "opam not found (brew install opam); need >= $REQ_OPAM_MIN"; ok=0
  fi

  # A real clang with dev headers — Apple Clang reports differently and lacks
  # the libclang dev headers cpp2v links against.
  if command -v clang >/dev/null; then
    local clangv; clangv="$(clang --version | sed -nE 's/.*version ([0-9]+\.[0-9]+\.[0-9]+).*/\1/p' | head -n1)"
    if [ -n "$clangv" ]; then
      ver_ge "$clangv" "$REQ_CLANG_MIN" || warn "clang $clangv < recommended $REQ_CLANG_MIN"
      ver_ge "$REQ_CLANG_MAX" "$clangv" || warn "clang $clangv >= first-unsupported $REQ_CLANG_MAX"
    fi
    clang --version | grep -qi apple && \
      warn "Apple Clang detected; install LLVM (brew install llvm) — cpp2v needs libclang dev headers"
  else
    warn "clang not found; install LLVM 18-21 (brew install llvm)"; ok=0
  fi

  # GNU sed (gsed on macOS) — workspace scripts use GNU extensions.
  if ! { command -v gsed >/dev/null || sed --version 2>/dev/null | grep -qi gnu; }; then
    warn "GNU sed not found (brew install gnu-sed); workspace scripts require it"
  fi

  [ "$ok" = 1 ] || die "Preflight failed; install the missing tools above and re-run."
  log "Preflight OK."
}

# --- Pin a single sub-repo to its known-good commit ---
pin_repo() {
  local dir="$1" commit="$2" name
  name="$(basename "$dir")"
  [ -n "$commit" ] || { warn "no pin recorded for $name; leaving at branch head"; return; }
  [ -d "$dir/.git" ] || { warn "$name not cloned; skipping pin"; return; }
  if [ "$(git -C "$dir" rev-parse HEAD)" = "$commit" ]; then
    return  # already pinned
  fi
  log "Pinning $name -> ${commit:0:12}"
  git -C "$dir" fetch --quiet origin "$commit" 2>/dev/null || git -C "$dir" fetch --quiet --all
  git -C "$dir" checkout --quiet "$commit"
}

apply_pins() {
  log "Applying known-good commit pins (scripts/pins.env)"
  git -C "$WORKSPACE_DIR" checkout --quiet "$WORKSPACE_COMMIT" 2>/dev/null || \
    warn "could not pin workspace to $WORKSPACE_COMMIT (continuing at current head)"

  pin_repo "$WORKSPACE_DIR/fmdeps/BRiCk"          "$PIN_fmdeps_BRiCk"
  pin_repo "$WORKSPACE_DIR/fmdeps/brick-libcpp"   "$PIN_fmdeps_brick_libcpp"
  pin_repo "$WORKSPACE_DIR/fmdeps/auto-docs"      "$PIN_fmdeps_auto_docs"
  pin_repo "$WORKSPACE_DIR/fmdeps/fm-ci"          "$PIN_fmdeps_fm_ci"

  pin_repo "$WORKSPACE_DIR/vendored/rocq"           "$PIN_vendored_rocq"
  pin_repo "$WORKSPACE_DIR/vendored/rocq-stdlib"    "$PIN_vendored_rocq_stdlib"
  pin_repo "$WORKSPACE_DIR/vendored/rocq-stdpp"     "$PIN_vendored_rocq_stdpp"
  pin_repo "$WORKSPACE_DIR/vendored/rocq-iris"      "$PIN_vendored_rocq_iris"
  pin_repo "$WORKSPACE_DIR/vendored/rocq-elpi"      "$PIN_vendored_rocq_elpi"
  pin_repo "$WORKSPACE_DIR/vendored/elpi"           "$PIN_vendored_elpi"
  pin_repo "$WORKSPACE_DIR/vendored/rocq-equations" "$PIN_vendored_rocq_equations"
  pin_repo "$WORKSPACE_DIR/vendored/rocq-ext-lib"   "$PIN_vendored_rocq_ext_lib"
  pin_repo "$WORKSPACE_DIR/vendored/rocq-lsp"       "$PIN_vendored_rocq_lsp"
  pin_repo "$WORKSPACE_DIR/vendored/vsrocq"         "$PIN_vendored_vsrocq"
}

# --- Main ---

preflight
[ "${1:-}" = "--check" ] && { log "Preflight-only run complete."; exit 0; }

if [ ! -d "$WORKSPACE_DIR/.git" ]; then
  log "Cloning workspace into .brick-workspace/ (public repos only)"
  git clone "$WORKSPACE_REPO" "$WORKSPACE_DIR"
fi

cd "$WORKSPACE_DIR"

log "Cloning public sub-repositories (make clone-public, over HTTPS)"
# The workspace defaults GITHUB_URL to `git@github.com:` (SSH). All the repos we
# need are PUBLIC, so force anonymous HTTPS — no SSH keys / SkyLabsAI
# credentials required. This is what makes the build reproducible for anyone.
make clone-public -j GITHUB_URL="https://github.com/"

apply_pins

# The opam switch lives one level above the workspace (the meta-repo's opam.sh
# runs `opam switch create --empty ..`), i.e. at the repo root. opam identifies
# a local switch by that containing directory.
SWITCH="$REPO_ROOT"
DEPS_OPAM="$WORKSPACE_DIR/dev/opam-deps/skylabs-deps.opam"

log "Creating the opam switch + installing dependencies (this can take ~30 min)"
# Use dev-setup-opam (gated only on opam version) rather than dev-setup, which
# runs the workspace's full dev-check-ver preflight. That preflight enforces
# strict UPPER bounds on clang/uv/rust that reject newer host toolchains
# (e.g. clang 22, uv 0.11) even though they are irrelevant to building Rocq +
# cpp2v. Our own preflight() above already checked the versions that matter.
make dev-setup-opam

opam update
opam repo add --this-switch --switch="$SWITCH" archive \
  git+https://github.com/ocaml/opam-repository-archive 2>/dev/null || true
# --update-invariant: a freshly-created empty switch may inherit a global
# compiler invariant (e.g. OCaml 5.3.0) that conflicts with the 5.4.0 that
# skylabs-deps pins; this lets opam adopt 5.4.0. Run twice: the first solve can
# satisfy the meta-package with a REDUCED set (dropping e.g. camlzip); a second
# plain install with the full switch settled pulls the remainder.
opam install --switch="$SWITCH" --update-invariant --yes "$DEPS_OPAM"
opam install --switch="$SWITCH" --yes "$DEPS_OPAM" || true
# Belt-and-suspenders: ensure libs Rocq's build needs that the solver may drop.
opam install --switch="$SWITCH" --yes camlzip.1.13 conf-zlib || true

log "Building Rocq + cpp2v + BRiCk theories (this can take ~30-60 min)"
# Activate OUR switch explicitly. Do NOT `source dev/activate.sh` — it runs a
# bare `eval $(opam env)` that resolves to the *default* switch, so the build
# would compile against the wrong findlib (symptom: `Library "camlzip" not
# found` even though it is installed in our switch).
eval "$(opam env --switch="$SWITCH" --set-switch)"
export OPAMSWITCH="$SWITCH"

# `make stage1` runs `ast-prepare-bluerock`, which tries to generate ASTs for
# the PRIVATE bluerock/NOVA and bluerock/bhv repos we deliberately did not clone
# and exits nonzero on the skip. `dune build` likewise fails only on an
# auto-docs *demo* target. Neither touches the BRiCk proof library, so we run
# the steps tolerantly and verify the real artifacts afterward.
make ide-prepare || true
make -j"$(getconf _NPROCESSORS_ONLN 2>/dev/null || echo 4)" stage1 || true
dune build || true

# --- Verify the toolchain actually works (exit codes above are unreliable) ---
COQC="$WS_BUILD/bin/coqc"; COQLIB="$WS_BUILD/lib/coq"
CPP2V_BIN="$WS_BUILD/bin/cpp2v"; PET_BIN="$WS_BUILD/bin/pet"
ok=1
for b in "$COQC" "$CPP2V_BIN" "$PET_BIN" "$WS_BUILD/bin/pet-server"; do
  [ -x "$b" ] || { warn "missing binary: $b"; ok=0; }
done
# The definitive check: can coqc import the BRiCk library our proofs use?
probe="$(mktemp -t brickprobe).v"
printf 'From Stdlib Require Import ZArith.\nRequire Import skylabs.lang.cpp.cpp.\nCheck cpp_logic.\n' > "$probe"
if "$COQC" -coqlib "$COQLIB" "$probe" >/dev/null 2>&1; then
  log "Verified: coqc imports skylabs.lang.cpp ✓"
else
  warn "coqc could not import skylabs.lang.cpp — the BRiCk library build is incomplete."
  ok=0
fi
rm -f "$probe" "${probe%.v}.vo" "${probe%.v}.vos" "${probe%.v}.vok" "${probe%.v}.glob" 2>/dev/null || true

[ "$ok" = 1 ] || die "Toolchain build did not produce a working coqc/cpp2v/pet. See log above."

log "Done. Toolchain built + verified under .brick-workspace/_build/install/default/."
log "The opam switch is the repo root ($SWITCH); binaries are in WS_BUILD/bin."
log "Next: from the repo root, run 'make cpp2v && make ast && make proofs'."
log "(Each new shell: eval \$(opam env --switch=$SWITCH --set-switch), and put"
log " .brick-workspace/_build/install/default/bin on PATH for pet/cpp2v.)"
