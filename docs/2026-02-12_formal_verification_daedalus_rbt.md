# Formal Verification Options for Daedalus C++ Red-Black Tree

**Date:** 2026-02-12
**Target:** [`rts-c/ddl/map.h`](https://github.com/GaloisInc/daedalus/blob/master/rts-c/ddl/map.h) in GaloisInc/daedalus

---

## 1. The Target Code: What We're Verifying

The Daedalus `map.h` is a ~400-line C++ header implementing a **persistent (functional) red-black tree** based on Okasaki's "Red-Black Trees in a Functional Setting." Key characteristics:

- **Templates**: `Map<Key, Value>` — generic over key and value types
- **Manual reference counting**: Custom `RefCount` field, manual `copy()`/`free()` calls (no `shared_ptr` or RAII; `HasRefs` trait dispatches via `if constexpr (hasRefs<T>())`)
- **Copy-on-write**: `makeCopy()` clones a node only when `ref_count > 1`, enabling structural sharing
- **Insert only**: No delete operation. Insert + lookup + contains + iterator
- **Okasaki balancing**: `setRebalanceLeft`/`setRebalanceRight` handle the 4 rotation cases (left-left, left-right, right-left, right-right) — identical logic to our Lean `balance` function
- **Mutable under the hood**: Despite functional semantics, the C++ uses in-place mutation on unique nodes for efficiency
- **Iterator**: `Boxed<Iterator>` stack for in-order traversal (parent chain as a heap-allocated linked list)
- **Runtime invariant checker**: `valid()` method checks no-red-red and uniform black-height (but only at runtime, not statically verified)

**Properties we'd want to verify:**
1. **BST invariant preserved by insert** (functional correctness)
2. **Red-black invariants preserved** (no red-red, uniform black-height)
3. **Memory safety** (no leaks, no use-after-free, correct reference counting)
4. **Equivalence to functional spec** (the mutable-under-copy-on-write implementation matches pure Okasaki semantics)

---

## 2. Option A: BRiCk (BlueRock/Bedrock Systems)

**Repo:** [github.com/bedrocksystems/BRiCk](https://github.com/bedrocksystems/BRiCk)
**Docs:** [skylabsai.github.io/BRiCk](https://skylabsai.github.io/BRiCk/)
**Proof assistant:** Coq/Rocq + Iris separation logic

### What it is

BRiCk is the only tool that directly targets **C++ verification**. Developed by BedRock Systems (now BlueRock Security) for verifying their NOVA microhypervisor. It provides:

- **cpp2v**: A Clang-based tool that translates C++ source into a Coq deep embedding (works on the elaborated AST, so templates are fully instantiated by Clang before translation)
- **Axiomatic semantics**: Hoare-logic-style reasoning rules for C++ constructs, built on Iris separation logic
- **Concurrency support**: Handles atomics, mutexes, lock-free code

### Applicability to map.h

| Feature | Supported? | Notes |
|---------|-----------|-------|
| Templates | Yes | cpp2v works post-instantiation; you'd verify `Map<int,int>` etc. specifically |
| Manual ref counting | Likely yes | Core BRiCk handles pointer manipulation; ref counting is just arithmetic + pointer ops |
| `if constexpr` | Yes | Resolved at compile time before cpp2v sees it |
| Operator overloading | Yes | Resolved by Clang elaboration |
| `new`/`delete` | Should work | Systems code typically uses allocators; BRiCk handles pointer operations |
| Nested classes | Unclear | `Node` is private nested inside `Map`; needs testing with cpp2v |

### Effort estimate

**High.** BRiCk is designed for separation-logic experts working in Coq. You'd need to:
1. Run cpp2v on a monomorphized `map.h` (with concrete Key/Value types)
2. Write separation logic predicates describing the tree shape, BST ordering, and ref-count invariants
3. Prove insert preserves all invariants via interactive Coq proof
4. The ref-counting / copy-on-write aspect adds significant proof complexity beyond a pure functional tree

### Verdict

**Most direct path for C++ verification**, but requires deep Coq/Iris expertise. No precedent for RBT verification in BRiCk specifically (their published work is on OS kernels and concurrency primitives). The axiomatic semantics approach means you're trusting the axioms are sound for the C++ features used.

**Key publication:** "Developing With Formal Methods at BedRock Systems, Inc." ([IEEE S&P 2022](https://ieeexplore.ieee.org/document/9760701))

---

## 3. Option B: Cerberus / CN (C only — requires translation)

**Repo:** [github.com/rems-project/cerberus](https://github.com/rems-project/cerberus) / [github.com/rems-project/cn](https://github.com/rems-project/cn)
**Project lead:** Peter Sewell (Cambridge)

### What it is

Cerberus is a formal executable semantics for ISO C11. **CN** is a verification tool built on top, using separation-logic refinement types. Think of CN as "Rust-style ownership annotations for C" that get verified either statically or via runtime testing (Fulminate, POPL 2025).

### The `septract/lean-c-semantics` project

**Repo:** [github.com/septract/lean-c-semantics](https://github.com/septract/lean-c-semantics)
**Author:** Mike Dodds (Galois), developed with Claude Code
**Status:** Active (178 commits, 98% CI pass rate on ~760 tests as of Jan 2026)

This is a **Lean 4 interpreter for Cerberus Core IR** — it creates a bridge from C into Lean's proof ecosystem:

```
C source → Cerberus → Core IR (JSON) → Lean Parser → Lean AST → Lean Interpreter
```

Key capabilities:
- **JSON parser** that converts Cerberus Core IR to Lean AST (100% success across 5500+ files)
- **Concrete memory model** with allocation-ID provenance, bounds validation, and undefined behavior detection
- **Small-step interpreter** mirroring Cerberus semantics
- **Docker deployment** for easy use: `docker run ghcr.io/septract/lean-c-semantics:main program.c`
- **Test results**: 76/76 minimal tests pass, 65/65 debug tests pass, ~745/760 CI tests pass (failures are unimplemented I/O and intentional semantic divergences)

This project is highly relevant because it means **C semantics are already formalized in Lean 4**. While it is currently an interpreter (not a verification tool), having the semantics in Lean opens the door to:
1. Stating properties about C program behavior directly in Lean
2. Proving refinement between a Lean functional spec and C code via the shared Lean framework
3. Eventually building a CN-like verification tool natively in Lean

### Applicability to map.h

**CN cannot directly verify C++ code.** Cerberus covers C11 only and explicitly excludes: templates, classes, operator overloading, namespaces, RAII, and all other C++-specific features.

To use CN, you'd need to **manually rewrite `map.h` as a C implementation**:
- Replace templates with `void*` + function pointers (or a concrete monomorphization)
- Replace classes with structs + free functions
- Replace `new`/`delete` with `malloc`/`free`
- Replace `if constexpr` dispatch with runtime function pointers or separate implementations
- Remove operator overloading, use explicit comparison functions

The resulting C code could then be annotated with CN separation-logic specs and verified. CN has been demonstrated on linked lists and the pKVM buddy allocator.

### Effort estimate

**Very high** (rewrite + verification). The C++ to C translation is significant manual effort and the resulting code would diverge from the actual Daedalus runtime, reducing the value of the verification.

### Verdict

**Not recommended for this specific task** unless a C port is independently useful. CN itself is excellent and actively developed (POPL 2023, POPL 2025 papers), but the C++ barrier is the blocker.

---

## 4. Option C: SAW via LLVM (Galois)

**Website:** [saw.galois.com](https://saw.galois.com/)
**Repo:** [github.com/GaloisInc/saw-script](https://github.com/GaloisInc/saw-script) (488 stars, 59 contributors, v1.3 released 2025)

### What it is

SAW (Software Analysis Workbench) performs formal verification by:
1. Compiling C/C++ to LLVM bitcode (or Java to JVM bytecode, or Rust to MIR)
2. Symbolically executing the bitcode via the Crucible engine
3. Translating to SAWCore (a pure functional dependently-typed IR)
4. Sending proof obligations to SMT solvers (Z3, Yices, ABC) or exporting to Coq

**Crown jewel case study:** Verified AWS LibCrypto (SHA2, HMAC, AES-GCM, ECDSA, ECDH, HKDF) — proofs run in CI on every AWS-LC pull request.

### The fundamental problem for RBTs

**SAW cannot handle unbounded loops.** Its symbolic execution unrolls loops, which works for crypto (fixed iterations) but fails for tree traversal where depth depends on input:

> "SAW is particularly suited to imperative programs that don't contain potentially-unbounded loops. Symbolic simulation can't effectively deal with loops whose termination depends on a symbolic value."

The `findNode` function in `map.h` has a `while` loop traversing the tree, and `ins` recursively descends — both are unbounded in the tree size.

### What SAW *could* do

- **Bounded verification**: Prove correctness for trees up to depth N (e.g., N=5). This gives high confidence but not a universal proof.
- **Memory safety of individual operations**: With Crucible's memory model, SAW could check for use-after-free, null dereference, etc. on bounded instances.
- **LLM-assisted proofwriting**: Galois has [experimented with GPT-4 generating SAW proofs](https://galois.com/blog/2023/08/applying-gpt-4-to-saw-formal-verification/) (automated a salsa20 memory safety proof). Could accelerate bounded verification.

### Interesting Galois connection

SAW is made by the same company (Galois) that made Daedalus. They might have internal insights on verifying their own runtime. However, there's no public evidence of SAW being applied to Daedalus.

### Effort estimate

**Medium for bounded, impossible for unbounded.** SAWScript is relatively ergonomic, and LLVM ingestion handles C++ templates/classes. But the fundamental loop limitation means you can't prove universal correctness.

### Verdict

**Good for bounded model checking / memory safety, but cannot prove full functional correctness** of a tree data structure. Consider as a complement to other approaches (e.g., prove correctness in Lean, then use SAW to check the C++ implementation matches on bounded instances).

---

## 5. Other Approaches Worth Considering

### 5a. VST (Verified Software Toolchain) — Appel's Coq framework

**The gold standard for C verification.** Andrew Appel has already published **[Efficient Verified Red-Black Trees](https://www.cs.princeton.edu/~appel/papers/redblack.pdf)** (2011) proving BST and balance invariants in Coq, as part of the [Verified Functional Algorithms](https://softwarefoundations.cis.upenn.edu/vfa-current/Redblack.html) textbook.

VST uses CompCert's C semantics and separation logic. **But it only works on C, not C++.** Same translation barrier as CN.

The **VeriFFI** project ([CertiCoq/VeriFFI](https://github.com/CertiCoq/VeriFFI), POPL 2025) bridges Coq functional specs to C implementations via VST — write a functional model in Coq, prove it correct, then show the C code implements it. This is the closest thing to "prove in a proof assistant, verify the C matches."

### 5b. CBMC (Bounded Model Checking for C/C++)

**Directly supports C++**, including templates, classes, and STL. Performs bounded model checking: unwinds loops to a fixed depth and checks assertions via SAT/SMT.

For `map.h`, CBMC could:
- Check assertions (`valid()` returns true after every insert) up to N insertions
- Find memory safety bugs, null dereferences, arithmetic overflow
- Requires no manual annotation — works on unmodified C++

**Limitation:** Same as SAW — bounded, not universal. But much lower effort: just add `assert()` statements and run CBMC.

### 5c. The "Lean spec + refinement proof" approach via `lean-c-semantics`

The most intellectually satisfying path, and now **partially enabled by existing tooling**:

1. **You already have a verified RBT in Lean 4** (`Rbtree/Basic.lean`) with BST invariant proofs
2. **`lean-c-semantics`** provides C semantics in Lean 4 via Cerberus Core IR
3. Write a **refinement layer** showing the C `map` operations (compiled through Cerberus) correspond to the Lean operations
4. For each C function, prove it refines the Lean function (same observable behavior)

**What exists today:**
- [`septract/lean-c-semantics`](https://github.com/septract/lean-c-semantics) — a Lean 4 interpreter for Cerberus Core IR with a concrete memory model, provenance tracking, and UB detection. 98% CI pass rate on ~760 tests.
- The pipeline `C source → Cerberus → Core IR → Lean AST` is working and tested.
- The Lean AST and memory model definitions give you the semantic foundation to state and prove properties about C programs in Lean.

**What's still needed:**
- A **verification mode** (the project is currently an interpreter, not a prover). You'd need to lift from concrete execution to symbolic reasoning.
- **C++ to C translation** is still required (Cerberus handles C only). But this is a smaller gap than before — you only need to translate the C++ features, not build the entire semantic framework.
- **VeriFFI** (Coq-to-C, POPL 2025) shows the pattern for connecting functional specs to C implementations, but lives in the Coq ecosystem, not Lean.

**This is the most promising research direction** because it keeps everything in Lean 4, leveraging both your existing RBT proofs and an existing C semantics formalization.

### 5d. SPARK/Ada precedent

Claire Dross and Yannick Moy published **[Auto-Active Proof of Red-Black Trees in SPARK](https://blog.adacore.com/uploads/Auto-Active-Proof-of-Red-Black-Trees-in-SPARK.pdf)** (NFM 2017) — a fully verified imperative RBT in SPARK/Ada with auto-active verification (annotations + SMT solvers). Demonstrates that auto-active verification of imperative RBTs is feasible but requires extensive annotations (contracts, loop invariants, type invariants, assertions).

---

## 6. Comparative Summary

| Approach | Handles C++ directly? | Proof strength | Effort | Tooling maturity |
|----------|----------------------|----------------|--------|-----------------|
| **BRiCk** | Yes | Full (Coq/Iris) | Very high | Medium (production-internal at BlueRock) |
| **CN/Cerberus** | No (C only) | Full (sep logic) | Very high (needs rewrite) | High (active, POPL 2023/2025) |
| **SAW via LLVM** | Yes (LLVM bitcode) | Bounded only | Medium | High (Galois production tool) |
| **CBMC** | Yes | Bounded only | Low | High (industry standard) |
| **VST** | No (C only) | Full (Coq) | High (needs rewrite) | High (Appel has RBT proof) |
| **Lean refinement** | No tooling yet | Full (if built) | Research project | Does not exist |

---

## 7. Recommendation

Given the constraints (C++ code, templates, manual ref counting, desire for strong guarantees):

### Tier 1: Most practical now

**CBMC for bounded verification.** Lowest effort, directly handles C++, catches real bugs. Add `assert(valid())` after every insert in a test harness and unwind to depth 10-15. This won't give a universal proof but will find bugs and build confidence quickly.

### Tier 2: Strongest guarantees

**BRiCk for full C++ verification.** The only tool that can verify this code without rewriting it. Requires Coq expertise and significant investment. Would produce machine-checked proofs of BST invariant, red-black invariant, and memory safety for the actual C++ code. Consider reaching out to the BlueRock team — this would be a good case study for them.

### Tier 3: Alternative full-proof paths

**Port to C and use CN or VST.** If a C version of the RBT is useful for Daedalus anyway (e.g., as a simpler runtime option), writing a clean C implementation with CN annotations would give full separation-logic verification with active community support.

### Tier 4: Research direction

**Build the Lean-to-C refinement bridge.** The most elegant approach: prove correctness once in Lean, then show the C++ implementation refines it. But this is a research project, not an off-the-shelf tool. The nonexistent `septract/lean-c-semantics` might be pointing in this direction — formalizing C semantics in Lean 4 would be the foundation for such a bridge.

---

## Key References

- **BRiCk:** [IEEE S&P 2022](https://ieeexplore.ieee.org/document/9760701), [HotOS 2025](https://sigops.org/s/conferences/hotos/2025/papers/hotos25-206.pdf), [GitHub](https://github.com/bedrocksystems/BRiCk)
- **CN/Cerberus:** [CN POPL 2023](https://www.cl.cam.ac.uk/~nk480/cn.pdf), [Fulminate POPL 2025](https://www.cl.cam.ac.uk/~pes20/cn-testing-popl2025.pdf), [Tutorial](https://rems-project.github.io/cn-tutorial/)
- **SAW:** [saw.galois.com](https://saw.galois.com/), [AWS-LC verification](https://github.com/awslabs/aws-lc-verification), [GPT-4 + SAW](https://galois.com/blog/2023/08/applying-gpt-4-to-saw-formal-verification/)
- **Appel RBT:** [Efficient Verified Red-Black Trees](https://www.cs.princeton.edu/~appel/papers/redblack.pdf), [VFA textbook](https://softwarefoundations.cis.upenn.edu/vfa-current/Redblack.html)
- **VeriFFI:** [POPL 2025](https://www.cs.princeton.edu/~appel/papers/VeriFFI.pdf), [GitHub](https://github.com/CertiCoq/VeriFFI)
- **SPARK RBT:** [Dross & Moy, NFM 2017](https://blog.adacore.com/uploads/Auto-Active-Proof-of-Red-Black-Trees-in-SPARK.pdf)
- **Separation logic RBT:** [Schellhorn et al., VSTTE 2022](https://link.springer.com/chapter/10.1007/978-3-031-25803-9_8)
- **CBMC:** [cbmc.org](https://www.cprover.org/cbmc/)
