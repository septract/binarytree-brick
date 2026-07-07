// Monomorphized driver for cpp2v translation.
//
// cpp2v operates on Clang's fully-elaborated AST. Templates must be
// instantiated before translation. This file:
//
//   1. Includes the real Daedalus headers (unmodified).
//   2. Explicitly instantiates Map<int,int> so Clang emits full AST nodes
//      for every Node static method.
//   3. Provides a small driver calling each function we want to verify,
//      ensuring Clang emits their definitions.
//
// Usage:
//   cpp2v -v -names coq/map_int_int_cpp_names.v \
//         -o coq/map_int_int_cpp.v \
//         src/map_int_int.cpp -- \
//         -std=c++17 -I.

#include <ddl/map.h>

// Force Clang to emit all Map<int,int>::Node methods.
template class DDL::Map<int, int>;

namespace {

// Driver function that exercises every operation we intend to verify.
// cpp2v will translate each called function into the Coq deep embedding.
void driver() {
  using Map = DDL::Map<int, int>;

  // --- Construction ---
  Map m;

  // --- insert ---
  m = m.insert(1, 100);
  m = m.insert(2, 200);
  m = m.insert(3, 300);

  // --- contains (uses findNode internally) ---
  bool found = m.contains(2);
  (void)found;

  // --- lookup (uses findNode internally) ---
  DDL::Maybe<int> result = m.lookup(2);
  if (result.isJust()) {
    int v = result.borrowValue();
    (void)v;
  }

  // --- valid (runtime RB invariant check) ---
  bool ok = m.valid();
  (void)ok;

  // --- copy / free (reference counting) ---
  Map m2 = m;
  m2.copy();
  m2.free();

  m.free();
}

} // anonymous namespace
