import Rbtree

-- ══════════════════════════════════════════════════════════════════════
-- Helpers
-- ══════════════════════════════════════════════════════════════════════

/-- Assert a boolean condition; print PASS or FAIL. -/
def check (name : String) (cond : Bool) : IO Unit :=
  if cond then
    IO.println s!"  ✓ {name}"
  else
    IO.println s!"  ✗ {name}  ← FAILED"

-- ══════════════════════════════════════════════════════════════════════
-- Classic implementation tests
-- ══════════════════════════════════════════════════════════════════════

namespace ClassicTests
open RBTree.Classic Color Tree

/-- Pretty-print a Classic tree with indentation. -/
def ppTree [Repr α] : Tree α → String → String
  | leaf, indent => s!"{indent}·"
  | node c l v r, indent =>
    let color := match c with | red => "R" | black => "B"
    let left := ppTree l (indent ++ "  ")
    let right := ppTree r (indent ++ "  ")
    s!"{indent}{color}({repr v})\n{left}\n{right}"

def run : IO Unit := do
  IO.println "═══ Classic Red-Black Tree Tests ═══"
  IO.println ""

  -- Build a tree by inserting [5, 3, 7, 1, 4, 6, 8, 2]
  let vals := [5, 3, 7, 1, 4, 6, 8, 2]
  let t := fromList vals

  IO.println "── Structure ──"
  IO.println (ppTree t "  ")
  IO.println ""

  -- Basic stats
  IO.println "── Stats ──"
  IO.println s!"  size:         {size t}"
  IO.println s!"  height:       {height t}"
  IO.println s!"  black height: {blackHeight t}"
  IO.println s!"  toList:       {toList t}"
  IO.println ""

  -- Membership tests
  IO.println "── Membership ──"
  check "contains 1" (contains 1 t)
  check "contains 5" (contains 5 t)
  check "contains 8" (contains 8 t)
  check "¬contains 0" (!contains 0 t)
  check "¬contains 9" (!contains 9 t)
  IO.println ""

  -- Sorted output
  IO.println "── Ordering ──"
  let sorted := toList t
  check "toList is sorted" (sorted == [1, 2, 3, 4, 5, 6, 7, 8])
  IO.println ""

  -- Insert duplicates should be idempotent
  IO.println "── Duplicates ──"
  let t2 := insert 5 (insert 3 (insert 7 t))
  check "dup insert preserves size" (size t2 == size t)
  check "dup insert preserves toList" (toList t2 == toList t)
  IO.println ""

  -- Empty tree
  IO.println "── Edge cases ──"
  let empty : Tree Nat := leaf
  check "empty tree size = 0" (size empty == 0)
  check "empty tree contains nothing" (!contains 42 empty)
  check "single insert" (toList (insert 42 empty) == [42])
  IO.println ""

  -- Larger tree: insert 1..20 in a scrambled order
  IO.println "── Larger tree (20 elements) ──"
  let big := fromList [10, 15, 5, 3, 12, 18, 1, 7, 14, 20, 2, 8, 6, 16, 4, 19, 11, 9, 13, 17]
  check "size = 20" (size big == 20)
  check "toList = [1..20]" (toList big == (List.range 20).map (· + 1))
  check "height ≤ 10" (height big ≤ 10)
  IO.println ""

  -- Reverse-sorted insertion (worst case for naive BST)
  IO.println "── Worst-case insertion order ──"
  let desc := fromList ((List.range 15).map (15 - ·))
  check "descending size = 15" (size desc == 15)
  check "descending toList sorted" (toList desc == (List.range 15).map (· + 1))
  check "descending height balanced" (height desc ≤ 10)
  IO.println ""

end ClassicTests

-- ══════════════════════════════════════════════════════════════════════
-- DoubleBlack implementation tests
-- ══════════════════════════════════════════════════════════════════════

namespace DoubleBlackTests
open RBTree.DoubleBlack Color Tree

/-- Pretty-print a DoubleBlack tree with indentation. -/
def ppTree [Repr α] : Tree α → String → String
  | leaf, indent => s!"{indent}·"
  | doubleBlackLeaf, indent => s!"{indent}BB·"
  | node c l v r, indent =>
    let color := match c with
      | red => "R" | black => "B" | doubleBlack => "BB" | negativeBlack => "-B"
    let left := ppTree l (indent ++ "  ")
    let right := ppTree r (indent ++ "  ")
    s!"{indent}{color}({repr v})\n{left}\n{right}"

def run : IO Unit := do
  IO.println "═══ DoubleBlack Red-Black Tree Tests ═══"
  IO.println ""

  -- ── Insertion tests (should match Classic behavior) ──
  let vals := [5, 3, 7, 1, 4, 6, 8, 2]
  let t := fromList vals

  IO.println "── Insertion ──"
  IO.println (ppTree t "  ")
  IO.println ""

  IO.println "── Stats ──"
  IO.println s!"  size:         {size t}"
  IO.println s!"  height:       {height t}"
  IO.println s!"  black height: {blackHeight t}"
  IO.println s!"  toList:       {toList t}"
  IO.println ""

  IO.println "── Membership ──"
  check "contains 1" (contains 1 t)
  check "contains 5" (contains 5 t)
  check "contains 8" (contains 8 t)
  check "¬contains 0" (!contains 0 t)
  check "¬contains 9" (!contains 9 t)
  IO.println ""

  IO.println "── Ordering ──"
  check "toList is sorted" (toList t == [1, 2, 3, 4, 5, 6, 7, 8])
  IO.println ""

  -- ── Deletion tests ──
  IO.println "── Deletion: basic ──"
  let t1 := delete 2 t
  check "delete 2: size decreases" (size t1 == size t - 1)
  check "delete 2: element removed" (!contains 2 t1)
  check "delete 2: others preserved" (contains 1 t1 && contains 3 t1)
  check "delete 2: toList correct" (toList t1 == [1, 3, 4, 5, 6, 7, 8])
  IO.println ""

  IO.println "── Deletion: root ──"
  let t2 := delete 5 t
  check "delete 5 (root val): size" (size t2 == size t - 1)
  check "delete 5: element removed" (!contains 5 t2)
  check "delete 5: toList correct" (toList t2 == [1, 2, 3, 4, 6, 7, 8])
  IO.println ""

  IO.println "── Deletion: absent element ──"
  let t3 := delete 99 t
  check "delete absent: size unchanged" (size t3 == size t)
  check "delete absent: toList unchanged" (toList t3 == toList t)
  IO.println ""

  IO.println "── Deletion: all elements ──"
  let mut tr := t
  for v in [1, 2, 3, 4, 5, 6, 7, 8] do
    tr := delete v tr
  check "delete all: empty" (size tr == 0)
  check "delete all: toList = []" (toList tr == [])
  IO.println ""

  IO.println "── Deletion: insert-delete roundtrip ──"
  let t4 := insert 99 t
  check "insert 99: contains 99" (contains 99 t4)
  let t5 := delete 99 t4
  check "delete 99: ¬contains 99" (!contains 99 t5)
  check "roundtrip: toList matches original" (toList t5 == toList t)
  IO.println ""

  IO.println "── Deletion: sequential deletes ──"
  let big := fromList [10, 15, 5, 3, 12, 18, 1, 7, 14, 20, 2, 8, 6, 16, 4, 19, 11, 9, 13, 17]
  let mut b := big
  for v in [5, 10, 15, 20] do
    b := delete v b
  check "delete 4 from 20: size = 16" (size b == 16)
  check "deleted elements gone" (!contains 5 b && !contains 10 b && !contains 15 b && !contains 20 b)
  check "remaining elements present" (contains 1 b && contains 9 b && contains 17 b)
  check "toList sorted" (toList b == [1, 2, 3, 4, 6, 7, 8, 9, 11, 12, 13, 14, 16, 17, 18, 19])
  IO.println ""

  IO.println "── Cross-implementation: toList agreement ──"
  let classicList := RBTree.Classic.toList (RBTree.Classic.fromList [5, 3, 7, 1, 4, 6, 8, 2])
  let dbList := toList (fromList [5, 3, 7, 1, 4, 6, 8, 2])
  check "Classic.toList == DoubleBlack.toList" (classicList == dbList)

  let bigClassic := RBTree.Classic.toList (RBTree.Classic.fromList
    [10, 15, 5, 3, 12, 18, 1, 7, 14, 20, 2, 8, 6, 16, 4, 19, 11, 9, 13, 17])
  let bigDB := toList (fromList
    [10, 15, 5, 3, 12, 18, 1, 7, 14, 20, 2, 8, 6, 16, 4, 19, 11, 9, 13, 17])
  check "large tree: Classic.toList == DoubleBlack.toList" (bigClassic == bigDB)
  IO.println ""

end DoubleBlackTests

-- ══════════════════════════════════════════════════════════════════════
-- Main
-- ══════════════════════════════════════════════════════════════════════

def main : IO Unit := do
  ClassicTests.run
  IO.println ""
  DoubleBlackTests.run
  IO.println "═══ All tests complete ═══"
