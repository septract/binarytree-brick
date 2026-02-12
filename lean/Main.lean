import Rbtree

open RBTree Color Tree

/-- Pretty-print a tree with indentation. -/
def ppTree [Repr α] : Tree α → String → String
  | leaf, indent => s!"{indent}·"
  | node c l v r, indent =>
    let color := match c with | red => "R" | black => "B"
    let left := ppTree l (indent ++ "  ")
    let right := ppTree r (indent ++ "  ")
    s!"{indent}{color}({repr v})\n{left}\n{right}"

/-- Assert a boolean condition; print PASS or FAIL. -/
def check (name : String) (cond : Bool) : IO Unit :=
  if cond then
    IO.println s!"  ✓ {name}"
  else
    IO.println s!"  ✗ {name}  ← FAILED"

def main : IO Unit := do
  IO.println "═══ Red-Black Tree Tests ═══"
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

  IO.println "═══ All tests complete ═══"
