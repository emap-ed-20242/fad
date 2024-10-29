import Fad.Chapter5

namespace Chapter5

-- Exercise 5.2: Quicksort

/-
qsort (x : xs)
= { definição }
Tree.flatten (mkTree (x :: xs))

= { definição de mkTree com (ys, zs) = xs.partition (< x) }
Tree.flatten (Tree.node (mkTree ys) x (mkTree zs))

= { definição de Tree.flatten }
Tree.flatten (mkTree ys) ++ [x] ++ Tree.flatten (mkTree zs)

= { definição de qsort }
qsort ys ++ [x] ++ qsort zs
-/

def qsort0 : List Nat → List Nat
| [] => []
| (x :: xs) =>
  Tree.flatten (mkTree (x :: xs))

#eval qsort0 (List.iota 1000)

def qsort1: List Nat → List Nat
| [] => []
| (x :: xs) =>
  let (ys, zs) := xs.partition (· < x)
  Tree.flatten (Tree.node (mkTree ys) x (mkTree zs))

#eval qsort1 (List.iota 1000)

def qsort2 : List Nat → List Nat
| [] => []
| (x :: xs) =>
  let (ys, zs) := xs.partition (· < x)
  Tree.flatten (mkTree ys) ++ [x] ++ Tree.flatten (mkTree zs)

#eval qsort2 (List.iota 1000)

partial def qsort3 : List Nat → List Nat
| [] => []
| (x :: xs) =>
  let (ys, zs) := xs.partition (· < x)
  (qsort3 ys) ++ [x] ++ (qsort3 zs)

#eval qsort3 (List.iota 1000)

end Chapter5
