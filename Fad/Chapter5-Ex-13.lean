import Fad.Chapter5

namespace Chapter5

/-
  Exercise 5.13 Give a divide-and-conquer algorithm for building a size-balanced
  heap in linearithmic time.
-/

def split (x : Nat) (xs : List Nat) : (Nat × List Nat × List Nat) :=
  let op x acc :=
    let (y, ys, zs) := acc
      if x < y then (x, y :: zs, ys)
      else (y, x :: zs, ys)
xs.foldr op (x, [], [])


#eval split 3 [1,4,5,6,7,8]
/- (1, [3, 5, 7], [4, 6, 8]) balanceado porém não é ordenado. -/

partial def mkheap : List Nat → Tree (Nat)
| []      => Tree.null
| x :: xs =>
  match split x  xs with
  | (y, ys, zs) => Tree.node (mkheap ys) y (mkheap zs)

#eval mkheap [1,4,5,9,8]


/- Árvore Balanceada, erro de terminação -/

end Chapter5
