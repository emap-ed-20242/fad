import Fad.Chapter5

namespace Chapter5

/-
  Exercise 5.13 Give a divide-and-conquer algorithm for building a size-balanced
  heap in linearithmic time.
-/

-- Função auxiliar usada em foldr
def auxiliar (x : Nat) (acc : Nat × List Nat × List Nat) : Nat × List Nat × List Nat :=
  let (y, ys, zs) := acc
  if x < y then (x, y :: zs, ys) else (y, x :: zs, ys)

-- Função split que separa uma lista em três partes
def split : List Nat → Nat × List Nat × List Nat
| []       => ( default, [], []) -- No caso de lista vazia, embora tecnicamente isso não ocorra
| (x :: xs) => xs.foldr auxiliar (x, [], [])

#eval split [1,3,4,5,6,7,8]
/- (1, [3, 5, 7], [4, 6, 8]) faz sentido? -/

-- Função para construir um heap
partial def mkheap_ : List Nat → Tree Nat
| []        => Tree.null
| xs =>
  let (y, ys, zs) := split (xs)
  Tree.node (mkheap_ ys) y (mkheap_ zs)


end Chapter5
