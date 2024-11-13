import Fad.Chapter4
import Fad.Chapter1
namespace Chapter4

/-
Exercise 4.13 | Luiz Eduardo Bravin

For the (second) definition of combine we have
  flatten (combine t1 t2) = flatten t1 ++ flatten t2

Anticipating the following chapter, give a definition of merge for which
  flatten (union t1 t2) = merge (flatten t1) (flatten t2)
-/

inductive Tree (α : Type) : Type where
| nil
| node (h : Nat) (t₁ : Tree α) (n : α) (t₂ : Tree α) : Tree α
deriving Repr

def flatten {α : Type} : Tree α → List α
| Tree.nil => []
| (Tree.node _ l x r) => flatten l ++ [x] ++ flatten r

def merge : List Int → List Int → List Int
  | [], ys => ys
  | xs, [] => xs
  | (x :: xs), (y :: ys) =>
    if x < y then (x :: merge xs (y :: ys))
    else if x == y then (x :: merge xs ys)
    else (y :: merge (x :: xs) ys)

#eval merge [1,9,10] [4,9,2]


end Chapter4
