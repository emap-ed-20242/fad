import Fad.Chapter3
namespace Chapter3


def Forest (α: Type):= List (Tree α)

def weight {α : Type} : Tree α → Nat
| Tree.leaf _ => 0
| Tree.node n t₁ t₂ => n +  weight t₁ + weight t₂

def insert {α : Type} (t1 : Tree α) : Forest α → Forest α
| [] => [t1]
| t2 :: ts =>
  if  weight t1 ≤  weight t2 then
    t1 :: t2 :: ts
  else
    t2 :: insert t1 ts


#eval insert (Tree.node 2 (Tree.leaf 5) (Tree.leaf 6))
             [Tree.node 3 (Tree.leaf 7) (Tree.leaf 8), Tree.node 4 (Tree.leaf 9) (Tree.leaf 10)]
