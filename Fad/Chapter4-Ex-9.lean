import Fad.Chapter4

namespace Chapter4

/- complete here -/

-- Exercise 4.9: Single-Traversal Partition

def foldr {a b : Type} : (a → b → b) → b → List a → b
| _, e, [] => e
| f, e, (x::xs) => f x (foldr f e xs)

def partition {α : Type} (p : α → Bool) : List α → List α × List α :=
  let op := λ x (ys, zs) => if p x then (x :: ys, zs) else (ys, x :: zs)
  foldr op ([], [])

-- Test cases
#eval partition (. > 0) [1, -2, 3, 0, -5, 6]
#eval partition (. % 2 = 0) [1, 2, 3, 4, 5]
#eval partition (. = 'a') ['a', 'b', 'a', 'c']
#eval partition (. < 5) [6, 7, 2, 4, 1, 9]
#eval partition (fun x => true) [10, 20, 30]
#eval partition (fun x => false) [10, 20, 30]
#eval partition (· % 3 = 0) [1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

end Chapter4
