
import Fad.Chapter7

namespace Chapter7

-- Ex 7.10

def picks (xs : List a) : List (a × List a) :=
  let rec helper : a → List (a × List a) → List (a × List a)
   | _, []                => []
   | x, ((y, ys) :: rest) => (y, x :: ys) :: (helper x rest)
  match xs with
  | []      => []
  | x :: xs => (x, xs) :: helper x (picks xs)


def pick₀ [LE a] [h : DecidableRel (α := a) (· ≤ ·)] [Inhabited a]
 (xs : List a) : (a × List a) :=
  match picks xs with
  | []      => (default, []) -- unreachable
  | [p]     => p
  | p :: ps =>
    let rec aux : (a × List a) → List (a × List a) → (a × List a)
     | (x, xs), []              => (x, xs)
     | (x, xs), (y, ys) :: rest =>
       if x ≤ y then aux (x, xs) rest else aux (y, ys) rest
    aux p ps


def pick : List Nat → Option (Nat × List Nat)
| []       => none
| [x]      => some (x, [])
| x :: xs  =>
  match pick xs with
  | none => none
  | some (y, ys) =>
    if x ≤ y then some (x, xs) else some (y, x :: ys)

/-
#eval pick [7]
#eval pick [3, 1, 4]
#eval pick [10, 20, 2, 5, 7]
-/
