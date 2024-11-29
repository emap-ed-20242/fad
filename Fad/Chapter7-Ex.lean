
import Fad.Chapter7

namespace Chapter7


-- Ex 7.10

/-
picks [] = []
picks (x:xs) = (x, xs) : [(y, x:ys) | (y, ys) <- picks xs]

picks [3, 1, 4] =
  [(3, [1, 4]), (1, [3, 4]), (4, [3, 1])]

pick xs = minimum (picks xs)

pick [3, 1, 4]
= minimum [(3, [1, 4]), (1, [3, 4]), (4, [3, 1])]
= (1, [3, 4])
-/

def picks (xs : List a) : List (a × List a) :=
  let rec helper : a → List (a × List a) → List (a × List a)
   | _, []                => []
   | x, ((y, ys) :: rest) => (y, x :: ys) :: (helper x rest)
  match xs with
  | []      => []
  | x :: xs => (x, xs) :: helper x (picks xs)

-- variable (h : Ord Nat) (hs : Ord (List Nat))

instance [Ord α] [Ord (List α)] : Min (α × List α) where
 min x y :=
  match compare x.1 y.1 with
  | Ordering.lt => x
  | Ordering.gt => y
  | Ordering.eq => match compare x.2 y.2 with
    | Ordering.eq => x
    | Ordering.lt => x
    | Ordering.gt => y

instance [Ord (List Nat)] : Min (Nat × List Nat) where
 min x y :=
  match compare x.1 y.1 with
  | Ordering.lt => x
  | Ordering.gt => y
  | Ordering.eq => match compare x.2 y.2 with
    | Ordering.eq => x
    | Ordering.lt => x
    | Ordering.gt => y

def test : List (Nat × List Nat) := [(1,[1,2]),(2,[2,3])]
#eval test.min?

def pick : List Nat → Option (Nat × List Nat)
| []       => none
| [x]      => some (x, [])
| (x :: xs) =>
  match pick xs with
  | some (y, ys) =>
    if x ≤ y then some (x, xs)
    else some (y, x :: ys)
  | none => none

#eval pick [7]         -- Esperado: `some (7, [])`
#eval pick [3, 1, 4]   -- Esperado: `some (1, [3, 4])`
#eval pick [10, 20, 2, 5, 7] -- Esperado: `some (2, [10, 20, 5, 7])`
