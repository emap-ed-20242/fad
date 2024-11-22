import Fad.Chapter1

namespace Chapter7

-- 7.1 A generic greedy algorithm

-- 7.2 Greedy sorting algorithms

def foldr1 [Inhabited a] (f : a → a → a) : List a → a
  | []    => default
  | x::xs => f x (foldr1 f xs)

def minWith { a b : Type} [LE b] [Inhabited a] [DecidableRel (@LE.le b _)]
  (f : a → b) (as : List a) : a :=
  let smaller f x y := if f x ≤ f y then x else y
  foldr1 (smaller f) as

def candidates : List component → List candidate :=
  minWith cost

def mcc : List component → candidate :=
 minWith cost ∘ candidates


open Chapter1 (tails) in

def pairs (xs : List a) : List (Prod a a) :=
 let step₁ : List a → List (Prod a a) → List (Prod a a)
  | [], acc => acc
  | x::ys, acc =>
    let step₂ : List a → List (Prod a a) → List (Prod a a)
     | [], acc => acc
     | y::_, acc => (x, y) :: acc
    (tails ys).foldr step₂ acc
 (tails xs).foldr step₁ []

#eval pairs [1,2,3]



def ic [Ord a] : List a → Nat


def sort [Ord a] : List a → List a :=
 minWith ic ∘ perms


end Chapter7
