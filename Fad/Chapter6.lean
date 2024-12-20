
import Fad.Chapter1
import Fad.«Chapter1-Ex»
import Fad.Chapter7
namespace Chapter6

-- 6.1 Minimum and maximum

def foldr1 [Inhabited a] (f : a → a → a) : List a → a
  | []    => default
  | [x]   => x
  | x::xs => f x (foldr1 f xs)

#eval foldr1 min [1,2,3]
#eval foldr1 max [1,2,3]


def minimum [Inhabited a] [Min a] : List a → a :=
  foldr1 min

def maximum [Inhabited a] [Max a] : List a → a :=
  foldr1 max

def pairWith (f : a → a → a) : List a →  List a
 | []       => []
 | [x]      => [x]
 | x::y::xs => (f x y) :: pairWith f xs

def mkPairs [LE a] [DecidableRel (α := a) (· ≤ ·)]
  : List a → List (a × a)
  | []       => []
  | [x]      => [(x, x)]
  | x::y::xs =>
    if x ≤ y then
     (x, y) :: mkPairs xs
    else
     (y, x) :: mkPairs xs


open Chapter1 (unwrap until' single) in

def minmax [Inhabited a] [LE a] [DecidableRel (α := a) (· ≤ ·)]
  [Min a] [Max a] (xs : List a)
  : (a × a) :=
  let op p q := (min p.1 q.1, max p.2 q.2)
  (unwrap ∘ until' single (pairWith op) ∘ mkPairs) xs
    |>.getD (default, default)

#eval minmax [3,4,5,6,7,8,9,10,2]


-- 6.2 Selection from one set

open Chapter7 (sort) in

def select [Inhabited a] [LT a] [DecidableRel (@LT.lt a _)]
(k : Nat) (xs : List a) : a :=
  aux k (sort xs)
 where
  aux : Nat → List a -> a
   | 0, x::_  => x
   | _, []    => default
   | k, _::xs => aux (k- 1) xs


def median [Inhabited a] [LT a] [DecidableRel (@LT.lt a _)]
(xs : List a) : a :=
  let k := xs.length / 2
  select k xs


partial def group [Inhabited a] [LT a] [DecidableRel (@LT.lt a _)] :
Nat →  List a → List (List a)
 | n, [] => [[]]
 | n, xs =>
  let rec p := xs.splitAt n
  p.1::(group n p.2)


open Chapter7 (sort) in

def medians [Inhabited a] [LT a] [DecidableRel (@LT.lt a _)]
(xs : List a) : List a :=
  (group 5 xs).map median


def pivot [Inhabited a] [LT a] [DecidableRel (@LT.lt a _)] :
List a → a
 | []  => default
 | [x] => x
 | xs  => median (medians xs)

/-
def partition3_aux [Inhabited a] [LT a] [DecidableRel (@LT.lt a _)]
(y : a) : (List a × List a × List a) → a → (List a × List a × List a)
   | (us, vs, ws) x =>
    if x < y then (x::us, vs, ws)
    else if x == y then (us, x::vs, ws)
    else (us, vs, x::ws)


def partition3 [Inhabited a] [LT a] [DecidableRel (@LT.lt a _)]
(y : a) (xs : List a) : (List a × List a × List a) :=
  xs.foldr (partition3_aux y ([], [], []))


def select₁ [Inhabited a] [LT a] [DecidableRel (@LT.lt a _)]
(k : Nat) (xs : List a) : a :=
 let (us, vs, ws) := partition3 (pivot xs) xs
 let (m,n) := (us.lengtth, vs.length)
 if k ≤ m then select₁ k us
 else if k ≤ m + n then select (k - m) vs
 else if k > m + n then select₁ (k - m - n) ws
 else default
-/

end Chapter6
