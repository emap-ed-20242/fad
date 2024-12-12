
import Fad.Chapter1
import Fad.«Chapter1-Ex»
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

#eval minimum [1,2,0]



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

end Chapter6
