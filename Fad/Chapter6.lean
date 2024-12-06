namespace Chapter6

-- 6.1 Minimum and maximum
def foldr1 [Inhabited a] (f : a → a → a) : List a → a
  | []    => default
  | [x]   => x
  | x::xs => f x (foldr1 f xs)

#eval foldr1 min [1,2,3]
#eval foldr1 max [1,2,3]

-- O input das funções minimum e maximum precisam ser corrigidos
def minimum {a : Type u} [Inhabited a] [Ord a] : ( List a) → a :=
  foldr1 min

def maximum { a : Type} [LE a] [Inhabited a] [DecidableRel (@LE.le a _)] : ( List a) → a :=
  foldr1 max

def pairWith (f : a → a → a) : List a →  List a
 | [] => []
 | [x] => [x]
 | x::y::xs => (f x y) :: pairWith f xs

 def mkPairs { a : Type} [LE a] [DecidableRel (@LE.le a _)] : List a → List (a × a)
 | [] => []
 | [x] => [(x,x)]
 | x::y::xs => if x <= y then (x,y) :: mkPairs xs else (y,x) :: mkPairs xs

end Chapter6
