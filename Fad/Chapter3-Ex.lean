import Fad.Chapter3
import Fad.Chapter1
import Lean.Data.AssocList


namespace Chapter3
open SL1

-- 3.1

/-
(['a', 'b', 'c'], ['d'])
(['a'], ['d', 'c', 'b'])
(['a', 'b'], ['d', 'c'])
-/

#eval toSL "abcd".toList
#eval List.foldr consSL nilSL "abcd".toList
#eval List.foldl (flip snocSL) nilSL "abcd".toList
#eval consSL 'a' (snocSL 'd' (List.foldr consSL nilSL "bc".toList))


-- 3.2

def nullSL {α : Type} : SymList α → Bool
| (xs, ys) => xs.isEmpty ∧ ys.isEmpty

def singleSL {α : Type} : SymList α → Prop
| (xs, ys) => (xs.isEmpty ∧ ys.single) ∨ (ys.isEmpty ∧ xs.single)

def lengthSL {α : Type} : SymList α → Nat
| (xs, ys) => xs.length + ys.length


-- 3.3

def headSL? {α : Type} : SymList α → Option α
 | ([],[])  => none    -- why not nilSL?
 | ([], ys) => List.head? ys
 | (xs, _)  => List.head? xs


-- 3.4

def initSL {α : Type} : SymList α → Option (SymList α)
 | (xs, [])  => if xs.isEmpty then none else some nilSL
 | (xs, [_]) =>
   let (us, vs) := xs.splitAt (xs.length / 2)
   some (us, vs.reverse)
 | (xs, _ :: ys)  => some (xs, ys)


-- 3.5

def dropWhileSL (p : α → Bool) (sl : SymList α) : SymList α :=
 let us := sl.1.dropWhile p
 if us.isEmpty then toSL (sl.2.reverse.dropWhile p) else (us, sl.2)

def dropWhileSL' (p : α → Bool) (sl : SymList α) : SymList α :=
 match headSL? sl with
 | none => nilSL
 | some a =>
   if p a then
    match (tailSL sl) with
    | none => nilSL
    | some us => dropWhileSL p us
   else sl

#eval [1,2,3,4].dropWhile (· < 3)
#eval dropWhileSL (· < 3) (toSL [1,2,3,4]) |> fromSL

-- 3.6

partial def initsSL {a : Type} (xs : SymList a) : SymList (SymList a) :=
 if nullSL xs then
  snocSL xs nilSL
 else
  match (initSL xs) with
  | none => nilSL
  | some i => snocSL xs (initsSL i)


-- 3.7

def inits {α : Type} (xs : List α) : List (List α) :=
 ((List.map List.reverse) ∘ (Chapter1.scanl (flip List.cons) [])) xs

#eval inits [1,2,3,4]


/- 3.8 - discussão sobre complexidade no Livro. Código sugerido abaixo. -/

def measure (ts : List (Tree a)) : Nat :=
  ts.foldr (λ t acc => size t + acc) 0
 where
  size : Tree a → Nat
  | Tree.leaf _       => 1
  | Tree.node _ t1 t2 => 1 + size t1 + size t2

def fromTs : List (Tree a) → List a
| [] => []
| (Tree.leaf x) :: ts =>
  have : measure ts < measure (Tree.leaf x :: ts) := by
   simp [measure,measure.size]
  x :: fromTs ts
| (Tree.node n t1 t2) :: ts =>
  have : measure (t1 :: t2 :: ts) < measure (Tree.node n t1 t2 :: ts) := by
   simp [measure, measure.size]
   rw [Nat.add_assoc]; simp
  fromTs (t1 :: t2 :: ts)
termination_by x1 => measure x1

open Tree in
#eval fromTs [mk (mk (leaf 'a') (leaf 'b')) (mk (leaf 'c') (leaf 'd'))]

-- 3.10

def toRA {a : Type} : List a → RAList a :=
  List.foldr consRA nilRA

#eval fromRA <| toRA [1,2,3,4,5]

example : ∀ (xs : List a), xs = fromRA (toRA xs) := by
  intro xs
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp [toRA, fromRA, consRA]
    rw [ih]
    match toRA xs with
    | [] => rfl
    | (Digit.zero :: ds) =>
      simp [fromRA, fromT, Tree.mk]
      rw [concatMap]
      sorry
    | (Digit.one t :: ds) =>
      simp [fromRA, fromT, Tree.mk]
      rw [concatMap]
      sorry

-- 3.11

def updateT : Nat → α → Tree α → Tree α
| 0, x, Tree.leaf _ => Tree.leaf x
| _, _, Tree.leaf y => Tree.leaf y -- problem
| k, x, Tree.node n t1 t2 =>
  let m := n / 2
  if k < m then
   Tree.node n (updateT k x t1) t2
  else
   Tree.node n t1 (updateT (k - m) x t2)

def updateRA : Nat → α → RAList α → RAList α
| _, _, [] => []
| k, x, Digit.zero :: xs => Digit.zero :: (updateRA k x xs)
| k, x, (Digit.one t) :: xs =>
  if k < t.size then
    (Digit.one $ updateT k x t) :: xs
  else
    (Digit.one t) :: (updateRA (k- t.size) x xs)

#eval fromRA <| updateRA 2 10 (toRA [1,2,3,4,5])


-- 3.12

def uncurry : (a → b → c) → (a × b) → c
| f, (x, y) => f x y

def updatesRA : RAList α → List (Nat × α) → RAList α
  | r, up => List.foldl (flip (uncurry updateRA)) r up

infix: 60 " // " => updatesRA

#eval fromRA <| (toRA ['a','b','c']) // [(2, 'x'), (0, 'y')]


-- 3.13

def unconsT : RAList a → Option (Tree a × RAList a)
| [] => none
| Digit.one t :: xs =>
  if xs.isEmpty then
   some (t, [])
  else
   some (t, Digit.zero :: xs)
| Digit.zero :: xs =>
  match unconsT xs with
  | none => none
  | some (Tree.leaf _, _) => none
  | some (Tree.node _ t1 t2, ys) => some (t1, Digit.one t2 :: ys)

def unconsRA (xs : RAList a) : Option (a × RAList a) :=
 match unconsT xs with
 | some (Tree.leaf x, ys) => some (x, ys)
 | some (Tree.node _ _ _, _) => none
 | none => none

#eval unconsT <| toRA ([] : List Nat)

#eval do
 let a ← unconsRA <| toRA [1,2,3]
 pure (a.1, fromRA a.2)

#eval (unconsRA <| toRA [1,2,3]) >>= (fun x => pure (x.1, fromRA x.2))

def headRA (xs : RAList a) : Option a :=
  Prod.fst <$> unconsRA xs

def tailRA (xs : RAList a) : Option (RAList a) :=
  Prod.snd <$> unconsRA xs

#eval fromRA <$> (tailRA <| toRA [1,2,3])
#eval headRA <| toRA [1,2,3]

-- 3.14

def fa₀ (n : Nat) : Array Nat :=
  Chapter1.scanl (· * ·) 1 (List.range' 1 n) |>.toArray

/-
def fa₁ (n : Nat) : Array Nat :=
  1 :: (List.range' 1 n).map (fun i => i * (fa₁ (i - 1)).get (i - 1))
-/

#eval fa₀ 10


-- 3.15

/- first we need to agree about accum

ghci> import Data.Array
ghci> listArray (0,5) [0..]
array (0,5) [(0,0),(1,1),(2,2),(3,3),(4,4),(5,5)]
ghci> accum (\ a b -> a + b) (listArray (0,5) [0..10]) [(1,10),(2,10)]
array (0,5) [(0,0),(1,11),(2,12),(3,3),(4,4),(5,5)]
ghci> accum (\ a b -> a + b) (listArray (0,5) [0..10]) [(1,10),(1,30)]
array (0,5) [(0,0),(1,41),(2,2),(3,3),(4,4),(5,5)]
-/

#eval (Fin.mk 3 (by simp) : Fin 4)

def accum : (e → v → e) → Array e → List (Nat × v) → Array e
 | _, a1, List.nil => a1
 | f, a1, (p :: ps) =>
   if h : p.1 < a1.size then
    let i : Fin a1.size := Fin.mk p.1 h
    accum f (a1.set i (f (a1.get i) p.2)) ps
   else
    accum f a1 ps

#eval accum (λ a b => a + b) (List.range 5).toArray [(1,10),(3,10)]

def accumArray
 (f : a → v → a) (e : a) (n : Nat) (is : List (Nat × v)) : Array a :=
 accum f (Array.mkArray n e) is

#eval accumArray (λ a b => a + b) 5 10 [(1,10),(3,10)]

end Chapter3
