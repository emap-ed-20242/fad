import Fad.Chapter5
import Fad.Chapter1
import Mathlib.tactic

namespace Chapter5

/-
 # 5.2 : qsort definitions
-/

open S51 in

/-
example (x : Nat) (xs : List Nat) (p := xs.partition (· < x))
 : qsort₀ p.1 ++ [x] ++ qsort₀ p.2 = qsort₀ (x :: xs)
 := by
 rewrite (config := {occs := .pos [3]}) [qsort₀]
 unfold Function.comp
 unfold mkTree
 unfold Tree.flatten
 unfold qsort₀
 unfold Function.comp
 sorry
-/

example (xs : List Nat) : qsort₀ xs = qsort₁ xs := by
  induction xs with
  | nil =>
     unfold qsort₀
     unfold qsort₁
     unfold Function.comp
     unfold mkTree
     unfold Tree.flatten
     rfl
  | cons x xs ih =>
    simp [qsort₀,mkTree]
    simp [Tree.flatten]
    simp [qsort₁]
    sorry


/- # Exercicio 5.8 : see book -/


/- # Exercicio 5.9 -/

namespace S52

example (xs : List Nat) : msort₂ xs = msort₃ xs := by
  induction xs with
  | nil => decide
  | cons x xs ih =>
    simp [msort₂, msort₃]
    sorry

end S52

/-- # Exercise 5.12

    sortBy é uma função de ordenação de listas parametrizada pela função de
    comparação. Precisamos adaptar merge para então basicamente renomear
    S52.msort₃ para sortBy parametrizando pela função de comparação.

    Como em Haskell, `compare` é definida para todo tipo instância de `Ord`.
    A função `compareOn` é equivalente a `comparing` do livro.  -/

def merge₁ (f : a → a → Ordering) : List a → List a → List a
 | [], ys => ys
 | xs, [] => xs
 | (x :: xs), (y :: ys) =>
   if f x y = Ordering.lt then
    x :: merge₁ f xs (y :: ys)
   else
    y :: merge₁ f (x :: xs) ys

open Chapter1 (wrap unwrap single until') in
open S52 in

def sortBy (f : a → a → Ordering) : List a → List a
 | []    => []
 | x::xs =>
   unwrap (until' single (pairWith (merge₁ f)) (List.map wrap (x::xs))) |>.getD []

#eval sortBy (λ a b => compare a b) [2,1,3]
#eval compareOn id 1 2

def sortOn₁ [Ord b] (f : a → b) : List a → List a :=
  sortBy (compareOn f)

def sortOn₂ [Ord b] (f : a → b) (xs : List a) : List a :=
  sortBy (compareOn Prod.fst) ((xs.map f).zip xs) |>.map Prod.snd

def sortOn₃ [Ord b] (f : a → b) : List a → List a :=
  List.map Prod.snd ∘ sortBy (compareOn Prod.fst) ∘ List.map (λ x => (f x, x))

/- para mostrar a vantagem -/
def len := dbg_trace "length"; String.length

#eval sortOn₁ len ["aaa", "a", "aa", "aaaaaa", "aaaa"]
#eval sortOn₂ len ["aaa", "a", "aa", "aaaaaa", "aaaa"]
#eval sortOn₃ len ["aaa", "a", "aa", "aaaaaa", "aaaa"]


/- # Exercicio 5.13 -/

namespace S53

def split [Inhabited a] [LE a] [DecidableRel (α := a) (· ≤ ·)]
 : List a → (a × List a × List a)
 | []      => (default, [], [])
 | x :: xs =>
   let op x acc :=
    if x ≤ acc.1
    then (x, acc.1 :: acc.2.2, acc.2.1)
    else (acc.1, x :: acc.2.2, acc.2.1)
   xs.foldr op (x, [], [])


/-- Nn `split₁` the `where` makes `op` visible from outside.
    In `split`, `let` is defined only in the second equation of
    the pattern match. `let rec` would make `op` also visible.

    If `op` is not visible, in the `split_left_le` we would need
    `lift_lets ; intro op` -/

def split₁ [Inhabited a] [LE a] [DecidableRel (α := a) (· ≤ ·)]
 : List a → (a × List a × List a)
 | []      => (default, [], [])
 | x :: xs =>
   xs.foldr op (x, [], [])
 where op x acc :=
  if x ≤ acc.1
  then (x, acc.1 :: acc.2.2, acc.2.1)
  else (acc.1, x :: acc.2.2, acc.2.1)

#eval split₁ [3,1,2,4,5]

theorem split_left_le [Inhabited a] [LE a] [DecidableRel (α := a) (· ≤ ·)]
 (xs : List a) : (split₁ xs).2.1.length ≤ xs.length := by
  unfold split₁
  split
  . simp
  . rename_i x xs
    induction xs with
    | nil => simp [split]
    | cons y xs ih =>
      unfold List.foldr
      simp [split₁.op]
      split ; simp
      rename_i h2
      sorry

partial def mkHeap [Inhabited a] [LE a] [DecidableRel (α := a) (· ≤ ·)]
 : List a → Tree a
 | []      => Tree.null
 | x :: xs =>
   let p := split (x :: xs)
   Tree.node p.1 (mkHeap p.2.1) (mkHeap p.2.2)


end S53

/- Árvore Balanceada, erro de terminação -/


/- # Exercicio 5.19 -/

def filter : (α → Bool) → List α → List α
  | _, [] => []
  | p, x::xs => if p x then (x :: filter p xs) else (filter p xs)

def remove_empty : List (List α) → List (List α)
  | [] => []
  | []::xs => remove_empty xs
  | x::xs => x :: remove_empty xs

def string_ptn : (String → Char) → List String → List (List String)
  | _, [] => []
  | f, x::xs =>
    let ms := "Aabcdefghijklmnopqrstuvwxyz".toList
    remove_empty (ms.map (fun m => filter (fun y => decide (f y = m)) (x::xs)))

#eval string_ptn (flip String.get ⟨0⟩) ["abc", "def", "ghi", "acb", "dfe", "gih"]

def lists_concat : List (List α) → List α
  | [] => []
  | x::xs => x ++ (lists_concat xs)

def string_rsort : List (String → Char) → List String → List String
  | _, [] => []
  | [], xs => xs
  | f::fs, xs => lists_concat (string_ptn f (string_rsort fs xs))

def string_incresing_order : Nat → List (String → Char)
  | sz => ((List.range sz).map (fun x => flip String.get ⟨x⟩))


#eval string_rsort (string_incresing_order 3) ["abc", "def", "ghi"]
#eval string_rsort (string_incresing_order 4) ["ac", "deyz", "deyx"]


end Chapter5
