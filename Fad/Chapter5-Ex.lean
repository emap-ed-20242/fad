import Fad.Chapter5
import Fad.Chapter1

namespace Chapter5

/-
 # 5.2 : qsort definitions
-/

open S51 in

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
    simp [qsort₀, qsort₁]
    sorry


/- 5.8 : see book -/


/- # Exercicio 5.9 -/

namespace S52

example (xs : List Nat) : msort₂ xs = msort₃ xs := by
  induction xs with
  | nil => decide
  | cons x xs ih =>
    simp [msort₂, msort₃]
    sorry

end S52

/- # Exercicio 5.13 -/

namespace S53

def split [Inhabited a] [LE a] [DecidableRel (α := a) (· ≤ ·)]
 : List a → (a × List a × List a)
 | x :: xs =>
   let op x acc :=
    if x ≤ acc.1
    then (x, acc.1 :: acc.2.2, acc.2.1)
    else (acc.1, x :: acc.2.2, acc.2.1)
   xs.foldr op (x, [], [])
 | _      => (default, [], [])

#eval split ([1,2,3,4,5] : List Nat)

theorem split_left_le [Inhabited a] [LE a] [DecidableRel (α := a) (· ≤ ·)]
 (xs : List a) : (split xs).2.1.length ≤ xs.length := by
  induction xs with
  | nil => simp [split]
  | cons x xs ih =>
    have h : (split xs).2.1.length ≤ xs.length := ih
    -- rw [split]


def mkHeap [Inhabited a] [LE a] [DecidableRel (α := a) (· ≤ ·)]
 : List a → Tree a
 | []      => Tree.null
 | x :: xs =>
   let p := split (x :: xs)
   Tree.node p.1 (mkHeap p.2.1) (mkHeap p.2.2)
termination_by xs => xs.length

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


def names := ["carlos", "felipe", "mariana", "pedro", "bianca", "gustavo", "camila", "ricardo", "leticia", "renato"]

#eval string_rsort (string_incresing_order 3) ["abc", "def", "ghi", "acb", "dfe", "gih"]
#eval string_rsort (string_incresing_order 4) ["ac", "deyz", "deyx", "def", "g", "za", "z", "acb", "dfe", "gih"]
#eval string_rsort (string_incresing_order 7) names



end Chapter5
