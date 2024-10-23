import Fad.Chapter4

namespace Chapter4

/- 4.2
Answer: We have smallest (a,b) = x such that f x < t ≤ f (x + 1)

But for t = 1024 and f x = x^2 below f x = t and f (x + 1) > t
-/

#eval D1.smallest (fun x => dbg_trace "fun {x}"; x * x) 1024 (0, 1024)
#eval (fun x => dbg_trace "fun {x}"; x * x) 32
#eval (fun x => dbg_trace "fun {x}"; x * x) 33


/- 4.6 -/

#eval D2.search₁ (λ (x, y) => x ^ 3 + y ^ 3) 1729


/- 4.7 -/

def Tree1.Tree.flatcat : (t : Tree1.Tree a) → (xs: List a) → List a
| null, xs => xs
| (node l x r), xs => l.flatcat (x :: r.flatcat xs)

def Tree1.Tree.flatten₁ (t : Tree1.Tree a) : List a :=
 t.flatcat []

#eval Tree1.mkTree [1,2,3,5] |>.flatten
#eval Tree1.mkTree [1,2,3,5] |>.flatten₁

example (t: Tree1.Tree a) :
  t.flatten = t.flatten₁ := by
  induction t with
  | null => exact rfl
  | node l x r ihl ihr =>
    simp [Tree1.Tree.flatten₁]
    simp [Tree1.Tree.flatten]
    simp [Tree1.Tree.flatcat]
    simp [ihl, ihr]
    simp [Tree1.Tree.flatten₁]
    sorry


/- 4.8
  obs: pode ser necessario mathlib? -/

open Chapter4.Tree1.Tree in

example {α : Type} (t : Chapter4.Tree1.Tree α) :
  t.height ≤ t.size ∧ t.size < 2 ^ t.height := by
 apply And.intro
 {
 induction t with
 | null =>
   simp [height, size]
 | node t₁ x t₂ ihl ihr =>
   simp [height, size]
   sorry
 }
 {
  induction t with
  | null =>
    simp [height,size]
  | node t₁ x t₂ ihl ihr =>
    simp [height, size]
    sorry
 }

/- 4.17 -/

section
open Chapter4.Tree2

abbrev Set (α : Type) : Type := Tree α

def pair  (f : α -> β) (p : α × α) : (β × β) := (f p.1, f p.2)

def split [LE α] [LT α] [DecidableRel (@LT.lt α _)] [DecidableRel (@LE.le α _)]
 (x : α) (t : Set α)
 : Set α × Set α :=
 pair (λ xs => mkTree xs) $ List.partition (· ≤ x) $ Tree.flatten t

#eval split 4 $ mkTree (List.iota 10)

end

end Chapter4
