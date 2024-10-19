import Fad.Chapter4

namespace Chapter4
/- 4.2 | Henrique Coelho Beltrão -/

/- Exercise 4.2 Look again at the expression
head ([x | x ← [a + 1 . . m], t <= f x] ++ [x | x ← [m + 1 . . b], t <= f x])
where a < m < b and f (a) < t <= f (b). If nothing else is assumed about f , then we
cannot assert that the first list is empty if f (m) < t. Nevertheless, the definition of
smallest (a, b) returns some value. What is it? -/

/- Written Answer:
smallest (a, b) returns the first x such that f(x) <= t, but f(x+1) > t.
That is, x is the point where the function f(x) crosses the threshold t. -/

-- Function that finds the x described above given a, m, and b; the threshold t; and the function f:
def findThresholdCrossing (a m b : Nat) (t : Nat) (f : Nat → Nat) : Option Nat :=
  let xs₁ := (List.range (m - a)).map (λ i => a + 1 + i) -- [a + 1, ..., m]
  let xs₂ := (List.range (b - m)).map (λ i => m + 1 + i) -- [m + 1, ..., b]
  let filtered₁ := xs₁.filter (λ x => t ≤ f x) -- [x | x ∈ [a+1, ..., m], t ≤ f x]
  let filtered₂ := xs₂.filter (λ x => t ≤ f x) -- [x | x ∈ [m+1, ..., b], t ≤ f x]
  match (filtered₁ ++ filtered₂).head? with -- Concatenate and take the head
  | some x => if f (x + 1) > t then some x else none -- Only check next element
  | none => none

-- Examples:
example : findThresholdCrossing 1 5 10 7 (λ x => x + 1) = some 6 := by rfl
example : findThresholdCrossing 2 4 8 10 (λ x => 2 * x) = some 5 := by rfl
example : findThresholdCrossing 1 3 6 4 (λ x => x * x) = some 2 := by rfl
example : findThresholdCrossing 0 3 5 26 (λ x => x * x) = none := by rfl
example : findThresholdCrossing 5 7 12 37 (λ x => 3 * x + 1) = some 12 := by rfl
example : findThresholdCrossing 1 5 10 8 (λ x => x - 2) = some 10 := by rfl

end Chapter4
