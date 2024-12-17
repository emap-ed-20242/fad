import Fad.Chapter6
import Fad.Chapter1

/- # Exercicio 7.5 -/
open Chapter6 (minimum)
open Chapter1 (map)

example (x : Nat) (h : x ≠ 0):
  (minimum ∘ map (x.add)) [] ≠ ((x.add) ∘ minimum) [] := by
  simp [minimum, map]
  exact h
