import Fad.Chapter4
import Fad.Chapter3

namespace Chapter4

/- complete here -/
def partition3 (y : Nat) (xs : List Nat) : (List Nat × List Nat × List Nat) :=
  xs.foldr (λ x (us_vs_ws : List Nat × List Nat × List Nat) =>
    let (us, vs, ws) := us_vs_ws
    if x < y then (x :: us, vs, ws)
    else if x = y then (us, x :: vs, ws)
    else (us, vs, x :: ws))
  ([], [], [])

#eval partition3 3 [3, 1, 4, 1, 5, 9, 2, 6, 5, 3, 5]

/-
def partition3_geral {α : Type} (y : α) (xs : List α) : (List α × List α × List α) :=
  xs.foldr (λ x (us_vs_ws : List α × List α × List α) =>
    let (us, vs, ws) := us_vs_ws
    if x < y then (x :: us, vs, ws)
    else if x = y then (us, x :: vs, ws)
    else (us, vs, x :: ws))
  ([], [], [])

Quando utilizo o geral, não estou conseguindo utilizar "<" ou "="
-/


end Chapter4
