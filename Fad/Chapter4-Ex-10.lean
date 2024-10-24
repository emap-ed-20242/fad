import Fad.Chapter4

namespace Chapter4

namespace Tree1

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
#eval Tree1.mkTree [1,2,3,5]

partial def mkTreeMulti:  List Nat → Tree (List Nat)
| [] => Tree.null -- retorna a que não tem folha
| (x :: xs) =>
  let (us,vs,ws) := partition3 x xs
  Tree.node (mkTreeMulti us) vs (mkTreeMulti ws)
  /-
    retorna a árvore em que um falor pode ser uma lista dos
    valores, em que pode ter um ou mais valores iguais
  -/

#eval Tree1.mkTreeMulti [3,1,1,2,3,5]

end Tree1

end Chapter4
