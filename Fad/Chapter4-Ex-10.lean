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

#eval Chapter3.Tree.mk (Chapter3.Tree.mk (Chapter3.Tree.leaf 'a') (Chapter3.Tree.leaf 'b')) (Chapter3.Tree.mk (Chapter3.Tree.leaf 'c') (Chapter3.Tree.leaf 'd'))
/-
  Tentei utilizar a estrutura de árvore usada no capítulo 3,
  mas pelo que entendi está estrutura não será suficiente
  para implementar a função
-/

def mktree:  List Nat →  Chapter3.Tree (List Nat)
| [] => Null -- retorna a que não tem folha
| (x :: xs) =>
  let (us,vs,ws) := partition3 x xs
  Node (mktree us) vs (mktree ws)
  /-
    retorna a árvore em que um falor pode ser uma lista dos
    valores, em que pode ter um ou mais valores iguais
  -/


end Chapter4
