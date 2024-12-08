import Fad.Chapter5

namespace Chapter5

/- 5.10 -
Primeiro analizando as expressoes em lean
-/
def expression₁ {α : Type} (xs : List α) : List α :=
  flip (List.foldl (λ f x => (λ acc => x :: (f acc))) id) [] xs

def expression₂ {α : Type} (xs : List α) : List α :=
  flip (List.foldr (λ x f => (λ acc => (f acc) ++ [x])) id) [] xs

#eval expression₁ [1, 2, 3, 4]

#eval expression₂ [1, 2, 3, 4]

/-
Temos que ambas as expressoes representam o reverse, uma outra forma de
implementar o reverse é
-/

def reverse {α : Type} : List α → List α :=
  List.foldl (λ acc x => x :: acc) []

#eval reverse [1, 2, 3, 4]

end Chapter5
