import Fad.Chapter5

namespace Chapter5

/- 5.8 : see book -/

/-! 
# Exercicio 5.19
-/

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
