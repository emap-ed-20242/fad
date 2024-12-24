/--Exercise 1.15 Give a definition of remove for which
 perms3 []=[[]]
 perms3 xs =[x:ys | x ←xs,ys ←perms3 (remove x xs)]
 computes the permutations of a list. Is the first clause necessary? What is the type
 of perms3, and can one generate the permutations of a list of functions with this
 definition?


import Fad.Chapter1

-- Remove a primeira ocorrencia de um elemento numa lista
def remove {α : Type} [DecidableEq α] : α → List α → List α
| _, []       => []
| x, (y :: ys) => if x = y then ys else y :: remove x ys

-- Gera as permutações de elementos de uma lista
partial def perms₃ {α : Type} [DecidableEq α] : List α → List (List α)
| []       => [[]]
| xs       => List.flatMap xs (λ x => List.map (λ ys => x :: ys) (perms₃ (remove x xs)))



#eval perms₃ [1, 2, 3]
