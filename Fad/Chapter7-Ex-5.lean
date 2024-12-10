-- Definição de pick em lean
def pick : List Nat → Option (Nat × List Nat)
| []      => none
| [x]     => some (x, [])
| x :: xs =>
  match pick xs with
  | none => some (x, []) -- Este caso nunca ocorre para listas não vazias
  | some (y, ys) =>
    if x ≤ y then
      some (x, xs)
    else
      some (y, x :: ys)

#eval pick []             -- Saída: none
#eval pick [5]            -- Saída: some (5, [])
#eval pick [3, 1, 4, 2]   -- Saída: some (1, [3, 4, 2])
