
namespace Chapter4

def search₀ (f : Nat → Nat) (t : Nat) : List Nat :=
 List.foldl (fun xs x => if t = f x then x :: xs else xs) []
  (List.range <| t + 1)

#eval search₀ (fun x => x) 10


def search (f : Nat → Nat) (t : Nat) : List Nat :=
  seek (0, t)
 where
  acc xs x := if t = f x then x :: xs else xs
  seek (p : Nat × Nat) : List Nat :=
   List.foldl acc [] <| List.range' p.1 (p.2 - p.1 + 1)

#eval search (fun x => x) 10


end Chapter4
