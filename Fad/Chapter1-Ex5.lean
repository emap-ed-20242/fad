import Fad.Chapter1

-- Com tipo geral α e β
def map {α β : Type} (f : α → β) (xs : List α) : List β :=
  List.foldr (fun x acc => f x :: acc) [] xs

def filter {α : Type} (p : α → Bool) (xs : List α) : List α :=
  List.foldr (fun x acc => if p x then x :: acc else acc) [] xs


-- Tests
#eval map (fun x => x * 2) [1, 2, 3]
#eval filter (fun x => x % 2 == 0) [1, 2, 3, 4]
