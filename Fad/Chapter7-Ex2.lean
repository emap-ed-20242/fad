/- # Exercicio 7.2 -/

def minsWith {α β : Type} [Ord β] (f : α → β) (xs : List α) : List α :=
  let step (x : α) (ys : List α) : List α :=
    match ys with
    | [] => [x]
    | y :: ys =>
      match compare (f x) (f y) with
      | Ordering.lt => [x]
      | Ordering.eq => x :: y :: ys
      | Ordering.gt => y :: ys
  List.foldr step [] xs

-- Exemplos

#eval minsWith (fun (p : (Int × Int)) => let (x, y) := p; x*x + y*y) [(1, 2), (3, 4), (1, 1), (-1, -1), (1, -1)] -- [(1, 1), (-1, -1), (1, -1)]

#eval minsWith (fun x => x % 3) (List.range 10) -- [0, 3, 6, 9]

#eval minsWith (fun (s : String) => s.length) ["apple", "banana", "kiwi", "pear"] -- ["kiwi", "pear"]
