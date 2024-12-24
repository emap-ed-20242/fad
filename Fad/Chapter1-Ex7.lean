/--The function takeWhile returns the longest initial segment of a list all
 of whose elements satisfy a given test. Moreover, its running time is proportional to
 the length of the result, not the length of the input. Express takeWhile as an instance
 of foldr, thereby demonstrating once again that a foldr need not process the whole
 of its argument before terminating.
--/

-- definimos a função takewhille
def takeWhile {α : Type} (p : α → Bool) : List α → List α :=
  List.foldr (fun x acc => if p x then x :: acc else []) []

--teste
#eval takeWhile (fun x => x < 5) [1, 2, 3, 6, 4, 5]
#eval takeWhile (fun x => (x % 2 == 0)) [2, 4, 3, 1, 7, 3]
