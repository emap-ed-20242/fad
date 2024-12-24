/--Exercise 1.8 The Data.List library contains a function dropWhileEnd which drops
 the longest suf[]fix of a list all of whose elements satisfy a given Boolean test.  --/

-- Exercise 1.8 Define dropWhileEnd using foldr.

def dropWhileEnd {α : Type} (p : α → Bool) : List α → List α :=
  List.foldr (fun x xs => if p x ∧ xs.isEmpty then [] else x :: xs) []

-- teste 
#eval dropWhileEnd (fun x => x % 2 == 0) [1, 4, 3, 6, 2, 4] 
#eval dropWhileEnd (fun x => x < 5) [2, 3, 6, 4, 5, 6]       
#eval dropWhileEnd (fun x => x < 10) [2, 3, 6, 7, 8]           
