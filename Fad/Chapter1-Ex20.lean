/--Exercise 1.20 Find a definition of op so that
 concat xss = foldl op id xss []-/

import Fad.Chapter1

def op (xs ys : List α) : List α :=
  xs ++ ys

-- `concat` como pedido no exercicio
def concat {α : Type} (xss : List (List α)) : List α :=
  List.foldl op [] xss

#eval concat [[1, 2], [3, 4], [5]]
#eval concat [[], [10, 9], [8], [7, 6]]
