def Demon := 2.32
def Tuple : List Nat := [100, 50, 20, 10, 5, 2, 1]
def qt : List Nat := [1, 1, 1, 1, 1, 1, 1]



def amount (tuple : List Nat) (qt : List Nat) : Nat :=
  (tuple.zip qt).foldr (λ (x1,x2) acc => x1 * x2 + acc) 0


def X : Nat × Nat := (0, 1)

#eval amount Tuple qt
