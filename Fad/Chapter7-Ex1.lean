import Fad.Chapter7


-- Define a function `minimumBy` that takes a comparator and a list, and returns the minimum element.
def minimumBy {α : Type} (cmp : α → α → Ordering) : List α → Option α
| [] => none -- Return `none` for an empty list
| x :: xs =>
  some (List.foldl (λ acc y => if cmp y acc = Ordering.lt then y else acc) x xs)


-- First version of `minWith`
def minWith {α β : Type} (f : α → β) [Ord β] (xs : List α) : Option α :=
  let cmp (x y : α) := compare (f x) (f y)
  minimumBy cmp xs

-- More efficient version of `minWith`
def minWith₂ {α β : Type} (f : α → β) [Ord β] (xs : List α) : Option α :=
  let tuple (x : α) : β × α := (f x, x)
  let cmp (x y : β × α) := compare x.1 y.1
  minimumBy cmp (xs.map tuple) >>= (λ pair => some pair.2)

-- Test, but this NOT works for Float numbers
#eval minWith (λ x : Nat => x * x) [3, 1, 4, 2]
#eval minWith₂ (λ x : Nat => x * x) [3, 1, 4, 2]


-- Define an `Ord` instance for `Float`, then works for floats
instance : Ord Float where
  compare x y :=
    if x < y then Ordering.lt
    else if x == y then Ordering.eq
    else Ordering.gt


#eval minWith (λ x : Float => x * x) [3.1, -1.2, 4.4, -1.1, 5.6]
#eval minWith₂ (λ x : Float => x * x) [3.1, -1.2, 4.4, -1.1, 5.6]
