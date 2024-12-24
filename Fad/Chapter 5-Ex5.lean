--Vamos começar implementando função auxliares 
--implementação do Quicksort 
partial def qsort : List Nat → List Nat
| []      => []
| (x::xs) => let smaller := qsort (xs.filter (λ y => y <= x))
             let larger  := qsort (xs.filter (λ y => y > x))
             smaller ++ [x] ++ larger

-- Define minimum usando qsort
def minimum (xs : List Nat) : Option Nat :=
  (qsort xs).head?

partial def quickselect₁  (xs : List Nat) (k : Nat) : Option Nat :=
  (qsort xs).get? k

-- Função de partição para quickselect 
def partition (pivot : Nat) (xs : List Nat) : (List Nat × List Nat) :=
  (xs.filter (λ y => y < pivot), xs.filter (λ y => y ≥ pivot))

-- Selecionar k de forma eficiente usando quickselect
partial def quickselect₂ : List Nat → Nat → Option Nat
| [], _        => none
| (x::xs), k   =>
  let (smaller, larger) := partition x xs
  if k < smaller.length then quickselect₂ smaller k
  else if k = smaller.length then some x
  else quickselect₂ larger (k - smaller.length - 1)


-- teste
#eval minimum [3, 1, 4, 1, 5]
#eval quickselect₁ [3, 1, 4, 1, 5] 2
#eval quickselect₂ [3, 1, 4, 1, 5] 2
