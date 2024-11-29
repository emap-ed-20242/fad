
import Fad.Chapter7

namespace Chapter7

-- Ex 7.10

def pick₁ : List Nat → Option (Nat × List Nat)
| []       => none
| [x]      => some (x, [])
| x :: xs  =>
  match pick₁ xs with
  | none => none
  | some (y, ys) =>
    if x ≤ y then some (x, xs) else some (y, x :: ys)

#eval pick₁ [7]
#eval pick₁ [3, 1, 4]
#eval pick₁ [10, 20, 2, 5, 7]
