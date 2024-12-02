import Fad.Chapter7

namespace Chapter7

/- # Exercicio 7.4 -/

def interleave {α : Type} : List α → List α → List (List α)
| xs, []            => [xs]
| [], ys            => [ys]
| x :: xs, y :: ys  =>
  let l := interleave xs (y :: ys) |>.map (x :: ·)
  let r := interleave (x :: xs) ys |>.map (y :: ·)
  l ++ r

def cp {α β : Type} (xs : List α) (ys : List β) : List (α × β) :=
 Chapter1.concatMap (λ x ↦ ys.map (λ y ↦ (x, y))) xs

def perms₁ {α : Type} : List α → List (List α)
| []  => [[]]
| [x] => [[x]]
| xs  =>
  let p := xs.splitAt (xs.length / 2)
  let yss := perms p.1
  let zss := perms p.2
  Chapter1.concatMap (Function.uncurry interleave) (cp yss zss)


/- # Exercicio 7.10  -/

def pick₁ : List Nat → Option (Nat × List Nat)
| []       => none
| [x]      => some (x, [])
| x :: xs  =>
  match pick₁ xs with
  | none => none
  | some (y, ys) =>
    if x ≤ y then some (x, xs) else some (y, x :: ys)

-- #eval pick₁ [7]
-- #eval pick₁ [3, 1, 4]
-- #eval pick₁ [10, 20, 2, 5, 7]
