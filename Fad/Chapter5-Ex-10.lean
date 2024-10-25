import Fad.Chapter5

namespace Chapter5

/- 5.10 : see book -/
-- Expression 1: flip (foldl (λ f x, (x ∘ f)) id) []
-- Define the reverse function using foldl and flip (foldl (flip (:)) [])
def reverse_via_foldl {α : Type} : list α → list α
| [] := []
| xs := foldl (flip (::)) [] xs

-- Define the reverse function using foldr (this works too, but foldl is preferred for reverse)
def reverse_via_foldr {α : Type} : list α → list α
| [] := []
| xs := foldr (λ x acc, acc ++ [x]) [] xs

-- Example to check that both definitions are correct and equivalent to list.reverse
example (xs : list ℕ) : reverse_via_foldl xs = xs.reverse :=
begin
  rw reverse_via_foldl,
  refl, -- reverse_via_foldl is equivalent to reverse
end

example (xs : list ℕ) : reverse_via_foldr xs = xs.reverse :=
begin
  rw reverse_via_foldr,
  refl, -- reverse_via_foldr is equivalent to reverse
end



end Chapter5
