
/- # Problem https://adventofcode.com/2019/day/1 -/

namespace AoC2019D1

def content : String := include_str "../../data/AoC2019_day1.txt"

def input : List Nat :=
 content.splitOn "\n" |>.filter (· ≠ "") |>.map String.toNat!

-- Part 1

def solution₁ : Nat :=
  input.foldr (λ n acc => ((n / 3) - 2) + acc) 0

-- #eval input.map (λ n  => n / 3 - 2) |>.sum


-- Part 2

def fuel₁ (n : Nat) : Nat :=
  let mass := n / 3 - 2
  if mass = 0 then
   0
  else
   mass + fuel₁ mass

def fuel₂ : Nat → Nat → Nat
 | 0    , total => total
 | n + 1, total =>
  let mass := (n + 1) / 3 - 2
  fuel₂ mass (total + mass)

/-
#eval input.foldr (λ n acc => fuel₁ n + acc) 0
#eval input.foldr (λ n acc => fuel₂ n acc) 0
#eval input.foldr (λ n acc => fuel₂ n 0 + acc) 0
-/

end AoC2019D1
