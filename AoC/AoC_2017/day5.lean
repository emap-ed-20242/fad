-- Problem: https://adventofcode.com/2017/day/5

namespace AoC2017D5

def content : String :=
  include_str "../../data/AoC2017_day5.txt"

def input : Array Int :=
  content.splitOn "\n" |>.filter (· ≠ "")
    |>.filterMap String.toInt? |>.toArray


-- Parte 1

partial def proc₁ (arr : Array Int) (i : Int)
   (steps : Nat) (f : Int → Int) : Nat :=
  if i < 0 ∨ i >= arr.size then
    steps
  else
    let off := arr[i.toNat]!
    let new := arr.set! i.toNat <| f off
    proc₁ new (i + off) (steps + 1) f

-- #eval proc₁ input 0 0 (λ x => x + 1)


-- Parte 2

-- #eval proc₁ input 0 0 (λ x => if x ≥ 3 then x - 1 else x + 1)

end AoC2017D5
