/-
# Problem: https://adventofcode.com/2020/day/1
-/

namespace AoC2020D1

def content : String :=
 include_str "../../data/AoC2020_day1.txt"

def process_data (s : String) : List Nat :=
  s.splitOn " " |>.map String.toNat!

def input : List Nat :=
  content.splitOn "\n" |>.filter (· ≠ "")
   |>.map (String.toNat! ∘ String.trim)


-- Part 1

def solve₁ (xs : List Nat) (val: Nat): Option (Nat × Nat) :=
  match xs with
  | [] => none
  | x::xs' =>
    match xs'.find? (λ y => x+y=val) with
    | none => solve₁ xs' val
    | some y => some (x, y)

#eval solve₁ input 2020
#eval 1917 * 103


-- Part 2

def solve₂ (xs : List Nat) (val: Nat)
  : Option (Nat × Nat × Nat) :=
  match xs with
  | [] => none
  | x::xs' =>
    match solve₁ xs' (2020-x) with
    | none => solve₂ xs' val
    | some (y, z) => some (x, y, z)

#eval solve₂ input 2020
#eval 443 * 232 * 1345


end AoC2020D1
