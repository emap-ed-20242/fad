-- Problem: https://adventofcode.com/2020/day/1

namespace AoC2020D1

def raw_data : String := include_str "../../data/AoC2020_day1.txt"

def process_data (s : String) : List Nat :=
  s.replace "\x0d\n" " " |>.replace "\n" " "
  |>.splitOn " " |>.map String.toNat!

def numbers_list : List Nat := process_data raw_data

#eval raw_data
#eval numbers_list

----------------- part one -----------------
def solve₁ (xs : List Nat) (val: Nat): Option (Nat × Nat) :=
  match xs with
  | [] => none
  | x::xs' =>
    match xs'.find? (λ y => x+y=val) with
    | none => solve₁ xs' val
    | some y => some (x, y)

#eval solve₁ numbers_list 2020 -- some(1917, 103)
#eval 1917 * 103 -- 197451 *part 1 solution*

----------------- part two -----------------

def solve₂ (xs : List Nat) (val: Nat): Option (Nat × Nat × Nat) :=
  match xs with
  | [] => none
  | x::xs' =>
    match solve₁ xs' (2020-x) with
    | none => solve₂ xs' val
    | some (y, z) => some (x, y, z)

#eval solve₂ numbers_list 2020 -- some (443, 232, 1345)
#eval 443 * 232 * 1345 -- 138233720 *part 2 solution*

end AoC2020D1
