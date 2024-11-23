--Problem: https://adventofcode.com/2017/day/1

import Fad.Chapter3

namespace AoC2017D1

def input : String := include_str "../../data/AoC2017_day1.txt"

-- Parte 1

def chToDig (c : Char) : Nat :=
  if c.val > 57 ∨ c.val < 48 then 0 else c.val.toNat - 48

def aux : Nat → List Nat → Nat → Nat
| _, [], acc =>  acc
| l, (x::xs), acc =>
  if x == l then aux x xs (acc + x) else aux x xs acc

def solve1 (str : String) : Nat :=
  let xs := str.toList.map chToDig
  aux (xs.getLast!) xs 0

#eval solve1 $ input.replace "\n" ""

-- Parte 2

def solve2 (str : String) : Nat :=
  let as := Subtype.mk (str.toList.map chToDig) (by rfl)
  let p := List.splitInTwo as
  List.zip p.1.val p.2.val
  |>.foldl (fun acc (x, y) => if x == y then acc + x else acc) 0
  |> (. * 2)

#eval solve2 $ input.replace "\n" ""


end AoC2017D1
