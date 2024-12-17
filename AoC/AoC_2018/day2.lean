-- Problem: https://adventofcode.com/2018/day/2

namespace AoC2018D2

def content : String := include_str "../../data/AoC2018_day2.txt"

def input := content.splitOn "\n"

-- PART 1

def count_letters (s : String) : List (Char × Nat) :=
  s.toList.foldl (fun acc c =>
    match acc.find? (·.1 == c) with
    | some (_, n) => acc.map (fun p => if p.1 == c then (c, n + 1) else p)
    | none        => (c, 1) :: acc
  ) []

def has_exactly (n : Nat) (s : String) : Bool :=
  count_letters s |>.any (·.2 == n)

def count_exactly (n : Nat) (ss : List String) : Nat :=
  ss.foldl (fun acc s => if has_exactly n s then acc + 1 else acc) 0

def checksum (ss : List String) : Nat :=
  let twos := count_exactly 2 ss
  let threes := count_exactly 3 ss
  twos * threes

#eval checksum input


-- PART 2

def differ_by_one (s1 s2 : String) : Bool :=
  let diffs := s1.toList.zip s2.toList |>.filter (fun (c1, c2) => c1 != c2)
  diffs.length == 1

def find_differ_by_one (ss: List String) : Option (String × String) :=
  let rec aux : List String → Option (String × String)
    | [] => default
    | h :: t =>
      match t.find? (differ_by_one h) with
      | some s => some (h, s)
      | none => aux t
  aux ss

def boxes := (find_differ_by_one input).getD default

def common_letters (s1 s2 : String) : String :=
  s1.toList.zip s2.toList |>.filter (fun (c₁, c₂) => c₁ = c₂) |>.map  (·.1) |>.asString

#eval common_letters boxes.1 boxes.2

end AoC2018D2
