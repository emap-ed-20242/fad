-- Problem: https://adventofcode.com/2018/day/2

namespace AoC2018D2
-- PART 1:

def input_day2 : String := include_str "../../data/AoC2018_day2.txt"

def remove_line_feed (s : String) : String :=
  s.replace "\x0d" ""

def split_by_new_line (s : String) : List String :=
  s.split (· == '\n')

def input_task := split_by_new_line <| remove_line_feed <| input_day2

#eval input_task

def count_letters (s : String) : List (Char × Nat) :=
  s.toList.foldl (fun acc c =>
    match acc.find? (·.1 == c) with
    | some (_, n) => acc.map (fun p => if p.1 == c then (c, n + 1) else p)
    | none => (c, 1) :: acc
  ) []

def has_exactly_n (n : Nat) (s : String) : Bool :=
  count_letters s |>.any (·.2 == n)

def count_exactly_n (n : Nat) (ss : List String) : Nat :=
  ss.foldl (fun acc s => if has_exactly_n n s then acc + 1 else acc) 0

def checksum (ss : List String) : Nat :=
  let twos := count_exactly_n 2 ss
  let threes := count_exactly_n 3 ss
  twos * threes

#eval checksum input_task -- 7105

-- PART 2:

def differ_by_one (s1 s2 : String) : Bool :=
  let diffs := s1.toList.zip s2.toList |>.filter (fun (c1, c2) => c1 != c2)
  diffs.length == 1

def find_differ_by_one (ss: List String) : Option (String × String) :=
  let rec aux (ss : List String) : Option (String × String) :=
    match ss with
    | [] => none
    | h :: t =>
      match t.find? (differ_by_one h) with
      | some s => some (h, s)
      | none => aux t
  aux ss

def correct_boxes := (find_differ_by_one <| input_task).getD ("", "")

def common_letters (s1 s2 : String) : String :=
  s1.toList.zip s2.toList |>.filter (fun (c1, c2) => c1 == c2) |>.map (·.1) |>.asString

#eval common_letters correct_boxes.1 correct_boxes.2 -- "omlvgdokxfncvqyersasjziup"

end AoC2018D2
