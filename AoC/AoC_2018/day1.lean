-- Problem: https://adventofcode.com/2018/day/1

import Std.Data.HashSet

namespace AoC2018D1

-- PART 1:

def content : String := include_str "../../data/AoC2018_day1.txt"

def parse_ints (lst : List String) : List Int :=
  lst.filterMap (fun s =>
    (if s.startsWith "+" then s.drop 1 else s).toInt?)

def input : List Int := parse_ints <| content.splitOn "\n"

#eval input.foldl (fun acc x => acc + x) 0

-- PART 2:

-- depending on the input, the function may not terminate, hence why
-- we cant prove termination

partial def first_duplicate_freq (lst : List Int) : Int :=
  let rec aux (seen : Std.HashSet Int) (acc : Int) (rem : List Int) : Int :=
    match rem with
    | [] => aux seen acc lst
    | h :: ts =>
      let new_sum := acc + h
      if seen.contains new_sum then
        new_sum
      else
        aux (seen.insert new_sum) new_sum ts
  aux (Std.HashSet.empty.insert 0) 0 lst

#eval first_duplicate_freq <| input

end AoC2018D1
