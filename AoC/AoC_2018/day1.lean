-- Problem: https://adventofcode.com/2018/day/1

import Std.Data.HashSet

namespace AoC2018D1

-- PART 1

def content : String := include_str "../../data/AoC2018_day1.txt"

def input : List Int := content.splitOn "\n" |>.filterMap
   (λ  s => (if s.startsWith "+" then s.drop 1 else s).toInt?)

#eval input.foldl (fun acc x => acc + x) 0

-- PART 2

partial def first_duplicate_freq (lst : List Int) : Int :=
  let rec aux (seen : Std.HashSet Int) (acc : Int) (rem : List Int) : Int :=
    match rem with
    | [] => aux seen acc lst
    | h :: ts =>
      let new := acc + h
      if seen.contains new then
        new
      else
        aux (seen.insert new) new ts
  aux (Std.HashSet.empty.insert 0) 0 lst

#eval first_duplicate_freq input

end AoC2018D1
