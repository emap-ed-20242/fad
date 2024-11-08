-- Problem: https://adventofcode.com/2018/day/1

import Std.Data.HashSet

-- PART 1:

def input_day1 : String := include_str "inputs/input_day1.txt"

def remove_line_feed (s : String) : String :=
  s.replace "\x0d" ""

def split_by_new_line (s : String) : List String :=
  s.split (· == '\n')

def parse_ints (lst : List String) : List Int :=
  lst.filterMap (fun s =>
    if s.startsWith "+" then
      s.drop 1 |>.toInt?
    else
      s.toInt?)

def input_task := parse_ints <| split_by_new_line <| remove_line_feed <| input_day1

#eval input_task

def sum_of_ints (lst : List Int) : Int :=
  lst.foldl (fun acc x => acc + x) 0

#eval sum_of_ints <| input_task -- 497

-- PART 2:

-- depending on the input, the function may not terminate, hence why we can't prove termination
partial def find_first_duplicate_cumulative_sum (lst : List Int) : Int :=
  let rec aux (seen : Std.HashSet Int) (current_sum : Int) (remaining : List Int) (original : List Int) : Int :=
    match remaining with
    | [] => aux seen current_sum original original
    | h :: t =>
      let new_sum := current_sum + h
      if seen.contains new_sum then
        new_sum
      else
        aux (seen.insert new_sum) new_sum t original
  aux (Std.HashSet.empty.insert 0) 0 lst lst

#eval find_first_duplicate_cumulative_sum <| input_task -- 558
