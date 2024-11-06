-- Problem: https://adventofcode.com/2015/day/1

-- PART 1:
-- Defining input
def input_task : String := include_str "inputs/input_day1.txt"

def string_to_char_list (s : String) : List Char :=
  s.toList

def eval_floor : List Char → Int
  | [] => 0
  | x :: xs =>
    if x = '(' then
      1 + eval_floor xs
    else if x = ')' then
      -1 + eval_floor xs
    else
      eval_floor xs

#eval eval_floor (string_to_char_list input_task)

-- PART 2:
def find_basement_position : List Char → Int → Int → Option Int
  | [], _, _ => none  -- No basement entry
  | '(' :: xs, floor, pos => find_basement_position xs (floor + 1) (pos + 1)
  | ')' :: xs, floor, pos =>
    let new_floor := floor - 1
    if new_floor = -1 then
      some (pos + 1)  -- Return the 1-based index when reaching the basement
    else
      find_basement_position xs new_floor (pos + 1)
  | _ :: xs, floor, pos => find_basement_position xs floor (pos + 1)

#eval find_basement_position (string_to_char_list input_task) 0 0
