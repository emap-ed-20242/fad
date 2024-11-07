-- Problem: https://adventofcode.com/2015/day/1


namespace AoC2015D1

def content : String := include_str "../../data/AoC2015_day1.txt"

def input : List Char := content.toList

-- PART 1

def eval_floor : List Char → Int
  | [] => 0
  | x :: xs =>
    if x = '(' then
      1 + eval_floor xs
    else if x = ')' then
      -1 + eval_floor xs
    else
      eval_floor xs

#eval eval_floor input

-- PART 2

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

#eval find_basement_position input 0 0

end AoC2015D1
