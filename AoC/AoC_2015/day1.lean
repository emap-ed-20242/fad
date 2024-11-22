-- Problem: https://adventofcode.com/2015/day/1


namespace AoC2015D1

def content : String := include_str "../../data/AoC2015_day1.txt"

def input : List Char := content.toList

-- PART 1

def part1 (input : String) : Int :=
  input.foldl (λ acc ch => if ch = '(' then acc + 1 else acc - 1) 0

#eval part1 content


-- PART 2

def find_basement : List Char → Int → Int → Option Int
  | []       , _  , _     => none
  | _        , -1 , pos   => some pos
  | '(' :: xs, floor, pos => find_basement xs (floor + 1) (pos + 1)
  | ')' :: xs, floor, pos => find_basement xs (floor - 1) (pos + 1)
  |   _ :: _, _, _        => none

#eval find_basement input 0 0


end AoC2015D1
