-- Problem: https://adventofcode.com/2015/day/2

namespace AoC2015D2

def content : String := include_str "../../data/AoC2015_day2.txt"

def input := content.split (· == '\n')

-- Part 1

def parse_dimensions (s : String) : Option (Int × Int × Int) :=
  match s.splitOn "x" with
  | [l, w, h] => some (l.toInt!, w.toInt!, h.toInt!)
  | _ => none

def paper_for_box (l w h : Int) : Int :=
  let sides := [l*w, w*h, h*l]
  let surface_area := 2 * l * w + 2 * w * h + 2 * h * l
  surface_area + sides.foldl min (l * w)  -- Add the smallest side area

def total_paper (input : List String) : Int :=
  input.foldl (fun acc s =>
    match parse_dimensions s with
    | some (l, w, h) => acc + paper_for_box l w h
    | none => acc) 0


#eval total_paper input


-- Part 2:
-- Calculate the ribbon required for a single box

def ribbon_for_box (l w h : Int) : Int :=
  let perimeters := [2 * (l + w), 2 * (w + h), 2 * (h + l)]
  let volume := l * w * h
  perimeters.foldl min (2 * (l + w)) + volume

-- Process a list of dimension strings to compute total ribbon
def total_ribbon (input : List String) : Int :=
  input.foldl (fun acc s =>
    match parse_dimensions s with
    | some (l, w, h) => acc + ribbon_for_box l w h
    | none => acc) 0

#eval total_ribbon input

end AoC2015D2
