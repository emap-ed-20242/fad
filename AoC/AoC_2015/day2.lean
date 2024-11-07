-- Problem: https://adventofcode.com/2015/day/2

-- Part 1:
-- Defining input
def input_day2 : String := include_str "inputs/input_day2.txt"

def split_by_new_line (s : String) : List String :=
  s.split (· == '\n')

def input_task := split_by_new_line input_day2

-- Solution of part 1
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


#eval total_paper input_task


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

#eval total_ribbon input_task
