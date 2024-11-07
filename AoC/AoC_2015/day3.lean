-- Problem: https://adventofcode.com/2015/day/3

-- Part 1:
-- Defining input
def input_day3 : String := include_str "inputs/input_day3.txt"

-- Define the type of coordinates (a pair of integers)
def coord := (Int × Int)

-- Provide an instance of BEq for coord to allow comparison
instance : BEq coord :=
  ⟨fun (a b : coord) => a.1 == b.1 && a.2 == b.2⟩

def move (pos : coord) (dir : Char) : coord :=
  match dir with
  | '>' => (pos.1 + 1, pos.2)  -- move east
  | '<' => (pos.1 - 1, pos.2)  -- move west
  | '^' => (pos.1, pos.2 + 1)  -- move north
  | 'v' => (pos.1, pos.2 - 1)  -- move south
  | _   => pos  -- invalid direction, stay in place

def is_visited (pos : coord) (visited : List coord) : Bool :=
  visited.contains pos

-- Add a coordinate to the list if it has not been visited
def visit (pos : coord) (visited : List coord) : List coord :=
  if is_visited pos visited then visited else pos :: visited

-- Compute the number of unique houses visited
def count_unique_houses (directions : String) : Nat :=
  let initialPos : coord := (0, 0)  -- Santa starts at (0, 0)
  let moves := directions.toList.foldl
    (fun (state : coord × List coord) (dir : Char) =>
      let newPos := move state.1 dir  -- move Santa and update position
      (newPos, visit newPos state.2))
    (initialPos, [initialPos])
  moves.2.length  -- return the length of the list of visited houses


#eval count_unique_houses input_day3

-- Part2
-- Compute the number of unique houses visited by Santa and Robo-Santa
def count_unique_houses_with_robot (directions : String) : Nat :=
  let initialPos : coord := (0, 0)  -- both Santa and Robo-Santa start at (0, 0)
  let moves := directions.toList.foldl
    (fun (state : (coord × coord) × List coord × Nat) (dir : Char) =>
      let (santaPos, roboPos) := state.1  -- current positions of Santa and Robo-Santa
      let visited := state.2.1              -- list of visited positions
      let turn := state.2.2                 -- turn number (even for Santa, odd for Robo-Santa)
      let (newPos, newVisited) :=
        if turn % 2 == 0 then  -- Santa's turn
          let newSantaPos := move santaPos dir
          (newSantaPos, visit newSantaPos visited)
        else  -- Robo-Santa's turn
          let newRoboPos := move roboPos dir
          (newRoboPos, visit newRoboPos visited)
      ((if turn % 2 == 0 then newPos else santaPos, if turn % 2 == 1 then newPos else roboPos), newVisited, turn + 1))
    ((initialPos, initialPos), [initialPos], 0)
  moves.2.1.length  -- return the length of the list of visited houses


#eval count_unique_houses_with_robot input_day3
