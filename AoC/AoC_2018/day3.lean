-- Problem: https://adventofcode.com/2018/day/3

namespace AoC2018D3

-- PART 1:

def content : String := include_str "../../data/AoC2018_day3.txt"

def input := content.split (· == '\n')

structure Claim where
  id : Nat
  left : Nat
  top : Nat
  width : Nat
  height : Nat
  deriving Repr

def parse_claim (s : String) : Option Claim :=
  let parts := s.split (· == ' ')
  if parts.length != 4 then none else
    let id := parts[0]!.drop 1 |>.toNat!
    let left_top := parts[2]!.dropRight 1 |>.split (· == ',')
    let left := left_top[0]!.toNat!
    let top := left_top[1]!.toNat!
    let width_height := parts[3]!.split (· == 'x')
    let width := width_height[0]!.toNat!
    let height := width_height[1]!.toNat!
    some { id, left, top, width, height }

def claims : List Claim :=
  input.filterMap <| parse_claim

#eval claims

def fabric_size : Nat := 1000

def fabric : Array (Array Nat) :=
  mkArray fabric_size (mkArray fabric_size 0)

def mark_claim (f : Array (Array Nat)) (c : Claim) : Array (Array Nat) :=
  let updt_row (row : Array Nat) (j : Nat) : Array Nat :=
    row.modify j (fun cell => cell + 1)
  let updt (f : Array (Array Nat)) (i : Nat) (j : Nat) : Array (Array Nat) :=
    f.modify i (fun row => updt_row row j)
  let idx :=
    List.range c.width |>.bind
      (fun w => List.range c.height |>.map
        (fun h => (c.left + w, c.top + h)))
  idx.foldl (fun f (i, j) => updt f i j) f

def mark_all_claims (cs : List Claim) : Array (Array Nat) :=
  cs.foldl mark_claim fabric

def count_overlaps (f : Array (Array Nat)) : Nat :=
  f.foldl (fun acc row =>
    acc + row.foldl (fun acc cell =>
      if cell > 1 then acc + 1 else acc) 0) 0

#eval count_overlaps <| mark_all_claims claims -- 104126

-- PART 2:

def is_intact (f : Array (Array Nat)) (c : Claim) : Bool :=
  let indices := List.range c.width |>.bind
    (fun w => List.range c.height |>.map
      (fun h => (c.left + w, c.top + h)))
  indices.all (fun (i, j) => f[i]![j]! == 1)

def find_intact_claim (cs : List Claim) (f : Array (Array Nat)) : Option Nat :=
  match cs.find? (fun claim => is_intact f claim) with
  | some claim => some claim.id
  | none => none

#eval (find_intact_claim claims <| mark_all_claims claims).getD 0 -- 695

end AoC2018D3
