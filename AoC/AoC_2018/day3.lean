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

def mark_claim (fabric : Array (Array Nat)) (claim : Claim) : Array (Array Nat) :=
  let update_row (row : Array Nat) (j : Nat) : Array Nat :=
    row.modify j (fun cell => cell + 1)
  let update_fabric (fabric : Array (Array Nat)) (i : Nat) (j : Nat) : Array (Array Nat) :=
    fabric.modify i (fun row => update_row row j)
  let indices :=
    List.range claim.width |>.bind
      (fun w => List.range claim.height |>.map
        (fun h => (claim.left + w, claim.top + h)))
  indices.foldl (fun fabric (i, j) => update_fabric fabric i j) fabric

def mark_all_claims (claims : List Claim) : Array (Array Nat) :=
  claims.foldl mark_claim fabric

def count_overlaps (fabric : Array (Array Nat)) : Nat :=
  fabric.foldl (fun acc row =>
    acc + row.foldl (fun acc cell =>
      if cell > 1 then acc + 1 else acc) 0) 0

def overlap_count : Nat :=
  count_overlaps (mark_all_claims claims)

#eval overlap_count -- 104126

-- PART 2:

def is_intact (fabric : Array (Array Nat)) (claim : Claim) : Bool :=
  let indices := List.range claim.width |>.bind (fun w => List.range claim.height |>.map (fun h => (claim.left + w, claim.top + h)))
  indices.all (fun (i, j) => fabric[i]![j]! == 1)

def find_intact_claim (claims : List Claim) (fabric : Array (Array Nat)) : Option Nat :=
  match claims.find? (fun claim => is_intact fabric claim) with
  | some claim => some claim.id
  | none => none

def intact_claim_id : Option Nat :=
  find_intact_claim claims (mark_all_claims claims)

#eval intact_claim_id.getD 0 -- 695

end AoC2018D3
