-- Problem: https://adventofcode.com/2018/day/6

namespace AoC2018D6

def content : String := (include_str "../../data/AoC2018_day6.txt")

def to_coord (s : String) : (Nat × Nat) :=
  let parts := s.split (· == ',') |>.map (·.trim.toNat!)
  (parts[0]!, parts[1]!)

def input := content.split (· == '\n') |>.map to_coord


-- Part 1

def manhattan_distance (p1 p2 : Nat × Nat) : Nat :=
  Int.natAbs (p1.1 - p2.1) + Int.natAbs (p1.2 - p2.2)

def bound_box (cs : List (Nat × Nat)) : (Nat × Nat) × (Nat × Nat) :=
  let xs := cs.map (·.1)
  let ys := cs.map (·.2)
  ((xs.min?.getD 0, ys.min?.getD 0), (xs.max?.getD 0, ys.max?.getD 0))

def closest (cs : List (Nat × Nat)) (p : Nat × Nat) : Option (Nat × Nat) :=
  let dists := cs.map (fun c => (c, manhattan_distance c p))
  let min_dist := dists.map (·.2) |>.min?.getD 0
  let closest := dists.filter (·.2 == min_dist)
  if closest.length == 1 then some closest.head!.1 else none

def fin_areas (cs : List (Nat × Nat)) : List (Nat × Nat) :=
  let ((min_x, min_y), (max_x, max_y)) := bound_box cs
  let border := (List.range (max_x - min_x + 1)).flatMap (fun x =>
    [(min_x + x, min_y), (min_x + x, max_y)]) ++
    (List.range (max_y - min_y + 1)).flatMap (fun y =>
    [(min_x, min_y + y), (max_x, min_y + y)])
  let inf_coords := border.map (closest cs) |>.filterMap id |>.eraseDups
  cs.filter (· ∉ inf_coords)

def area (cs : List (Nat × Nat)) (target : Nat × Nat) : Nat :=
  let ((min_x, min_y), (max_x, max_y)) := bound_box cs
  let pts := (List.range (max_x - min_x + 1)).flatMap (fun x =>
    (List.range (max_y - min_y + 1)).map (fun y => (min_x + x, min_y + y)))
  pts.filter (closest cs · == some target) |>.length

def largest (cs : List (Nat × Nat)) : Nat :=
  fin_areas cs |>.map (area cs) |>.max?.getD 0

-- #eval largest input

-- Par 2

def total (cs : List (Nat × Nat)) (p : Nat × Nat) : Nat :=
  cs.foldl (fun acc c => acc + manhattan_distance c p) 0

def safe_size (cs : List (Nat × Nat)) (dist : Nat) : Nat :=
  let ((min_x, min_y), (max_x, max_y)) := bound_box cs
  let pts := (List.range (max_x - min_x + 1)).flatMap (fun x =>
    (List.range (max_y - min_y + 1)).map (fun y => (min_x + x, min_y + y)))
  pts.filter (fun p => total cs p < dist) |>.length

-- #eval safe_size input 10000

end AoC2018D6
