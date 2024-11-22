-- Problem: https://adventofcode.com/2015/day/6

namespace AoC2015D6

def input_day6 : String := include_str "../../data/AoC2015_day6.txt"

def split_by_new_line (s : String) : List String :=
  s.split (· == '\n')

def input_task := split_by_new_line input_day6

-- Part 1

def initial_grid : List (List Bool) :=
  List.replicate 1000 (List.replicate 1000 false)

def apply_action (grid : List (List Bool))
                 (action : String)
                 (x1 y1 x2 y2 : Nat) :
                 List (List Bool) :=
  grid.enum.map (λ ⟨i, row⟩ =>
    if x1 ≤ i ∧ i ≤ x2 then
      row.enum.map (λ ⟨j, light⟩ =>
        if y1 ≤ j ∧ j ≤ y2 then
          match action with
          | "turn on"  => true
          | "turn off" => false
          | "toggle"   => ¬ light
          | _          => light
        else light)
    else row)

def count_lights (grid : List (List Bool)) : Nat :=
  grid.foldl (λ acc row =>
    acc + row.foldl (λ acc2 light =>
      acc2 + if light then 1 else 0) 0) 0

def solve (instructions : List (String × Nat × Nat × Nat × Nat)) : Nat :=
  let
    final_grid := instructions.foldl (λ grid instruction =>
      apply_action grid instruction.1
                        instruction.2.1
                        instruction.2.2.1
                        instruction.2.2.2.1
                        instruction.2.2.2.2) initial_grid
  count_lights final_grid

def parse_instruction (instr : String) : (String × Nat × Nat × Nat × Nat) :=
  let parts := instr.splitOn " "
  match parts with
  | ["turn", "on", x1, ",", y1, "through", x2, ",", y2] =>
      ("turn on", x1.toNat!, y1.toNat!, x2.toNat!, y2.toNat!)
  | ["turn", "off", x1, ",", y1, "through", x2, ",", y2] =>
      ("turn off", x1.toNat!, y1.toNat!, x2.toNat!, y2.toNat!)
  | ["toggle", x1, ",", y1, "through", x2, ",", y2] =>
      ("toggle", x1.toNat!, y1.toNat!, x2.toNat!, y2.toNat!)
  | _ => ("", 0, 0, 0, 0)


def parsed_instructions : List (String × Nat × Nat × Nat × Nat) :=
  (input_task.map (λ s => s.replace "," " , ")).map parse_instruction

#eval solve parsed_instructions

-- Part 2:

def initial_grid₂ : List (List Nat) :=
  List.replicate 1000 (List.replicate 1000 0)

def count_brightness (grid : List (List Nat)) : Nat :=
  grid.foldl (λ acc row => acc + row.foldl (λ acc2 light => acc2 + light) 0) 0

def apply_action₂ (grid : List (List Nat))
                  (action : String)
                  (x1 y1 x2 y2 : Nat) :
                  List (List Nat) :=
  grid.enum.map (λ ⟨i, row⟩ =>
    if x1 ≤ i ∧ i ≤ x2 then
      row.enum.map (λ ⟨j, light⟩ =>
        if y1 ≤ j ∧ j ≤ y2 then
          match action with
          | "turn on"  => light + 1
          | "turn off" => light - 1
          | "toggle"   => light + 2
          | _          => light
        else light)
    else row)

def solve₂ (instructions : List (String × Nat × Nat × Nat × Nat)) : Nat :=
  let
    final_grid := instructions.foldl (λ grid instruction =>
      apply_action₂ grid instruction.1
                         instruction.2.1
                         instruction.2.2.1
                         instruction.2.2.2.1
                         instruction.2.2.2.2) initial_grid₂
  count_brightness final_grid

#eval solve₂ parsed_instructions

end AoC2015D6
