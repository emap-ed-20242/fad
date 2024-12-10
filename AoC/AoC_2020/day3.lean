
-- Problem: https://adventofcode.com/2020/day/3

namespace AoC2020D3

def content : String := include_str "../../data/AoC2020_day3.txt"

def input : List (String) :=
  content.splitOn "\n" |>.map String.trim

-- Part 1

def dfs (ls : List String) (dx dy : Nat) (x : Nat) : Nat :=
    match ls with
    | [] => 0
    | l::ls' =>
      let x' := (x + dx) % l.length
      let rs := ls'.drop (dy - 1)
      cond (l.get ⟨x⟩ = '#') 1 0 + dfs rs dx dy x'
termination_by (ls.length, x)

def solve₁ (ls : List String) : Nat :=
  dfs ls 3 1 0

#eval solve₁ input

-- Part 2

def solve₂ (ls : List String) (dx dy : Nat) : Nat :=
  dfs ls dx dy 0

#eval [(1,1),(3,1),(5,1),(7,1),(1,2)].map
  (λ ⟨dx,dy⟩ => solve₂ input dx dy)

#eval [(1,1),(3,1),(5,1),(7,1),(1,2)].foldl
  (λ acc ⟨dx,dy⟩ => acc * solve₂ input dx dy) 1


end AoC2020D3
