/-!
# Problem: https://adventofcode.com/2020/day/3
-/

namespace AoC2020D3

def raw_data : String := include_str "../../data/AoC2020_day3.txt"

def process_data (s : String) : List (String) :=
  s.replace "\x0d\n" "$" |>.replace "\n" "$" |>.splitOn "$"

def grid : List String := process_data raw_data

#eval raw_data
#eval grid

-------------- Part one --------------

def solve₁! (ls : List String) : Nat :=
  dfs! ls 0
  where dfs! (ls : List String) (y : Nat) : Nat :=
    match ls with
    | [] => 0
    | l :: ls' =>
      let c := l.get! ⟨y⟩
      let y' := (y + 3) % l.length
      (if c = '#' then 1 else 0) + dfs! ls' y'

#eval solve₁! grid -- 228 solution part 1

-------------- Part two --------------

def solve₂! (ls : List String) (dx dy : Nat): Nat :=
  dfs! ls 0 0
  where dfs! (ls : List String) (aux y : Nat) : Nat :=
    match ls with
    | [] => 0
    | l :: ls' =>
      match aux with
      | 0 =>
        let c := l.get! ⟨y⟩
        let y' := (y + dy) % l.length
        (if c = '#' then 1 else 0) + dfs! ls' dx y'
      | aux'+1 => dfs! ls' aux' y

#eval solve₂! grid (1-1) 1 -- 84
#eval solve₂! grid (1-1) 3 -- 228 (equivalent to solve₁!)
#eval solve₂! grid (1-1) 5 -- 89
#eval solve₂! grid (1-1) 7 -- 100
#eval solve₂! grid (2-1) 1 -- 40

#eval 84 * 228 * 89 * 100 * 40 -- 6818112000 solution part 2

end AoC2020D3
