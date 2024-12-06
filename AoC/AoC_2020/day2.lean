/-!
# Problem: https://adventofcode.com/2020/day/2
-/

namespace AoC2020D2

structure PolicyAndPassword where
  low : Nat
  high : Nat
  letter : Char
  password : String
deriving Repr

def raw_data : String := include_str "../../data/AoC2020_day2.txt"

def process_data₁ (s : String) : List (String) :=
  s.replace "\x0d\n" "$" |>.replace "\n" "$" |>.splitOn "$"

def process_data₂ (ls : List String) : List (List String) :=
  List.map (λ x => x.splitOn " ") ls

def process_data₃! (lls : List (List String)) : List PolicyAndPassword :=
  List.map aux_process_data₃ lls
  where aux_process_data₃ (ss : List String) : PolicyAndPassword :=
    let lowhigh  := ss.get! 0 |>.splitOn "-"
    let low      := lowhigh.get! 0 |>.toNat!
    let high     := lowhigh.get! 1 |>.toNat!
    let letter   := ss.get! 1 |>.get! 0
    let password := ss.get! 2
    PolicyAndPassword.mk low high letter password

def count_letters (s : String) (c : Char) : Nat :=
  s.foldl (λ n x => if x = c then n + 1 else n) 0

#eval raw_data
#eval process_data₁ raw_data
#eval process_data₂ <| process_data₁ raw_data
#eval process_data₃! <| process_data₂ <| process_data₁ raw_data

def pps : List PolicyAndPassword := process_data₃! <| process_data₂ <| process_data₁ raw_data

----------------- part one -----------------
def solve₁! (ps: List PolicyAndPassword) : Nat :=
  match ps with
  | [] => 0
  | p::ps' =>
    let n := count_letters p.password p.letter
    if p.low ≤ n ∧ n ≤ p.high then 1 + solve₁! ps'
    else solve₁! ps'

#eval solve₁! pps -- 524 part 1 solution

----------------- part two -----------------

def solve₂! (ps: List PolicyAndPassword) : Nat :=
  match ps with
  | [] => 0
  | p::ps' =>
    let a := p.password.get! ⟨p.low-1⟩
    let b := p.password.get! ⟨p.high-1⟩
    let flag₁ := (a = p.letter)
    let flag₂ := (b = p.letter)
    if (flag₁ ∧ ¬flag₂) ∨ (¬flag₁ ∧ flag₂) then 1 + solve₂! ps'
    else solve₂! ps'

#eval solve₂! pps -- 485 part 2 solution

end AoC2020D2
