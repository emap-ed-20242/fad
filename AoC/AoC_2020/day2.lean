/-!
# Problem: https://adventofcode.com/2020/day/2
-/

namespace AoC2020D2

def content : String := include_str "../../data/AoC2020_day2.txt"

def input : List (String) :=
  content.splitOn "\n"

structure Password where
  low    : Nat
  high   : Nat
  letter : Char
  pwd    : String
deriving Repr

def parse (s : String) : Password :=
  let ss := s.splitOn " "
  let lowhigh  := ss.get! 0 |>.splitOn "-"
  let low      := lowhigh.get! 0 |>.toNat!
  let high     := lowhigh.get! 1 |>.toNat!
  let letter   := ss.get! 1 |>.get! 0
  let password := ss.get! 2
  Password.mk low high letter password

def count_letters (s : String) (c : Char) : Nat :=
  s.foldl (λ n x => if x = c then n + 1 else n) 0

-- Part 1

def solve₁ (ps: List Password) : Nat :=
  match ps with
  | [] => 0
  | p::ps' =>
    let n := count_letters p.pwd p.letter
    if p.low ≤ n ∧ n ≤ p.high then 1 + solve₁ ps'
    else solve₁ ps'

-- #eval solve₁ $ input.map parse

-- Part 2

def solve₂ (ps: List Password) : Nat :=
  match ps with
  | [] => 0
  | p::ps' =>
    let a := p.pwd.get! ⟨p.low-1⟩
    let b := p.pwd.get! ⟨p.high-1⟩
    let flag₁ := (a = p.letter)
    let flag₂ := (b = p.letter)
    if (flag₁ ∧ ¬flag₂) ∨ (¬flag₁ ∧ flag₂) then
      1 + solve₂ ps'
    else
      solve₂ ps'

-- #eval solve₂ $ input.map parse

end AoC2020D2
