import Std.Internal.Parsec

/- # Problema https://adventofcode.com/2021/day/2 -/

namespace AoC2021D2

def content : String := include_str "../../data/AoC2021_day2.txt"

structure Command where
  direction : String
  unit : Nat
deriving Repr, Inhabited

def parseCommand (s : String) : Command :=
  match s.trim.splitOn " " with
  | [d, u] =>
    { direction := d, unit := u.toNat! }
  | _ =>
    { direction := "", unit := 0 }

def input : List Command :=
  content.splitOn "\n" |>.filter (· ≠ "") |>.map parseCommand

-- Part 1

def execute₁ (pos : Nat × Nat) : List Command → Nat × Nat
 | [] => pos
 | c :: xs =>
    match c with
    | ⟨"forward", n⟩ => execute₁ (pos.1 + n, pos.2) xs
    | ⟨"down", n⟩    => execute₁ (pos.1, pos.2 + n) xs
    | ⟨"up", n⟩      => execute₁ (pos.1, pos.2 - n) xs
    | ⟨_,_⟩          => execute₁ pos xs

#eval (λ a => a.1 * a.2) $ execute₁ (0,0) input


-- Part 2

def execute₂ (pos : Nat × Nat) (aim : Nat) : List Command → Nat × Nat
 | [] => pos
 | c :: xs =>
    match c with
    | ⟨"forward", n⟩ => execute₂ (pos.1 + n, pos.2 + aim * n) aim xs
    | ⟨"down", n⟩    => execute₂ pos (aim + n) xs
    | ⟨"up", n⟩      => execute₂ pos (aim - n) xs
    | ⟨_,_⟩          => execute₂ pos aim xs

#eval (λ a => a.1 * a.2) $ execute₂ (0,0) 0 input
