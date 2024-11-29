import Std.Internal.Parsec

-- Problem: https://adventofcode.com/2015/day/6

namespace AoC2015D6

open Std.Internal.Parsec
open Std.Internal.Parsec.String

def content : String := include_str "../../data/AoC2015_day6.txt"

def input := content.split (· == '\n') |>.filter (· ≠ "")

-- utils

inductive Action where
  | TurnOn
  | TurnOff
  | Toggle
  | Invalid
deriving Repr

structure Command where
 action : Action
 x : Nat × Nat
 y : Nat × Nat
deriving Repr


def Grid (α : Type) : Type := List (List α)

def parseCommand : Parser Command := do
 let a ← pstring "turn on" <|> pstring "turn off" <|> pstring "toggle"
 let _ ← pstring " "
 let x1 ← digits <* pstring ","
 let x2 ← digits <* pstring " through "
 let y1 ← digits <* pstring ","
 let y2 ← digits
 return { action := match a with
                    | "turn on"  => Action.TurnOn
                    | "turn off" => Action.TurnOff
                    | "toggle"   => Action.Toggle
                    | _          => Action.Invalid,
          x := (x1, x2),
          y := (y1, y2) }

-- #eval parseCommand "toggle 223,39 through 454,511".mkIterator

def parseInstructions (is : List String) : List Command :=
  let p := Std.Internal.Parsec.String.Parser.run parseCommand
  let d := { action := Action.Invalid, x := (0, 0), y := (0, 0) }
  is.map
    (λ i => match p i with
            | Except.ok c => c
            | Except.error _ => d)


def applyCommand (grid : Grid α) (cmd : Command) (f : Action → α → α) : Grid α :=
  grid.enum.map (λ ⟨i, row⟩ =>
    if cmd.x.1 ≤ i ∧ i ≤ cmd.y.1 then
      row.enum.map (λ ⟨j, light⟩ =>
        if cmd.x.2 ≤ j ∧ j ≤ cmd.y.2 then
          f cmd.action light
        else light)
    else row)


def count (f : α → Nat) (grid : Grid α) : Nat :=
  grid.foldl (λ acc row =>
    acc + row.foldl (λ acc2 light => acc2 + f light) 0) 0


def grid2pgm (grid : Grid α) (f : α → Nat) : String :=
  let ms := grid.map (λ r => r.map f |>.max? |>.getD 0)
  let mt := ms.max? |>.getD 0
  let header := ["P2", "# test ", "1000 1000", s!"{mt}"]
  let fmt (line : List α) := String.intercalate " " (line.map (toString ∘ (mt - ·) ∘ f))
  let lines := grid.map fmt
  String.intercalate "\n" (header ++ lines) ++ "\n"


def solve (f : Action → α → α) : Grid α  → List Command → Grid α
| g, [] => g
| g, (c::cs) => solve f (applyCommand g c f) cs


-- Part 1

def initGrid₁ : Grid Bool :=
  List.replicate 1000 (List.replicate 1000 false)

def applyAction₁ : Action → Bool → Bool
 | Action.TurnOn , _ => true
 | Action.TurnOff, _ => false
 | Action.Toggle , l => ¬ l
 | _             , l => l

-- #eval count (λ c => cond c 1 0) $ solve applyAction₁ initGrid₁ $ parseInstructions input

-- Part 2

def initGrid₂ : Grid Nat :=
  List.replicate 1000 (List.replicate 1000 0)

def applyAction₂ : Action → Nat → Nat
 | Action.TurnOn , n => n + 1
 | Action.TurnOff, n => n - 1
 | Action.Toggle , n => n + 2
 | _             , n => n

-- #eval count id $ solve applyAction₂ initGrid₂ $ parseInstructions input
-- #eval solve applyAction₂ initGrid₂ [{action := Action.TurnOn, x := (0, 0), y := (0, 0)}]

end AoC2015D6
