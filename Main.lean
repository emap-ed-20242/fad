import Fad
import AoC

/-
def main : IO Unit :=
  IO.println s!"Hello, Alexandre!"
-/

open AoC2018D6 in

def main : IO Unit := do
  IO.println s!"Part 1: {largest input}"
  IO.println s!"Part 2: {safe_size input 10000}"
