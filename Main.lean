import Fad
import AoC.AoC_2015.day6

/-
def main : IO Unit :=
  IO.println s!"Hello, Alexandre!"
-/

open AoC2015D6 in

def main : IO Unit :=
  let c  := parseInstructions input
  let c₁ := countLit (λ c => cond c 1 0) $ solve applyAction₁ initGrid₁ c
  let c₂ := countLit id $ solve applyAction₂ initGrid₂ c
  IO.println s!"c₁: {c₁} c₂: {c₂}"
