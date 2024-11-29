import Fad
import AoC.AoC_2015.day6

/-
def main : IO Unit :=
  IO.println s!"Hello, Alexandre!"
-/

open AoC2015D6 in

def main : IO Unit :=
  let c  := parseInstructions input
  let c₁ := solve applyAction₁ initGrid₁ c
  let c₂ := solve applyAction₂ initGrid₂ c
  -- IO.println s!"c₁: {count (λ c => cond c 1 0) c₁} c₂: {count id c₂}"
  -- IO.FS.writeFile (System.FilePath.mk "day6-1.pgm") (grid2pgm c₁ (λ c => cond c 1 0))
  IO.FS.writeFile (System.FilePath.mk "day6-2.pgm") (grid2pgm c₂ id)
