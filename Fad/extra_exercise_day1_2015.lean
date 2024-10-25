def final_floor (instructions : String) : Int :=
  instructions.foldl (λ acc ch => if ch = '(' then acc + 1 else acc - 1) 0

def instructions : String := include_str "instructions.txt"

#eval final_floor instructions
