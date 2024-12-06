-- Problem: https://adventofcode.com/2017/day/2

namespace AoC2017D2

def inp : String := include_str "../../data/AoC2017_day2.txt"

def parseSheet (txt : String) : List (List Nat) :=
  txt.replace "\r" ""
   |>.split (· == '\n')
   |>.map (fun line =>
       line.split (fun c => c == ' ' || c == '\t')
       |>.filterMap String.toNat?
   )

def sheet : List (List Nat) := parseSheet inp

-- Parte 1
def rowDiff (rw : List Nat) : Nat :=
  match rw with
  | [] => 0
  | x :: xs =>
    let mx := List.foldl max x xs
    let mn := List.foldl min x xs
    mx - mn

def checksum (sheet : List (List Nat)) : Nat :=
  sheet.foldl (fun acc rw => acc + rowDiff rw) 0

#eval checksum sheet

-- Parte 2
def genPairs (rw : List Nat) : List (Nat × Nat) :=
  rw.foldl (fun acc x =>
    acc ++ (rw.filter (fun y => y ≠ x)).map (fun y => (x, y))
  ) []

def divPair (rw : List Nat) : Nat :=
  let pairs := genPairs rw
  let valid := pairs.filter (fun (a, b) => a % b == 0)
  match valid.head? with
  | some (a, b) => a / b
  | none => 0

def checksum2 (sheet : List (List Nat)) : Nat :=
  sheet.foldl (fun acc rw => acc + divPair rw) 0

#eval checksum2 sheet

end AoC2017D2
