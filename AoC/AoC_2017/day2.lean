-- Problem: https://adventofcode.com/2017/day/2

namespace AoC2017D2

def input_day2 : String := include_str "../../data/AoC2017_day2.txt"

def psSheet (s : String) : List (List Nat) :=
  s.replace "\r" ""
   |>.split (· == '\n')
   |>.map (fun line =>
       line.split (fun c => c == ' ' || c == '\t')
       |>.filterMap String.toNat?
   )

def SheetData : List (List Nat) := psSheet input_day2

-- Parte 1
def rwDiff (rw : List Nat) : Nat :=
  match rw with
  | [] => 0
  | x :: xs =>
    let maxVal := List.foldl max x xs
    let minVal := List.foldl min x xs
    maxVal - minVal

def cksum (sheet : List (List Nat)) : Nat :=
  sheet.foldl (fun acc rw => acc + rwDiff rw) 0

#eval cksum SheetData

-- Parte 2
def GenPairs (rw : List Nat) : List (Nat × Nat) :=
  rw.foldl (fun acc x =>
    acc ++ (rw.filter (fun (y : Nat) => y ≠ x)).map (fun (y : Nat) => (x, y))
  ) []

def DivPair (rw : List Nat) : Nat :=
  let pairs := GenPairs rw
  let validPairs := pairs.filter (fun (a, b) => a % b == 0)
  match validPairs.head? with
  | some (a, b) => a / b
  | none => 0

def cksum2 (sheet : List (List Nat)) : Nat :=
  sheet.foldl (fun acc rw => acc + DivPair rw) 0

#eval cksum2 SheetData
