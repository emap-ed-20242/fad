-- Problem: https://adventofcode.com/2017/day/4

import Std

namespace AoC2017D4

-- Entrada e processamento
def inp : String := include_str "../../data/AoC2017_day4.txt"

def parseInp (txt : String) : List String :=
  txt.replace "\x0d" "" |>.splitOn "\n" |>.filter (· ≠ "")

def inpTask : List String := parseInp inp

#eval inpTask

-- Parte 1
def isValid1 (ph : String) : Bool :=
  let wrds := ph.splitOn " "
  let rec hasDup (rem : List String) (seen : Std.HashSet String) : Bool :=
    match rem with
    | [] => true
    | w :: rest =>
      if seen.contains w then false
      else hasDup rest (seen.insert w)
  hasDup wrds Std.HashSet.empty

def countValid1 (phrs : List String) : Nat :=
  phrs.foldl (fun acc ph => if isValid1 ph then acc + 1 else acc) 0

#eval countValid1 inpTask --477

-- Parte 2
def sortChars (lst : List Char) : List Char :=
  let rec ins (x : Char) (sorted : List Char) : List Char :=
    match sorted with
    | [] => [x]
    | y :: ys => if x < y then x :: y :: ys else y :: ins x ys
  lst.foldr ins []

def sortStr (s : String) : String :=
  (sortChars s.toList).asString

def isValid2 (ph : String) : Bool :=
  let wrds := ph.splitOn " " |>.map sortStr
  let rec hasDup (rem : List String) (seen : Std.HashSet String) : Bool :=
    match rem with
    | [] => true
    | w :: rest =>
      if seen.contains w then false
      else hasDup rest (seen.insert w)
  hasDup wrds Std.HashSet.empty

def countValid2 (phrs : List String) : Nat :=
  phrs.foldl (fun acc ph => if isValid2 ph then acc + 1 else acc) 0

#eval countValid2 inpTask --167

end AoC2017D4
