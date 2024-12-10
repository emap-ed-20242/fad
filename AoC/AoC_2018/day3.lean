import Std.Internal.Parsec
import Std.Data.HashMap

-- Problem: https://adventofcode.com/2018/day/3

namespace AoC2018D3

open Std.Internal.Parsec
open Std.Internal.Parsec.String

def content : String := include_str "../../data/AoC2018_day3.txt"

def input := content.split (· == '\n') |>.filter (· ≠ "")

structure Claim where
  id     : Nat
  left   : Nat
  top    : Nat
  width  : Nat
  height : Nat
deriving Repr, Inhabited

def parseClaim : Parser Claim := do
 let id ← pstring "#" *> digits
 let _ ← pstring " @ "
 let left   ← digits <* pstring ","
 let top    ← digits <* pstring ": "
 let width  ← digits <* pstring "x"
 let height ← digits
 return { id := id, left := left, top := top, width := width, height := height }

-- #eval parseClaim "#6 @ 703,27: 3x9".mkIterator

def parseClaims (is : List String) : List Claim :=
  let p := Std.Internal.Parsec.String.Parser.run parseClaim
  let help (i : String) : Claim :=
    match p i with
    | Except.ok c => c
    | Except.error _ => default
  is.map help

abbrev Map := Std.HashMap (Nat × Nat) Nat


-- Part 1

def fabric : Map :=
  (List.range 1000).foldl (fun m i =>
    (List.range 1000).foldl (fun m j =>
      m.insert (i, j) 0) m) Std.HashMap.empty

def claims := parseClaims input

def mark_claim (c : Claim) (m : Map) : Map :=
  let idx :=
    List.range c.width |>.flatMap
      (fun w => List.range c.height |>.map
        (fun h => (c.left + w, c.top + h)))
  idx.foldl (fun m p => m.modify p Nat.succ) m

def mark_claims : List Claim → Map → Map
 | []     , m => m
 | c :: cs, m => mark_claims cs (mark_claim c m)

def count_overlaps (m : Map) : Nat :=
  m.fold (fun acc _ v => if v > 1 then acc + 1 else acc) 0

#eval count_overlaps $ mark_claims claims fabric


-- Part 2

def is_intact (m : Map) (c : Claim) : Bool :=
  let indices :=
    List.range c.width |>.flatMap
     (fun w => List.range c.height |>.map
      (fun h => (c.left + w, c.top + h)))
  indices.all (fun p => m[p]! == 1)

def find_intact_claim (cs : List Claim) (m : Map) : Option Nat :=
  match cs.find? (is_intact m ·) with
  | some claim => some claim.id
  | none => none

#eval (find_intact_claim claims <| mark_claims claims fabric).getD 0

end AoC2018D3
