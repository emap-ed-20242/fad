-- Problem: https://adventofcode.com/2018/day/5

namespace AoC2018D5

-- PART 1:

def content : String := include_str "../../data/AoC2018_day5.txt"

def input := content.replace "\n" ""

def reacts (c₁ c₂ : Char) : Bool :=
  c₁.toLower == c₂.toLower && c₁.isLower != c₂.isLower

def fullyReact (p : String) : String :=
  let rec loop (ts : List Char) (rem : List Char) : List Char :=
    match rem with
    | [] => ts.reverse
    | c :: cs =>
      match ts with
      | [] => loop [c] cs
      | a :: as =>
        if reacts a c then loop as cs
        else loop (c :: ts) cs
  (loop [] p.toList).asString

#eval String.length <| fullyReact <| input -- 10766


-- PART 2:

def removeUnit (p : String) (unit : Char) : String :=
  (p.toList.filter (fun c => c.toLower != unit.toLower)).asString

def shortestP (p : String) : Nat :=
  let units := "abcdefghijklmnopqrstuvwxyz".toList
  let lengths := units.map (fun unit => String.length <| fullyReact <| removeUnit p unit)
  lengths.foldl Nat.min (String.length p)

#eval shortestP <| input -- 6538

end AoC2018D5
