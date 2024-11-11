-- Problem: https://adventofcode.com/2015/day/5

namespace AoC2015D5

def content : String := include_str "../../data/AoC2015_day5.txt"

def input := content.split (· == '\n')

-- Part 1

def is_vowel (c : Char) : Bool :=
  c ∈ "aeoiu".toList

def rule₁ (s : List Char) : Bool :=
  (s.foldl (λ acc c => if is_vowel c then acc + 1 else acc) 0) ≥ 3

def rule₂ : List Char -> Bool
 | []        => false
 | [_]       => false
 | c1 :: c2 :: cs => if c1 = c2 then true else rule₂ (c2 :: cs)

def rule₃ (s : List Char) : Bool :=
  let f := ["ab", "cd", "pq", "xy"]
  ¬(s.zip s.tail |>.any (λ p => f.contains s!"{p.1}{p.2}"))

def is_nice (s : String) : Bool :=
  let cs := s.toList
  rule₁ cs ∧ rule₂ cs ∧ rule₃ cs

#eval input.foldl (λ acc s => if is_nice s then acc + 1 else acc) 0

-- Part 2

def pairs_of_chairs : List Char -> List (List Char)
  | [] => []
  | [_] => []
  | [c1, c2] => [[c1, c2]]
  | c1 :: c2 :: c3 :: cs => if c1 ≠ c2 ∨ c2 ≠ c3
    then [c1, c2] :: pairs_of_chairs (c2 :: c3 :: cs)
    else pairs_of_chairs (c2 :: c3 :: cs)

def check_replication : List (List Char) -> Bool
  | [] => false
  | x :: xs => if x ∈ xs then true
    else check_replication xs

def rule₄ : List Char -> Bool :=
  λ x => (check_replication (pairs_of_chairs x))

def rule₅ : List Char -> Bool
  | []        => false
  | [_]       => false
  | [_, _]    => false
  | c1 :: c2 :: c3 :: rest => if c1 = c3 then true else rule₅ (c2 :: c3 :: rest)


def is_nice₂ (s : String) : Bool :=
  let chars := s.toList
  rule₄ chars ∧ rule₅ chars

def count_nice_strings₂ (ss : List String) : Nat :=
  ss.foldl (λ acc s => if is_nice₂ s then acc + 1 else acc) 0

#eval count_nice_strings₂ input

end AoC2015D5
