-- Problem: https://adventofcode.com/2015/day/5

-- Defining input
def input_day5 : String := include_str "inputs/input_day5.txt"

def split_by_new_line (s : String) : List String :=
  s.split (· == '\n')

def input_task := split_by_new_line input_day5

-- Part 1:
def is_vowel (c : Char) : Bool :=
  c ∈ ['a', 'e', 'i', 'o', 'u']


def rule₁ (s : List Char) : Bool :=
  let num_vowels := s.foldl (λ acc c => if is_vowel c then acc + 1 else acc) 0
  num_vowels ≥ 3

def rule₂ : List Char -> Bool
  | []        => false
  | [_]       => false
  | c1 :: c2 :: cs => if c1 = c2 then true else rule₂ (c2 :: cs)

def rule₃ (s : List Char) : Bool :=
  let forbidden := ['a', 'b'] :: ['c', 'd'] :: ['p', 'q'] :: ['x', 'y'] :: []
  ¬(s.zip s.tail |>.any (λ ⟨c1, c2⟩ => forbidden.contains [c1, c2]))


def is_nice (s : String) : Bool :=
  let chars := s.toList
  rule₁ chars ∧ rule₂ chars ∧ rule₃ chars

def count_nice_strings (ss : List String) : Nat :=
  ss.foldl (λ acc s => if is_nice s then acc + 1 else acc) 0


#eval count_nice_strings input_task


-- Part 2:
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

#eval count_nice_strings₂ input_task
