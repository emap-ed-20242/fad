--  Definindo input
def input_day5 : String := include_str "day5-2015.txt"

def split_by_new_line (s : String) : List String :=
  s.split (· == '\n')

def input_task := split_by_new_line input_day5

--  Parte 1

-- Verificar se é vogal ('a', 'e', 'i', 'o', 'u')
def is_vowel (c : Char) : Bool :=
  c = 'a' ∨ c = 'e' ∨ c = 'i' ∨ c = 'o' ∨ c = 'u'


def count_vowels (s : List Char) : Nat :=
  s.foldl (λ acc c => if is_vowel c then acc + 1 else acc) 0

def has_double_letter (s : List Char) : Bool :=
  match s with
  | []        => false
  | [_]       => false
  | c1 :: c2 :: rest => if c1 = c2 then true else has_double_letter (c2 :: rest)



def has_forbidden_substrings (s : List Char) : Bool :=
  let forbidden := ['a', 'b'] :: ['c', 'd'] :: ['p', 'q'] :: ['x', 'y'] :: []
  s.zip s.tail |>.any (λ ⟨c1, c2⟩ => forbidden.contains [c1, c2])


def is_nice (s : String) : Bool :=
  let chars := s.toList
  count_vowels chars >= 3 ∧ has_double_letter chars ∧ ¬has_forbidden_substrings chars

def count_nice_strings (ss : List String) : Nat :=
  ss.foldl (λ acc s => if is_nice s then acc + 1 else acc) 0

-- A parte 1 deu certo (:
#eval count_nice_strings input_task
