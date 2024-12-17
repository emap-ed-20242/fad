
/- # Problema https://adventofcode.com/2021/day/1 -/

namespace AoC2021D1

def content : String := include_str "../../data/AoC2021_day1.txt"

def input : List Nat :=
  content.splitOn "\n" |>.filter (· ≠ "") |>.map (·.trim.toNat!)


/- # Part 1

Analisar uma sequência de medições de profundidade do mar.

- O input é uma lista de números inteiros, representando as
  profundidades do mar, coletados em diferentes momentos.

Objetivo: Contar o número de vezes que uma medição de profundidade é
maior que a medição anterior.

-/

def countIncreases : List Nat → Nat
| []  => 0
| [_] => 0
| (x :: y :: xs) => (if y > x then 1 else 0) + countIncreases (y :: xs)

#eval countIncreases input


/- # Part 2

Análise de somas de janelas deslizantes de três medições consecutivas
de profundidade do mar.

- Em vez de comparar as medições individuais, agora deve-se considerar
  janelas de três medições consecutivas.

- Para cada janela, a soma das três medições é calculada.

Objetivo: Contar o número de vezes que a soma de uma janela de três
medições consecutivas é maior que a soma da janela anterior.

-/

def sublists (n: Nat) : List α → List (List α) → List (List α)
 | []     , acc => acc.reverse
 | x :: xs, acc =>
   let slice := List.take n (x :: xs)
   if slice.length < 3 then
     acc.reverse
   else
     sublists n xs (slice :: acc)

-- #eval sublists 3 input []
#eval countIncreases $ sublists 3 input [] |>.map List.sum

end AoC2021D1
