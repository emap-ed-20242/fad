namespace AoC2021D1


-- Data process --
def content : String := include_str "../../data/AoC2021_day1.txt"

def process_data (s : String) : List Nat :=
  s.replace "\x0d\n" " " |>.replace "\n" " "
  |>.splitOn " " |>.map String.toNat!

def convert_to_nat_list : List Nat := process_data content

#eval content
#eval convert_to_nat_list


-- Part 1 --

/-!
Analisar uma sequência de medições de profundidade do mar.

- O input é uma lista de números inteiros, representando as profundidades do mar, coletados em diferentes momentos.

Objetivo:
Contar o número de vezes que uma medição de profundidade é maior que a medição anterior.
-/


def countIncreases : List Nat → Nat
| [] => 0
| [_] => 0
| (x :: y :: xs) => (if y > x then 1 else 0) + countIncreases (y :: xs)
/-!
Da para melhorar e implementar a função de alta ordem foldr ou flodl com a lógica contrária de decaimento.
Mas por hora ta bom o suficiente :)
-/
#eval countIncreases convert_to_nat_list


-- Part 2 --

/-!
Análise de somas de janelas deslizantes de três medições consecutivas de profundidade do mar.

- Em vez de comparar as medições individuais, agora deve-se considerar janelas de três medições consecutivas.
- Para cada janela, a soma das três medições é calculada.

Objetivo:
Contar o número de vezes que a soma de uma janela de três medições consecutivas é maior que a soma da janela anterior.
-/


def sum : List Nat -> Nat
| [] => 0
| (x :: xs) => x + sum xs

def movingWindow (n:Nat) (acc:List Nat) : List Nat -> List Nat
| [] => []
| (x :: xs) => (sum (List.take n (x :: acc))) :: movingWindow n (x :: acc) xs
/-!
Vou criando uma lista com a soma das sublistas de tamanho n (3).
Para isso, crio as janelas deslizantes de 3 elementos consecutivos, somo os valores de cada janela e comparo as somas de janelas consecutivas.

- Funciona para qualquer tamanho de janela que queiramos. Inclusive com janela = 1 resolvendo a anterior também.
-/

def countMovingIncreases3 ( xs: List Nat) : Nat := countIncreases (movingWindow 3 (List.take 2 xs) (List.drop 2 xs))
/-!
- List.take: n xs retorna os primeiros n elementos da lista xs.
-/
#eval countMovingIncreases3 convert_to_nat_list


def countMovingIncreases1 ( xs: List Nat) : Nat := countIncreases (movingWindow 1 (List.reverse $ List.take 2 xs) (List.drop 2 xs)) + 1
#eval countMovingIncreases1 convert_to_nat_list
