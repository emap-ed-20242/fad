import Fad.Chapter7

namespace Chapter7


/- # Tradução e adaptação do código em Haskell (Cap 7.3) -/


def amount (tuple : List Nat) (qt : List Nat) : Nat :=
  (tuple.zip qt).foldr (λ (x1, x2) acc => x1 * x2 + acc) 0

def count (cs : List Nat) : Nat := cs.sum

-- mkchange retorna o conjunto de moedas com menor quantidade de moedas
-- mktuples cria todas as listas para que mkchange seja feito
def mktuples : List Nat → Nat → List (List Nat)
| [], _        => []
| [1], n       => [[n]]
| (d :: ds), n =>
  (List.range (n / d + 1)).flatMap (fun c =>
    (mktuples ds (n - c * d)).map (fun cs => c :: cs))


def mkchange (ds : List Nat) (n : Nat) : List Nat :=
  minWith count (mktuples ds n)


-- mkchange_greedy é o algoritmo guloso (no livro recebe o nome mkchange)
-- qtd é a função auxiliar e recursiva.
def qtd: List Nat → Nat → List Nat → List Nat
| [], _, cs => cs.reverse
| (d :: ds), n, cs => qtd ds (n % d) ((n / d) :: cs)


def mkchange_greedy (ds : List Nat) (n : Nat) : List Nat :=
  qtd ds n []


/- # Exercício 7.12 -/

def ds := [7, 3, 1]
#eval mkchange ds 54 -- [6, 4, 0]
#eval mkchange_greedy ds 54 -- [7, 1, 2]

/-
  Esta questão pede para explicar porque o mkchange
  retorna [6, 4, 0] em vez de [7, 1, 2]. Ela é
  respondido pelo fato de mkchange retornar a
  primeira lista com mínimo de quantidade de
  moedas(menor soma entre os elementos) e o mktuples
  ordena estes elemenos de ordem crescente dos primeiros
  elemntos de cada uma das listas.

  Para resolver este problema temos que alterar
  a função mktuples e fazer a ordem decrescente
  dos primeiros elementos de cada uma das listas.
  Para isto, basta trocar a função List.range por
  List.Iota como é feito na função mktuples2.
-/

def mktuples2 : List Nat → Nat → List (List Nat)
| [], _        => []
| [1], n       => [[n]]
| (d :: ds), n =>
  ((List.iota (n / d + 1)).map (λ c => c - 1)).flatMap (fun c =>
    (mktuples2 ds (n - c * d)).map (fun cs => c :: cs))


def mkchange2 (ds : List Nat) (n : Nat) : List Nat :=
  minWith count ([n+1]::(mktuples2 ds n))

#eval mkchange2 ds 54 -- [7, 1, 2]


/-
  Atenção:
  Em mkchange2, o elemento [n+1] foi adicionado na
  lista de possíveis conjuntos, pois a função minWith
  apresenta um comportamento estranho. Quando existem
  mais de um mínimo e o primeiro elemento é um deles,
  a função retorna um elemento mínimo diferente do
  elemento da primeira posição da lista.
  Adicionar [n+1] não é a solução ótima, mas é eficiente
  pois contorna o problema sem gerar um novo problema,
  pois sum([n+1])>sum([ ... , n]), quando todas as moedas
  são de valor 1.
-/


#eval minWith count [[5], [4, 1], [6], [1, 4]] -- [4, 1]
#eval minWith count [[5], [7], [4, 1], [1, 4]] -- [4, 1]


end Chapter7
