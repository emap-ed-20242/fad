import Fad.Chapter12
import Fad.Chapter1

namespace Chapter12

/- Exercise 12.3 Dê outra definição de `parts` em termos de `foldr`, uma que em cada
etapa faça todas as operações de `cons` antes das operações de `glue`.-/


-- Importa foldr do capitulo 1
open Chapter1 (foldr)

-- Não achei implementações anteriores das funções `cons` e `glue`,
-- então fiz elas baseadas na descrição do livro

def cons {α : Type} (x : α) (p : List (List α)) : List (List α) :=
  /-
      Adiciona o elemento `x` no início de uma lista de listas `p`
      Cria uma nova lista com `x` como o primeiro elemento, e o restante da lista é `p`
  -/
  [x] :: p

def glue {α : Type} (x : α) (p : List (List α)) : List (List α) :=
/-
    Adiciona o elemento `x` a 1a sub lista dentro da lista de listas `p`
    caso base:= Se a lista `p` estiver vazia, ela cria uma nova lista apenas com `[x]`
-/
  match p with
  | [] => [[x]]
  | (s :: ps) => (x :: s) :: ps

/-
    A função `step` deveria aplicar `cons` antes de `glue` pra cada elemento da lista `ps`.
    Tentei definir `step` dentro de `parts`, como está no gabarito do livro, porém encontrei
    um erro que não consegui resolver. Em outras palavras, não consegui definir a função `step`
    de forma que ela fizesse a operação corretamente de DENTRO de `foldr`

    A implementação que mais chega perto do resultado esperado é apresentada a seguir. Porém a
    partição está duplicada. Tentei de várias formas, mas a sokução correta não saiu :(
-/

def step {α : Type} (x : α) (ps : List (List (List α))) : List (List (List α)) :=
  foldr (λ p acc => (cons x p) :: acc) (foldr (λ p acc => (glue x p) :: acc) [] ps) ps

def parts {α : Type} : List α → List (List (List α)) :=
  /-
    `parts` tá usando `foldr` para aplicar a função `step` sobre a lista, com o acumulador inicial `[[]]`
    Ela gera as partições da lista fornecida, mas duplica os resultados
  -/
  foldr step [[]]

-- TESTE
#eval parts [1, 2, 3]

/-
Output:
    [[[1], [2], [3]],
    [[1], [2], [3]],
    [[1], [2, 3]],
    [[1], [2, 3]],
    [[1, 2], [3]],
    [[1, 2], [3]],
    [[1, 2, 3]],
    [[1, 2, 3]]]

    Minha interpretação do que está acontecendo é a seguinte: a duplicação ocorre porque
    a função `foldr` está aplicando as operações `cons` e `glue` separadamente para cada
    sublista em `ps`, isso acaba resultando em duplicação de partições. A causa desse erro
    é o modo como o acumulador é atualizado em `foldr`, onde as listas são concatenadas
    ao acumulador duas vezes para cada sublista. Faz sentido?
-/


end Chapter12
