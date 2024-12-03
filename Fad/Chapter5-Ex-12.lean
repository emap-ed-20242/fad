import Fad.Chapter5

namespace Chapter5

/-
  compara dois elementos de tipo α usando uma função f que mapeia para
  valores de tipo β. O resultado da comparação tem tipo Ordering.
  A comparação é feita com base na ordem de β (menor, igual ou maior)
-/
def comparing {α β : Type} [LT β] [DecidableRel (· < · : β → β → Prop)] [DecidableEq β] (f : α → β) : α → α → Ordering :=
  λ x y =>
    -- Se 'f x' for menor que 'f y', retorna Ordering.lt (menor).
    if f x < f y then Ordering.lt
    -- Se 'f x' for igual a 'f y', retorna Ordering.eq (igual).
    else if f x = f y then Ordering.eq
    -- Se 'f x' for maior que 'f y', retorna Ordering.gt (maior).
    else Ordering.gt


/-
  implementaãço parcial de quicksort que aceita uma função de comparação.
  Ela ordena uma lista de elementos de tipo α usando uma função lt que
  compara dois elementos retornando um valor booleano
-/
partial def qsortBy {α : Type} (lt : α → α → Bool) : List α → List α
| [] => []
| x :: xs =>
  --usa "partition" pra dividir a lista xs em dois subconjuntos: (p.1) com elementos
  -- menores que "x" e (p.2) com elementos maiores ou iguais
  let p := xs.partition (λ y => lt y x)
  -- chama recursivamente qsortBy nos dois subconjuntos e concatena o resultado
  -- com x no meio (ou seja, a ordem fica: menores, 'x', maiores).
  (qsortBy lt p.1) ++ [x] ++ (qsortBy lt p.2)


/-
  A função sortOn_simple usa a função qsortBy para ordenar uma lista xs de tipo
  α com base nos valores resultantes de aplicar a função f a cada elemento. A
  função f, por sua vez, mapeia elementos de α para β e a ordenação é feita
  com base na relação de ordem de β
-/
def sortOn_simple {α β : Type} [LT β] [DecidableRel (· < · : β → β → Prop)] (f : α → β) (xs : List α) : List α :=
  -- chama qsortBy passando uma função que compara dois elementos x e y com base nos resultados de 'f x' e 'f y'
  qsortBy (λ x y => f x < f y) xs

-- OBS.: sortOn_simple usa qsortBy com uma função de comparação baseada nos valores de f x,
-- e isso pode chamadar f repetidamente


/-
  NEssa versão, evitamos computar 'f x' repetidas vezes. Em vez disso,
  cada elemento x é associado ao valor de 'f x' e ordenamos a lista de
  pares. Após a ordenação, extraímos os elementos originais
-/
def sortOn_better {α β : Type} [LT β] [DecidableRel (· < · : β → β → Prop)] (f : α → β) (xs : List α) : List α :=
  -- mapeia cada elemento x da lista xs para um par (f x, x)
  let pairs := xs.map (λ x => (f x, x))
  -- ordena a lista de pares usando qsortBy comparando os primeiros elementos dos pares
  let sorted_pairs := qsortBy (λ p1 p2 => p1.1 < p2.1) pairs
  --mapeia a lista para retornar apenas os segundos elementos dos pares (i.e. os elementos originais x)
  sorted_pairs.map Prod.snd

-- OBS.: sortOn_better melhora a eficiência pq mapeia a lista original para pares (f x, x),
-- ordenando a lista de pares e depois extraindo os elementos originais

/-
  sortOn_best combina várias transformações em uma única expressão composta:
  mapeia os elementos para pares (f x, x); ordena os pares e depois extrai os
  elementos originais, utdo isso usando a composição de funções (∘)
-/
def sortOn_best {α β : Type} [LT β] [DecidableRel (· < · : β → β → Prop)] (f : α → β) : List α → List α :=
  -- Função composta:
  -- 1. mapeia cada x para (f x, x)
  -- 2. 'qsortBy' para ordenar os pares com base no primeiro elemento (f x)
  -- 3. mapeia os pares ordenados para extrair o segundo elemento (os x originais)
  List.map Prod.snd ∘ qsortBy (λ p1 p2 => p1.1 < p2.1) ∘ List.map (λ x => (f x, x))

-- OBS.: sortOn_best usa composição de função para realizar as mesmas etapas de sortOn_better,
-- mas de forma mais compacta ,clara e funcional...

-- TESTES
def strings := ["apple", "banana", "cherry", "date"]

#eval sortOn_simple String.length strings
-- Saída: ["date", "apple", "banana", "cherry"]

#eval sortOn_better String.length strings
-- Saída: ["date", "apple", "banana", "cherry"]

#eval sortOn_best String.length strings
-- Saída: ["date", "apple", "banana", "cherry"]

end Chapter5
