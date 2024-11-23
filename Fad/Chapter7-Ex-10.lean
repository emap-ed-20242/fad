-- Ideia : Transformar a função pick que tem custo quadrático em custo linear

/-
picks [] = []
picks (x:xs) = (x, xs) : [(y, x:ys) | (y, ys) <- picks xs]

* Para uma lista vazia ([]), ela retorna uma lista vazia.
* Para uma lista não vazia (x:xs), ela considera o elemento x como a escolha atual, deixando o restante da lista como xs.
 Além disso, recursivamente, aplica o mesmo processo ao restante da lista (xs), tratando cada elemento subsequente
  como a possível escolha atual e reconstruindo a lista restante com o elemento inicial (x) reinserido

picks [3, 1, 4] =
  [(3, [1, 4]), (1, [3, 4]), (4, [3, 1])]

pick xs = minimum (picks xs)

* seleciona o menor elemento de uma lista junto com o restante da lista sem esse elemento

pick [3, 1, 4]
= minimum [(3, [1, 4]), (1, [3, 4]), (4, [3, 1])]
= (1, [3, 4])

O custo quadrático surge porque tanto a geração dos pares quanto a comparação para encontrar o menor elemento dependem do tamanho da lista de maneira acumulativa

A função picks gasta tempo O(n^2) para gerar os pares
A função minimum gasta O(n^2) para processar os pares

-/


/-
Nova função com complexidade linear

Caso base:
Quando a lista contém apenas um elemento [x], a função simplesmente retorna um par com este elemento como o menor (x) e uma lista vazia [] (o resto da lista).

Caso recursivo:
Quando a lista contém mais de um elemento (x : xs), a função realiza os seguintes passos:
Faz uma chamada recursiva para calcular o menor elemento y e a sublista restante ys da lista xs.
Compara x com y:
Se x é menor ou igual a y, então o menor elemento é x e a sublista restante é xs (a lista original menos o x).
Caso contrário, o menor elemento é y e x é adicionado de volta no início de ys para formar a sublista restante.

-/

def pick : List Nat → Option (Nat × List Nat)
| []       => none
| [x]      => some (x, [])
| (x :: xs) =>
  match pick xs with
  | some (y, ys) =>
    if x ≤ y then some (x, xs)
    else some (y, x :: ys)
  | none => none

-- Testes
#eval pick [7]         -- Esperado: `some (7, [])`
#eval pick [3, 1, 4]   -- Esperado: `some (1, [3, 4])`
#eval pick [10, 20, 2, 5, 7] -- Esperado: `some (2, [10, 20, 5, 7])`

-- Mesma função com mensagens de depuração (mais poluída)
def pick2 : List Nat → Option (Nat × List Nat)
| []       =>
  dbg_trace "Lista vazia, retornando none"; none
| [x]      =>
  dbg_trace s!"Lista com um único elemento: {x}, retornando some ({x}, [])"; some (x, [])
| (x :: xs) =>
  dbg_trace s!"Processando: cabeça = {x}, cauda = {xs}";
  match pick2 xs with
  | some (y, ys) =>
    if x ≤ y then
      dbg_trace s!"Escolhido: {x}, resto: {xs}"; some (x, xs)
    else
      dbg_trace s!"Escolhido: {y}, inserindo {x} de volta no resto {ys}"; some (y, x :: ys)
  | none =>
    dbg_trace "Nenhuma escolha possível para lista vazia!"; none


#eval pick2 [10, 20, 2, 5, 7] -- Esperado: `some (2, [10, 20, 5, 7])`

/-

A nova definição de pick tem complexidade O(n) porque:

* A função percorre a lista apenas uma vez.

  Para cada elemento 𝑥 da lista, ela faz uma única comparação com o menor elemento calculado até o momento (y).

* Não há recriação repetitiva de sublistas.

  A sublista restante é construída incrementalmente ao longo da recursão, o que evita operações custosas como a reconstrução de listas em cada iteração (como na versão anterior com picks).

* A recursão desce até o último elemento da lista (O(n)) e depois retorna, realizando uma única comparação por elemento

Portanto, a complexidade total é O(n)
-/
