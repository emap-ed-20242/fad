import Fad.Chapter1

namespace Chapter1


def inserts_foldr {a : Type} (x : a) (ys : List a) : List (List a) :=
  -- foldr percorre a lista ys da direita para a esquerda aplicando a função step em cada elemento
  ys.foldr
    (fun y yss =>
      -- ys' eh o sufixo de yss.head! removendo o primeiro elemento
      -- yss nunca está vazio pq começa com [[x]]
      let ys' := yss.head!.tail
      -- Inserimos x na posição antes de y (primeira posição)
      -- Depois, mapeamos y :: (adicionamos y na frente) sobre todas as listas em yss
      (x :: y :: ys') :: yss.map (List.cons y))
    -- [[x]] é o valor inicial do acumulador yss, que representa a inserção de x na última posição
    [[x]]


#eval inserts_foldr 1 [2,3,4]
-- Saída:
    ---- [[1, 2, 3, 4], [2, 1, 3, 4], [2, 3, 1, 4], [2, 3, 4, 1]]

end Chapter1
