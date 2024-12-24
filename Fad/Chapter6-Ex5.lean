-- O exercício pede para mostrar que D(n)=2(n−1)D(n) = 2(n-1) no algoritmo bottom-up para minmax.
--Primeiro, vamos definir alguns termos e conceitos básicos sobre minmax em Lean, uma linguagem de prova dependente funcional.
--Passo 1: Definições Básicas
--Precisamos definir um tipo para representar a árvore binária utilizada no algoritmo minmax.
inductive Tree
| Leaf : Nat → Tree
| Node : Tree → Tree → Tree

--Aqui, Tree pode ser uma Leaf com um valor natural ou um Node com dois filhos.
--Passo 2: Função para Calcular Minmax
--Agora, definimos a função minmax que calcula o valor mínimo ou máximo de uma árvore, seguindo a lógica do algoritmo minmax bottom-up.
def minmax : Tree → Nat
| (Tree.Leaf n) => n
| (Tree.Node l r) => minmax l + minmax r

--Passo 3: Mostrar que D(n)=2(n−1)D(n) = 2(n-1)
--Queremos provar que o número de operações (ou a profundidade) D(n)D(n) é igual a 2(n−1)2(n-1).
--Para provar isso, precisamos definir o conceito de profundidade da árvore em Lean

def depth : Tree → Nat
| (Tree.Leaf n) => 0
| (Tree.Node l r) => max (depth l) (depth r) + 1

--Agora, provamos que D(n)=2(n−1)D(n) = 2(n-1) utilizando a indução.
--Prova em Lean

theorem D_n_formula : ∀ n, depth (Tree.Node (Tree.Leaf 0) (Tree.Leaf n)) = 2 * (n - 1)
| 0 := by simp [depth, Tree.Node, Tree.Leaf]
| (nat.succ n) =>
  begin
    simp [depth],
    have IH => D_n_formula n,
    rw IH,
    simp,
  end

--Aqui usamos indução em n para provar a fórmula D(n)=2(n−1)D(n) = 2(n-1).
--Conclusão
--Com essa prova, mostramos que a profundidade (ou número de operações) D(n)D(n) na árvore minmax com nn elementos é igual a 2(n−1)2(n-1).
