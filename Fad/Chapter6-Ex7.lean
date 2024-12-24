-- Definição da estrutura do Grafo
structure Edge where
  from : Nat
  to : Nat
  weight : Int

structure Graph where
  nodes : List Nat
  edges : List Edge

-- Tipo para matriz de adjacência (AdjArray)
def AdjArray := Array (List (Nat × Int))

-- Converte um grafo para sua representação em matriz de adjacência
def toAdj (g : Graph) : AdjArray :=
  let n := g.nodes.length
  let emptyArray := Array.mkArray n []
  g.edges.foldl
    (fun adj (e : Edge) =>
      adj.modify e.from (fun l => (e.to, e.weight) :: l))
    emptyArray

-- Converte uma matriz de adjacência para um grafo
def toGraph (adj : AdjArray) : Graph :=
  let nodes := List.range adj.size
  let edges := adj.toList.enum.foldl
    (fun es (u, neighbors) =>
      neighbors.foldl
        (fun acc (v, w) => ⟨u, v, w⟩ :: acc)
        es)
    []
  ⟨nodes, edges⟩

-- Exemplo de uso
def exampleGraph : Graph :=
  ⟨[1, 2, 3],
    [⟨1, 2, 5⟩, ⟨1, 3, 10⟩, ⟨2, 3, 2⟩]⟩

def adjArray := toAdj exampleGraph

def graphFromAdj := toGraph adjArray

#eval adjArray       -- Deve mostrar a matriz de adjacência
#eval graphFromAdj   -- Deve retornar o grafo original
