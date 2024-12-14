structure Graph where
  vertices : List Nat
  edges : List (Nat × Nat × Nat)
deriving Repr

structure AdjArray where
  adjacency : Array (List (Nat × Nat))
deriving Repr


def toAdj (g : Graph) : AdjArray :=
  let n := g.vertices.length
  let initArray := Array.mkArray n []
  let adj := g.edges.foldl
    (fun acc (u, v, w) =>
      acc.modify (u - 1) (fun lst => (v, w) :: lst)
    )
    initArray
  { adjacency := adj }


def toGraph (adj : AdjArray) : Graph :=
  let edges := adj.adjacency.toList.enum.foldl
    (fun acc (u, lst) =>
      acc ++ lst.map (fun (v, w) => (u + 1, v, w))
    )
    []
  { vertices := List.range adj.adjacency.size |>.map (· + 1), edges := edges }


def g : Graph :=
  { vertices := [1, 2, 3],
    edges := [(1, 2, 5), (1, 3, 10), (2, 3, 2)] }

#eval toAdj g


def adj := toAdj g

#eval toGraph adj
