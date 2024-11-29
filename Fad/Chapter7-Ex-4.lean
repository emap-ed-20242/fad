-- Intercalar duas listas
def interleave {α : Type} : list α → list α → list (list α)
| [], []            => [[]]  -- Caso base: ambas as listas estão vazias
| xs, []            => [xs]  -- Caso a segunda lista esteja vazia
| [], ys            => [ys]  -- Caso a primeira lista esteja vazia
| x :: xs, y :: ys  =>
    let left := (interleave xs (y :: ys)).map (λ zs => x :: zs)
    let right := (interleave (x :: xs) ys).map (λ zs => y :: zs)
    left ++ right

-- Produto cartesiano de duas listas
def cp {α β : Type} (xs : list α) (ys : list β) : list (list (α × β)) :=
xs.bind (λ x => ys.map (λ y => [(x, y)]))

-- Dividir uma lista ao meio
def split_at {α : Type} : ℕ → list α → list α × list α
| 0, xs => ([], xs)
| _, [] => ([], [])
| n, x :: xs =>
  let (ys, zs) := split_at (n - 1) xs in (x :: ys, zs)

-- Calcular permutações
def perms {α : Type} : list α → list (list α)
| [] => [[]]
| [x] => [[x]]
| xs  =>
    let n := xs.length / 2,
        (ys, zs) := split_at n xs,
        yss := perms ys,
        zss := perms zs in
    (cp yss zss).bind (λ (yz : list α × list α), interleave yz.1 yz.2)

/- Teste
#eval perms [1, 2, 3]
-/
