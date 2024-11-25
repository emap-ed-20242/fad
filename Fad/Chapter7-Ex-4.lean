-- Intercalar duas listas
def interleave {α : Type} : list α × list α → list (list α)
| (xs, []) => [xs]
| ([], ys) => [ys]
| (x :: xs, y :: ys) :=
    (interleave (xs, y :: ys)).map (λ zs, x :: zs) ++
    (interleave (x :: xs, ys)).map (λ zs, y :: zs)

-- Produto cartesiano de duas listas
def cp {α β : Type} (xs : list α) (ys : list β) : list (α × β) :=
xs.bind (λ x => ys.map (λ y=> (x, y)))

-- Dividir uma lista ao meio
def split_at {α : Type} : ℕ → list α → list α × list α
| 0, xs => ([], xs)
| _n, [] => ([], [])
| n, x :: xs =>
  let (ys, zs) := split_at (n - 1) xs
  in (x :: ys, zs)

-- Calcular permutações
def perms {α : Type} : list α → list (list α)
| [] => [[]]
| [x] => [[x]]
| xs :=
    let n := xs.length / 2,
        (ys, zs) := split_at n xs,
        yss := perms ys,
        zss := perms zs in
    (cp yss zss).bind (λ (yz : list α × list α), interleave yz)

-- Teste
#eval perms [1, 2, 3]
