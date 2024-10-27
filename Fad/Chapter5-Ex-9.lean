--until::(a → Bool) → (a →a)→a→a
--until p f x = if pxthen x else until p f (f x)

-- Definição de until com recursão
partial def until' (p: a → Bool) (f: a → a) (x : a) : a :=
  if p x then x
  else until' p f (f x)

-- Definição de flatten que une listas
def flatten {α : Type} : list (list α) → list α := list.join

-- Definição de map
def map {α β : Type} (f : α → β) : list α → list β := list.map f

-- Função que verifica se a lista tem um único elemento
def single {α : Type} : list α → bool := λ xs, xs.length = 1

-- Função que combina pares de elementos em uma lista usando f
def pairWith {α : Type} (f : α → α → α) : list α → list α
| (x :: y :: xs) => f x y :: pairWith f xs
| xs := xs

-- Função merge para listas de números (simplificação para exemplo)
def merge (x y : list ℕ) : list ℕ := x ++ y

-- Definição de Leaf
def Leaf {α : Type} : α → list α := λ x=> [x]

-- Definição de wrap (simplificação)
def wrap {α : Type} : list α → list α := id

-- Função unwrap (ajustada para funcionar com o código)
def unwrap {α : Type} : list α → list α := id

-- Função mergesort utilizando until, pairWith, e wrap
def mergesort (xs : list ℕ) : list ℕ :=
unwrap (until single (pairWith merge) (map wrap xs))

