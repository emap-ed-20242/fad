/--Exercise 3.5 Implement dropWhileSL so that
 dropWhile·fromSL = fromSL·dropWhileSL-/

--  tipo indutivo 
inductive SL (α : Type) : Type
| nil : SL α
| cons : α → (Unit → SL α) → SL α

open SL  --

-- Função para verificar se a lista está vazia
def nullSL {α : Type} : SL α → Bool
| SL.nil => true
| (SL.cons _ _) => false

-- Função para pegar o primeiro elemento da lista
def headSL {α : Type} [Inhabited α] : SL α → α
| (SL.cons x _) => x
| SL.nil => panic! "Lista vazia"


-- Função para pegar o restante da lista (tail)
def tailSL {α : Type} [Inhabited (SL α)] : SL α → SL α
| (SL.cons _ xs) => xs ()
| SL.nil => panic! "Lista vazia"


-- Função que representa a lista vazia
def nilSL {α : Type} : SL α := SL.nil

-- Função dropWhileSL
def dropWhileSL {α : Type} (p : α → Bool) : SL α → SL α
| SL.nil => SL.nil
| (SL.cons x xs) =>
  if p x then dropWhileSL p (xs ())
  else SL.cons x xs

-- Lista suspensa simples: 1, 2, 3
def simpleSL : SL Nat :=
  SL.cons 1 (λ _=> SL.cons 2 (λ _=> SL.cons 3 (λ _=> SL.nil)))

-- Predicado para remover números menores que 2
def simplePred (n : Nat) : Bool := n < 2

-- Função para converter SL em lista normal (para exibir o resultado)
def toList {α : Type} : SL α → List α
| SL.nil => []
| (SL.cons x xs) => x :: toList (xs ())

-- Teste final: aplica dropWhileSL e converte para lista
#eval toList (dropWhileSL simplePred simpleSL)  
