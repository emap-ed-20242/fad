def concat1 {a : Type} : List (List a) → List a :=
  List.foldr List.append []
def concatMap (f : a → List b) : List a → List b :=
  concat1 ∘ (List.map f)

/- 5.17
Suponha que você receba uma lista de n inteiros,
todos eles pertencentes a algum determinado
intervalo (0,m). Mostre como ordenar a lista
em passos Θ(m+n).
-/

-- ms (lista equivalente ao intervalo [0, m])
-- xs (lista de tamanho n a ser ordenada)
-- ys (lista dos pares ordenados (i, times))
-- i (elemento de ms)
-- x (elemento de xs)
-- times (vezes que x aparece em xs)

def accumList : List Nat → List (Nat × Nat) → List (Nat × Nat)
| ms, ys => ms.map (fun i => (i, List.foldr Nat.add 0 <|
 (ys.filter (fun (x,_) => x = i)).map (fun (_,times) => times)))

-- Ordenar lista θ(m+n)
def csort : Nat → List Nat → List Nat
| _, [] => []
| m, xs =>
  -- Contar quantidade de m+1 números: θ(m)
  let ys := accumList (List.range (m+1)) (xs.map (fun x => (x,1)))
  -- Reconstruir lista de tamanho n: θ(n)
  concatMap ((fun (x, times) => (List.replicate times x)) ·) ys

#eval csort 5 [1, 2, 2, 5, 4, 5, 2, 5, 0, 2, 1, 0]



-- RASCUNHO -- RASCUNHO -- RASCUNHO -- RASCUNHO -- RASCUNHO -- RASCUNHO -- RASCUNHO --



-- csort ::Nat → [Int] → [Int]
-- csort m xs = concat [replicate k x | (x, k) ← assocs a]
-- where a = accumArray (+) 0 (0,m)[(x,1) | x ← xs]
-- accumArray ::Ix i ⇒ (e → v → e) → e → (i,i) → [(i, v)] → Array i e

#eval List.replicate 9 12 -- replicate
#eval List.enum [1,5,6,7] -- assocs
#eval List.range 3
#eval Nat.add 2 3

def addifequal₂ : Nat → List (Nat × Nat) → List Nat
  | _, [] => []
  | j, (i, v)::xs =>
    if i == j then v::(addifequal₂ j xs)
    else addifequal₂ j xs

def accumList₂ : List Nat → List (Nat × Nat) → List (Nat × Nat)
| [], _ => []
| j::ms, xs =>
  let addifequal := List.foldr Nat.add 0 <| (xs.filter (fun (i,_) => i = j)).map (fun (_,v) => v)
  (j, addifequal) :: (accumList₂ ms xs)

#eval addifequal₂ 3 [(4,6), (3,5), (3,5),(4,6), (1,8), (3,9)]
#eval accumList [1,2,3,4,5,6] [(4,6), (3,5), (3,5),(4,6), (1,8), (3,9)]
--  array (l,r)[(j,foldl f e [v | (i,v) ← ivs,i == j]) | j ← [l..r]]

#eval csort 5 [0,1,2,3,4,5,5,4,5,1,1,0,1,2,2,2]

#eval concatMap ((fun (a, b) => List.replicate a b) ·) ([1,4,5,6,7].enum)
#eval [1,4,6].map (fun a => (a,1))
