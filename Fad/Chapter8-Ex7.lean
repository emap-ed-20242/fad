/--Exercise 8.7 The function splits::[a] → [([a],[a])] splits a list xs into all pairs
 of lists (ys,zs) such that xs = ys++zs. The function splitsn is similar, except that
 it splits a list into pairs of nonempty lists. Give recursive definitions of splits and
 splitsn.-/

-- Função splits: gera todas as divisões de uma lista em duas sublistas
def splits {α : Type} : List α → List (List α × List α)
| []       => [([], [])]
| x :: xs  => ([], x :: xs) :: (splits xs).map (fun (ys, zs) => (x :: ys, zs))

-- Função splitsn: gera divisões em pares de listas não vazias
def splitsn {α : Type} : List α → List (List α × List α)
| []       => []
| [x]      => []
| x :: xs  => ([x], xs) :: (splitsn xs).map (fun (ys, zs) => (x :: ys, zs))

-- teste 
#eval splits [1, 2, 3]  
#eval splitsn [1, 2, 3]
