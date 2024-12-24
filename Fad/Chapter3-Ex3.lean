/--Exercise 3.3 Define the functions consSL and headSL.--/
  
import Fad.Chapter3

-- headSL: pega o primeiro elemento, se houver
def headSL {α : Type} : SymList α → Option α
| ([], ys) => ys.head?
| (x :: _, _) => some x

-- Exemplos
def exemplo1 : SymList Nat := ([1, 2, 3], [4, 5, 6])
def exemplo2 : SymList Nat := ([], [7, 8, 9])

#eval headSL exemplo1 
#eval headSL exemplo2  
