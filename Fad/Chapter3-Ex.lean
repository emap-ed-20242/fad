import Fad.Chapter3
import Fad.Chapter1

namespace Chapter3
open SL1

/-
| 3.12 | Anderson Gabriel Falcão dos Santos     |
|  3.4 | Breno Russo Guedes de Souza Melo       | not
| 3.10 | Henrique Coelho Beltrão                |
|  3.9 | Jaime Willian Carneiro da Silva        |
|  3.3 | Kauan Kevem Sousa Farias               | not
| 3.14 | Leonardo Micheli Belo                  |
|  3.8 | Luís Filipe Novaes de Souza            |
| 3.15 | Nícolas Mateus Spaniol                 |
| 3.11 | Pablo Andrade Carvalho Barros          |
|  3.6 | Thiago Franke Melchiors                | not
| 3.13 | Wellington José Leite da Silva         |
-/

-- 3.1

/-
(['a', 'b', 'c'], ['d'])
(['a'], ['d', 'c', 'b'])
(['a', 'b'], ['d', 'c'])
-/

#eval toSL "abcd".toList
#eval List.foldr consSL nilSL "abcd".toList
#eval List.foldl (flip snocSL) nilSL "abcd".toList
#eval consSL 'a' (snocSL 'd' (List.foldr consSL nilSL "bc".toList))


-- 3.2

def nullSL {α : Type} : SymList α → Bool
| (xs, ys) => xs.isEmpty ∧ ys.isEmpty

def singleSL {α : Type} : SymList α → Prop
| (xs, ys) => (xs.isEmpty ∧ ys.single) ∨ (ys.isEmpty ∧ xs.single)

def lengthSL {α : Type} : SymList α → Nat
| (xs, ys) => xs.length + ys.length


-- 3.3

def headSL? {α : Type} : SymList α → Option α
 | ([],[])  => none    -- why not nilSL?
 | ([], ys) => List.head? ys
 | (xs, _)  => List.head? xs


-- 3.4

def initSL {α : Type} : SymList α → Option (SymList α)
 | (xs, [])  => if xs.isEmpty then none else some nilSL
 | (xs, [_]) =>
   let (us, vs) := xs.splitAt (xs.length / 2)
   some (us, vs.reverse)
 | (xs, _ :: ys)  => some (xs, ys)


-- 3.5

def dropWhileSL (p : α → Bool) (sl : SymList α) : SymList α :=
 let us := sl.1.dropWhile p
 if us.isEmpty then toSL (sl.2.reverse.dropWhile p) else (us, sl.2)

def dropWhileSL' (p : α → Bool) (sl : SymList α) : SymList α :=
 match headSL? sl with
 | none => nilSL
 | some a =>
   if p a then
    match (tailSL sl) with
    | none => nilSL
    | some us => dropWhileSL p us
   else sl

#eval [1,2,3,4].dropWhile (· < 3)
#eval dropWhileSL (· < 3) (toSL [1,2,3,4]) |> fromSL

-- 3.6

def initsSL {a : Type} (xs : SymList a) : SymList (SymList a) :=
 if nullSL xs then
  snocSL xs nilSL
 else
  match (initSL xs) with
  | none => nilSL
  | some i => snocSL xs (initsSL i)


-- 3.7

def inits {α : Type} (xs : List α) : List (List α) :=
 ((List.map List.reverse) ∘ (Chapter1.scanl (flip List.cons) [])) xs

#eval inits [1,2,3,4]


-- 3.8



-- 3.14

def fa₀ (n : Nat) : Array Nat :=
  Chapter1.scanl (· * ·) 1 (List.range' 1 n) |>.toArray

/-
def fa₁ (n : Nat) : Array Nat :=
  1 :: (List.range' 1 n).map (fun i => i * (fa₁ (i - 1)).get (i - 1))
-/

#eval fa₀ 10

end Chapter3
