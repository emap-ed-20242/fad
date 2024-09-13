
namespace Chapter3

open List (reverse tail cons)

-- 3.1 Symmetric lists

def snoc {a : Type u} (x : a) (xs : List a) : List a :=
  xs ++ [x]

abbrev SymList (α : Type u) := (List α) × (List α)

#check ([],[])

def nilSL : SymList a := ([], [])

def fromSL (sl : SymList a) : List a :=
 sl.1 ++ sl.2.reverse

def snocSL : a → SymList a → SymList a
| z, ([],    ys) => (ys, [z])
| z, (b::bs, ys) => (b::bs, z :: ys)

def consSL : a → SymList a → SymList a
| z, (xs, []) => ([z], xs)
| z, (xs, ys) => (z :: xs, ys)

def toSL : List a → SymList a
 | [] => nilSL
 | x :: xs => consSL x (toSL xs)

#eval fromSL $ consSL 4 $ consSL 3 $ consSL 2 $ consSL 1 nilSL
#eval toSL (List.iota 20)

def lastSL : SymList a → Option a
| (xs, ys) => if ys.isEmpty then xs.head? else ys.head?

#eval fromSL (snocSL 1 (snocSL 2 (snocSL 3 ([], []))))

def _root_.List.splitAt (xs : List a) (n : Nat) : List a × List a :=
 (xs.take n, xs.drop n)

#eval [1, 2, 3, 4, 5].splitAt 2

def tailSL (sl : SymList a) : Option (SymList a) :=
 let (us, vs) := sl.2.splitAt (sl.2.length / 2)
 match sl with
 | ([],       []) => none
 | ([],  _ :: []) => some nilSL
 | (_ :: [],   _) => some (reverse vs, us)
 | (xs,       ys) => some (tail xs, ys)

#eval tailSL (snocSL 1 (snocSL 2 (snocSL 3 ([], []))))
#eval do let a ← tailSL (snocSL 1 (snocSL 2 (snocSL 3 ([], [])))); pure $ fromSL a

#check pure ∘ fromSL
#eval tailSL (snocSL 1 (snocSL 2 (snocSL 3 ([], [])))) >>= pure ∘ fromSL


/- Evidencias como argumentos
https://lean-lang.org/functional_programming_in_lean/props-proofs-indexing.html#evidence-as-arguments
-/

#check ([] : List Nat)
#eval ([] : List Nat).head?
#eval [1,2].head?

#eval [].head (by simp)
#eval [1,2].head (by simp)

def mytest (n : Nat) := n
#eval mytest 3

def terceiro (xs : List α) (ok : xs.length > 2) : α := xs[2]
#eval terceiro [1, 2, 3, 4] (by simp)


example : cons x ∘ fromSL = fromSL ∘ consSL x := by
  funext xs
  sorry

/- pagina 45 provar a equacao -/
#eval fromSL ([],[1,2,3] ++ [4,5,6])
#eval reverse [4,5,6] ++ reverse [1,2,3]

example (us vs : List Nat)
 : [] ++ reverse (us ++ vs) = reverse vs ++ reverse us := by
 sorry


-- 3.2 Random-access lists

def fetch : Nat → List a → Option a
 | _, [] => none
 | k, x::xs => if k = 0 then x else fetch (k - 1) xs

#eval [1,2,3,4].get? 2
#eval fetch 2 [1,2,3,4]


inductive Tree (α : Type) : Type where
 | leaf (n : α) : Tree α
 | node (n : Nat) (t₁ : Tree α) (t₂ : Tree α) : Tree α
 deriving Repr

open Tree

def Tree.size : Tree a → Nat
 | leaf _ => 1
 | node n _ _ => n

def Tree.mk (t₁ t₂ : Tree a) : Tree a :=
 node (t₁.size + t₂.size) t₁ t₂

#eval mk (mk (leaf 'a') (leaf 'b')) (mk (leaf 'c') (leaf 'd'))

inductive Digit (a : Type) : Type where
 | zero : Digit a
 | one (t : Tree a) : Digit a
 deriving Repr

-- works with def too
abbrev RAList (a : Type) : Type := List (Digit a)

#check ([Digit.zero, Digit.zero] : RAList Nat)

def concat1 {a : Type} : List (List a) → List a :=
 List.foldr List.append []

def concatMap (f : a → List b) : List a → List b :=
 concat1 ∘ (List.map f)

def fromT : Tree a → List a
 | (leaf x) => [x]
 | (node _ t₁ t₂) => fromT t₁ ++ fromT t₂

def fromRA : RAList a → List a :=
  concatMap frm
 where
  frm : Digit a → List a
   | Digit.zero => []
   | Digit.one t => fromT t

open Digit in
#eval fromRA [zero,
        one (mk (leaf 'a') (leaf 'b')),
        one (mk (mk (leaf 'c') (leaf 'd'))
                (mk (leaf 'e') (leaf 'f')))]


end Chapter3
